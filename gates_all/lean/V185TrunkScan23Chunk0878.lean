import V185TrunkScan23Chunk0877

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5196016 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_5196016 : Nat := 118140960795 + 5196016 * 2 ^ 59
def prefixEnd_5196016 : Nat := 4983230072969 + 3 ^ 40 * 5196016 * 2
def baseEnd_5196016 : Nat := 2668053696452247797203963

theorem tailTrace_5196016 : CollatzResearch.WordTrace tailWord_5196016 prefixEnd_5196016 2668053696452247797203963 := by
  unfold tailWord_5196016
  simp only [CollatzResearch.WordTrace]
  refine ⟨94757136371864457863839951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126342848495819277151786601 94757136371864457863839951)
  ·
    refine ⟨142135704557796686795759927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94757136371864457863839951 142135704557796686795759927)
    ·
      refine ⟨213203556836695030193639891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142135704557796686795759927 213203556836695030193639891)
      ·
        refine ⟨319805335255042545290459837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213203556836695030193639891 319805335255042545290459837)
        ·
          refine ⟨119927000720640954483922439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319805335255042545290459837 119927000720640954483922439)
          ·
            refine ⟨179890501080961431725883659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119927000720640954483922439 179890501080961431725883659)
            ·
              refine ⟨269835751621442147588825489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179890501080961431725883659 269835751621442147588825489)
              ·
                refine ⟨202376813716081610691619117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269835751621442147588825489 202376813716081610691619117)
                ·
                  refine ⟨75891305143530604009357169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202376813716081610691619117 75891305143530604009357169)
                  ·
                    refine ⟨56918478857647953007017877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75891305143530604009357169 56918478857647953007017877)
                    ·
                      refine ⟨2668053696452247797203963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56918478857647953007017877 2668053696452247797203963)
                      ·
                        rfl

theorem cell23_5196016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_5196016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196016 prefixEnd_5196016 := by exact prefixLift 5196016
  have htrace : WordTrace (prefixWord ++ tailWord_5196016) baseStart_5196016 baseEnd_5196016 := by
    simpa [prefixWord, tailWord_5196016, baseEnd_5196016] using wordTrace_append hprefix tailTrace_5196016
  have hstable : (prefixWord ++ tailWord_5196016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196016).length < 2 ^ (prefixWord ++ tailWord_5196016).sum := by decide
  have hdescent : baseEnd_5196016 < baseStart_5196016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196034 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5196034 : Nat := 118140960795 + 5196034 * 2 ^ 59
def prefixEnd_5196034 : Nat := 4983230072969 + 3 ^ 40 * 5196034 * 2
def baseEnd_5196034 : Nat := 889354313034676242259627

theorem tailTrace_5196034 : CollatzResearch.WordTrace tailWord_5196034 prefixEnd_5196034 889354313034676242259627 := by
  unfold tailWord_5196034
  simp only [CollatzResearch.WordTrace]
  refine ⟨47378732314415926200458789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126343286171775803201223437 47378732314415926200458789)
  ·
    refine ⟨8883512308952986162586023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47378732314415926200458789 8883512308952986162586023)
    ·
      refine ⟨13325268463429479243879035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8883512308952986162586023 13325268463429479243879035)
      ·
        refine ⟨19987902695144218865818553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325268463429479243879035 19987902695144218865818553)
        ·
          refine ⟨14990927021358164149363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19987902695144218865818553 14990927021358164149363915)
          ·
            refine ⟨22486390532037246224045873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14990927021358164149363915 22486390532037246224045873)
            ·
              refine ⟨16864792899027934668034405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22486390532037246224045873 16864792899027934668034405)
              ·
                refine ⟨3162148668567737750256451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16864792899027934668034405 3162148668567737750256451)
                ·
                  refine ⟨4743223002851606625384677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162148668567737750256451 4743223002851606625384677)
                  ·
                    refine ⟨889354313034676242259627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4743223002851606625384677 889354313034676242259627)
                    ·
                      rfl

theorem cell23_5196034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5196034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196034 prefixEnd_5196034 := by exact prefixLift 5196034
  have htrace : WordTrace (prefixWord ++ tailWord_5196034) baseStart_5196034 baseEnd_5196034 := by
    simpa [prefixWord, tailWord_5196034, baseEnd_5196034] using wordTrace_append hprefix tailTrace_5196034
  have hstable : (prefixWord ++ tailWord_5196034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196034).length < 2 ^ (prefixWord ++ tailWord_5196034).sum := by decide
  have hdescent : baseEnd_5196034 < baseStart_5196034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196084 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5196084 : Nat := 118140960795 + 5196084 * 2 ^ 59
def prefixEnd_5196084 : Nat := 4983230072969 + 3 ^ 40 * 5196084 * 2
def baseEnd_5196084 : Nat := 2668088613136753531153651

theorem tailTrace_5196084 : CollatzResearch.WordTrace tailWord_5196084 prefixEnd_5196084 2668088613136753531153651 := by
  unfold tailWord_5196084
  simp only [CollatzResearch.WordTrace]
  refine ⟨94758376453741281670577653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126344501938321708894103537 94758376453741281670577653)
  ·
    refine ⟨8883597792538245156616655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94758376453741281670577653 8883597792538245156616655)
    ·
      refine ⟨13325396688807367734924983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8883597792538245156616655 13325396688807367734924983)
      ·
        refine ⟨19988095033211051602387475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325396688807367734924983 19988095033211051602387475)
        ·
          refine ⟨29982142549816577403581213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19988095033211051602387475 29982142549816577403581213)
          ·
            refine ⟨11243303456181216526342955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29982142549816577403581213 11243303456181216526342955)
            ·
              refine ⟨16864955184271824789514433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11243303456181216526342955 16864955184271824789514433)
              ·
                refine ⟨12648716388203868592135825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16864955184271824789514433 12648716388203868592135825)
                ·
                  refine ⟨9486537291152901444101869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12648716388203868592135825 9486537291152901444101869)
                  ·
                    refine ⟨3557451484182338041538201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9486537291152901444101869 3557451484182338041538201)
                    ·
                      refine ⟨2668088613136753531153651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557451484182338041538201 2668088613136753531153651)
                      ·
                        rfl

theorem cell23_5196084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5196084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196084 prefixEnd_5196084 := by exact prefixLift 5196084
  have htrace : WordTrace (prefixWord ++ tailWord_5196084) baseStart_5196084 baseEnd_5196084 := by
    simpa [prefixWord, tailWord_5196084, baseEnd_5196084] using wordTrace_append hprefix tailTrace_5196084
  have hstable : (prefixWord ++ tailWord_5196084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196084).length < 2 ^ (prefixWord ++ tailWord_5196084).sum := by decide
  have hdescent : baseEnd_5196084 < baseStart_5196084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196090 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_5196090 : Nat := 118140960795 + 5196090 * 2 ^ 59
def prefixEnd_5196090 : Nat := 4983230072969 + 3 ^ 40 * 5196090 * 2
def baseEnd_5196090 : Nat := 889363898006893502559541

theorem tailTrace_5196090 : CollatzResearch.WordTrace tailWord_5196090 prefixEnd_5196090 889363898006893502559541 := by
  unfold tailWord_5196090
  simp only [CollatzResearch.WordTrace]
  refine ⟨47379242936365206591468431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126344647830307217577249149 47379242936365206591468431)
  ·
    refine ⟨71068864404547809887202647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47379242936365206591468431 71068864404547809887202647)
    ·
      refine ⟨106603296606821714830803971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71068864404547809887202647 106603296606821714830803971)
      ·
        refine ⟨159904944910232572246205957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106603296606821714830803971 159904944910232572246205957)
        ·
          refine ⟨29982177170668607296163617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159904944910232572246205957 29982177170668607296163617)
          ·
            refine ⟨22486632878001455472122713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29982177170668607296163617 22486632878001455472122713)
            ·
              refine ⟨16864974658501091604092035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22486632878001455472122713 16864974658501091604092035)
              ·
                refine ⟨25297461987751637406138053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16864974658501091604092035 25297461987751637406138053)
                ·
                  refine ⟨4743274122703432013650885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25297461987751637406138053 4743274122703432013650885)
                  ·
                    refine ⟨889363898006893502559541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4743274122703432013650885 889363898006893502559541)
                    ·
                      rfl

theorem cell23_5196090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_5196090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196090 prefixEnd_5196090 := by exact prefixLift 5196090
  have htrace : WordTrace (prefixWord ++ tailWord_5196090) baseStart_5196090 baseEnd_5196090 := by
    simpa [prefixWord, tailWord_5196090, baseEnd_5196090] using wordTrace_append hprefix tailTrace_5196090
  have hstable : (prefixWord ++ tailWord_5196090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196090).length < 2 ^ (prefixWord ++ tailWord_5196090).sum := by decide
  have hdescent : baseEnd_5196090 < baseStart_5196090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196103 : List Nat := [1, 1, 4, 1, 2, 2, 4, 8]
def baseStart_5196103 : Nat := 118140960795 + 5196103 * 2 ^ 59
def prefixEnd_5196103 : Nat := 4983230072969 + 3 ^ 40 * 5196103 * 2
def baseEnd_5196103 : Nat := 98818458121081072474669

theorem tailTrace_5196103 : CollatzResearch.WordTrace tailWord_5196103 prefixEnd_5196103 98818458121081072474669 := by
  unfold tailWord_5196103
  simp only [CollatzResearch.WordTrace]
  refine ⟨189517445894413729586096963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126344963929609153057397975 189517445894413729586096963)
  ·
    refine ⟨284276168841620594379145445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189517445894413729586096963 284276168841620594379145445)
    ·
      refine ⟨53301781657803861446089771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284276168841620594379145445 53301781657803861446089771)
      ·
        refine ⟨79952672486705792169134657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53301781657803861446089771 79952672486705792169134657)
        ·
          refine ⟨59964504365029344126850993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79952672486705792169134657 59964504365029344126850993)
          ·
            refine ⟨44973378273772008095138245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59964504365029344126850993 44973378273772008095138245)
            ·
              refine ⟨8432508426332251517838421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44973378273772008095138245 8432508426332251517838421)
              ·
                refine ⟨98818458121081072474669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8432508426332251517838421 98818458121081072474669)
                ·
                  rfl

theorem cell23_5196103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 8].length) (baseStart_5196103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196103 prefixEnd_5196103 := by exact prefixLift 5196103
  have htrace : WordTrace (prefixWord ++ tailWord_5196103) baseStart_5196103 baseEnd_5196103 := by
    simpa [prefixWord, tailWord_5196103, baseEnd_5196103] using wordTrace_append hprefix tailTrace_5196103
  have hstable : (prefixWord ++ tailWord_5196103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196103).length < 2 ^ (prefixWord ++ tailWord_5196103).sum := by decide
  have hdescent : baseEnd_5196103 < baseStart_5196103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196117 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5196117 : Nat := 118140960795 + 5196117 * 2 ^ 59
def prefixEnd_5196117 : Nat := 4983230072969 + 3 ^ 40 * 5196117 * 2
def baseEnd_5196117 : Nat := 2668105557998351902040999

theorem tailTrace_5196117 : CollatzResearch.WordTrace tailWord_5196117 prefixEnd_5196117 2668105557998351902040999 := by
  unfold tailWord_5196117
  simp only [CollatzResearch.WordTrace]
  refine ⟨189517956516363009977106605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126345304344242006651404403 189517956516363009977106605)
  ·
    refine ⟨71069233693636128741414977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189517956516363009977106605 71069233693636128741414977)
    ·
      refine ⟨53301925270227096556061233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71069233693636128741414977 53301925270227096556061233)
      ·
        refine ⟨39976443952670322417045925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53301925270227096556061233 39976443952670322417045925)
        ·
          refine ⟨7495583241125685453196111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39976443952670322417045925 7495583241125685453196111)
          ·
            refine ⟨11243374861688528179794167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495583241125685453196111 11243374861688528179794167)
            ·
              refine ⟨16865062292532792269691251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11243374861688528179794167 16865062292532792269691251)
              ·
                refine ⟨25297593438799188404536877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16865062292532792269691251 25297593438799188404536877)
                ·
                  refine ⟨9486597539549695651701329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25297593438799188404536877 9486597539549695651701329)
                  ·
                    refine ⟨7114948154662271738775997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9486597539549695651701329 7114948154662271738775997)
                    ·
                      refine ⟨2668105557998351902040999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114948154662271738775997 2668105557998351902040999)
                      ·
                        rfl

theorem cell23_5196117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5196117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196117 prefixEnd_5196117 := by exact prefixLift 5196117
  have htrace : WordTrace (prefixWord ++ tailWord_5196117) baseStart_5196117 baseEnd_5196117 := by
    simpa [prefixWord, tailWord_5196117, baseEnd_5196117] using wordTrace_append hprefix tailTrace_5196117
  have hstable : (prefixWord ++ tailWord_5196117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196117).length < 2 ^ (prefixWord ++ tailWord_5196117).sum := by decide
  have hdescent : baseEnd_5196117 < baseStart_5196117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196157 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_5196157 : Nat := 118140960795 + 5196157 * 2 ^ 59
def prefixEnd_5196157 : Nat := 4983230072969 + 3 ^ 40 * 5196157 * 2
def baseEnd_5196157 : Nat := 2668126097224531745540815

theorem tailTrace_5196157 : CollatzResearch.WordTrace tailWord_5196157 prefixEnd_5196157 2668126097224531745540815 := by
  unfold tailWord_5196157
  simp only [CollatzResearch.WordTrace]
  refine ⟨189519415436218096808562725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126346276957478731205708483 189519415436218096808562725)
  ·
    refine ⟨35534890394290893151605511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189519415436218096808562725 35534890394290893151605511)
    ·
      refine ⟨53302335591436339727408267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35534890394290893151605511 53302335591436339727408267)
      ·
        refine ⟨79953503387154509591112401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53302335591436339727408267 79953503387154509591112401)
        ·
          refine ⟨59965127540365882193334301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79953503387154509591112401 59965127540365882193334301)
          ·
            refine ⟨22486922827637205822500363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59965127540365882193334301 22486922827637205822500363)
            ·
              refine ⟨33730384241455808733750545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22486922827637205822500363 33730384241455808733750545)
              ·
                refine ⟨25297788181091856550312909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33730384241455808733750545 25297788181091856550312909)
                ·
                  refine ⟨9486670567909446206367341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25297788181091856550312909 9486670567909446206367341)
                  ·
                    refine ⟨3557501462966042327387753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9486670567909446206367341 3557501462966042327387753)
                    ·
                      refine ⟨2668126097224531745540815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557501462966042327387753 2668126097224531745540815)
                      ·
                        rfl

theorem cell23_5196157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_5196157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196157 prefixEnd_5196157 := by exact prefixLift 5196157
  have htrace : WordTrace (prefixWord ++ tailWord_5196157) baseStart_5196157 baseEnd_5196157 := by
    simpa [prefixWord, tailWord_5196157, baseEnd_5196157] using wordTrace_append hprefix tailTrace_5196157
  have hstable : (prefixWord ++ tailWord_5196157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196157).length < 2 ^ (prefixWord ++ tailWord_5196157).sum := by decide
  have hdescent : baseEnd_5196157 < baseStart_5196157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196174 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5196174 : Nat := 118140960795 + 5196174 * 2 ^ 59
def prefixEnd_5196174 : Nat := 4983230072969 + 3 ^ 40 * 5196174 * 2
def baseEnd_5196174 : Nat := 2668134826395658179028237

theorem tailTrace_5196174 : CollatzResearch.WordTrace tailWord_5196174 prefixEnd_5196174 2668134826395658179028237 := by
  unfold tailWord_5196174
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690004434644563588991447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126346690318104339141287717 23690004434644563588991447)
  ·
    refine ⟨35535006651966845383487171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23690004434644563588991447 35535006651966845383487171)
    ·
      refine ⟨53302509977950268075230757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35535006651966845383487171 53302509977950268075230757)
      ·
        refine ⟨9994220620865675264105767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53302509977950268075230757 9994220620865675264105767)
        ·
          refine ⟨14991330931298512896158651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9994220620865675264105767 14991330931298512896158651)
          ·
            refine ⟨22486996396947769344237977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14991330931298512896158651 22486996396947769344237977)
            ·
              refine ⟨16865247297710827008178483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22486996396947769344237977 16865247297710827008178483)
              ·
                refine ⟨25297870946566240512267725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16865247297710827008178483 25297870946566240512267725)
                ·
                  refine ⟨9486701604962340192100397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25297870946566240512267725 9486701604962340192100397)
                  ·
                    refine ⟨3557513101860877572037649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9486701604962340192100397 3557513101860877572037649)
                    ·
                      refine ⟨2668134826395658179028237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557513101860877572037649 2668134826395658179028237)
                      ·
                        rfl

theorem cell23_5196174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5196174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196174 prefixEnd_5196174 := by exact prefixLift 5196174
  have htrace : WordTrace (prefixWord ++ tailWord_5196174) baseStart_5196174 baseEnd_5196174 := by
    simpa [prefixWord, tailWord_5196174, baseEnd_5196174] using wordTrace_append hprefix tailTrace_5196174
  have hstable : (prefixWord ++ tailWord_5196174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196174).length < 2 ^ (prefixWord ++ tailWord_5196174).sum := by decide
  have hdescent : baseEnd_5196174 < baseStart_5196174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196182 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5196182 : Nat := 118140960795 + 5196182 * 2 ^ 59
def prefixEnd_5196182 : Nat := 4983230072969 + 3 ^ 40 * 5196182 * 2
def baseEnd_5196182 : Nat := 2668138934240894147728201

theorem tailTrace_5196182 : CollatzResearch.WordTrace tailWord_5196182 prefixEnd_5196182 2668138934240894147728201 := by
  unfold tailWord_5196182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845020453820470379888925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126346884840751684052148533 11845020453820470379888925)
  ·
    refine ⟨4441882670182676392458347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11845020453820470379888925 4441882670182676392458347)
    ·
      refine ⟨6662824005274014588687521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4441882670182676392458347 6662824005274014588687521)
      ·
        refine ⟨4997118003955510941515641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6662824005274014588687521 4997118003955510941515641)
        ·
          refine ⟨3747838502966633206136731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4997118003955510941515641 3747838502966633206136731)
          ·
            refine ⟨5621757754449949809205097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747838502966633206136731 5621757754449949809205097)
            ·
              refine ⟨4216318315837462356903823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5621757754449949809205097 4216318315837462356903823)
              ·
                refine ⟨6324477473756193535355735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216318315837462356903823 6324477473756193535355735)
                ·
                  refine ⟨9486716210634290303033603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6324477473756193535355735 9486716210634290303033603)
                  ·
                    refine ⟨14230074315951435454550405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9486716210634290303033603 14230074315951435454550405)
                    ·
                      refine ⟨2668138934240894147728201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14230074315951435454550405 2668138934240894147728201)
                      ·
                        rfl

theorem cell23_5196182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5196182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196182 prefixEnd_5196182 := by exact prefixLift 5196182
  have htrace : WordTrace (prefixWord ++ tailWord_5196182) baseStart_5196182 baseEnd_5196182 := by
    simpa [prefixWord, tailWord_5196182, baseEnd_5196182] using wordTrace_append hprefix tailTrace_5196182
  have hstable : (prefixWord ++ tailWord_5196182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196182).length < 2 ^ (prefixWord ++ tailWord_5196182).sum := by decide
  have hdescent : baseEnd_5196182 < baseStart_5196182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196210 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_5196210 : Nat := 118140960795 + 5196210 * 2 ^ 59
def prefixEnd_5196210 : Nat := 4983230072969 + 3 ^ 40 * 5196210 * 2
def baseEnd_5196210 : Nat := 296461479077691115353119

theorem tailTrace_5196210 : CollatzResearch.WordTrace tailWord_5196210 prefixEnd_5196210 296461479077691115353119 := by
  unfold tailWord_5196210
  simp only [CollatzResearch.WordTrace]
  refine ⟨47380337126256521715060521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126347565670017391240161389 47380337126256521715060521)
  ·
    refine ⟨35535252844692391286295391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47380337126256521715060521 35535252844692391286295391)
    ·
      refine ⟨53302879267038586929443087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35535252844692391286295391 53302879267038586929443087)
      ·
        refine ⟨79954318900557880394164631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53302879267038586929443087 79954318900557880394164631)
        ·
          refine ⟨119931478350836820591246947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79954318900557880394164631 119931478350836820591246947)
          ·
            refine ⟨179897217526255230886870421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119931478350836820591246947 179897217526255230886870421)
            ·
              refine ⟨8432682071543213947822051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179897217526255230886870421 8432682071543213947822051)
              ·
                refine ⟨12649023107314820921733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8432682071543213947822051 12649023107314820921733077)
                ·
                  refine ⟨296461479077691115353119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12649023107314820921733077 296461479077691115353119)
                  ·
                    rfl

theorem cell23_5196210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_5196210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196210 prefixEnd_5196210 := by exact prefixLift 5196210
  have htrace : WordTrace (prefixWord ++ tailWord_5196210) baseStart_5196210 baseEnd_5196210 := by
    simpa [prefixWord, tailWord_5196210, baseEnd_5196210] using wordTrace_append hprefix tailTrace_5196210
  have hstable : (prefixWord ++ tailWord_5196210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196210).length < 2 ^ (prefixWord ++ tailWord_5196210).sum := by decide
  have hdescent : baseEnd_5196210 < baseStart_5196210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196225 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5196225 : Nat := 118140960795 + 5196225 * 2 ^ 59
def prefixEnd_5196225 : Nat := 4983230072969 + 3 ^ 40 * 5196225 * 2
def baseEnd_5196225 : Nat := 2668161013909037479490503

theorem tailTrace_5196225 : CollatzResearch.WordTrace tailWord_5196225 prefixEnd_5196225 2668161013909037479490503 := by
  unfold tailWord_5196225
  simp only [CollatzResearch.WordTrace]
  refine ⟨189521895599971744422038129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126347930399981162948025419 189521895599971744422038129)
  ·
    refine ⟨142141421699978808316528597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189521895599971744422038129 142141421699978808316528597)
    ·
      refine ⟨3331439571093253319918639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 142141421699978808316528597 3331439571093253319918639)
      ·
        refine ⟨4997159356639879979877959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3331439571093253319918639 4997159356639879979877959)
        ·
          refine ⟨7495739034959819969816939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997159356639879979877959 7495739034959819969816939)
          ·
            refine ⟨11243608552439729954725409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495739034959819969816939 11243608552439729954725409)
            ·
              refine ⟨8432706414329797466044057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11243608552439729954725409 8432706414329797466044057)
              ·
                refine ⟨6324529810747348099533043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8432706414329797466044057 6324529810747348099533043)
                ·
                  refine ⟨9486794716121022149299565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6324529810747348099533043 9486794716121022149299565)
                  ·
                    refine ⟨3557548018545383305987337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9486794716121022149299565 3557548018545383305987337)
                    ·
                      refine ⟨2668161013909037479490503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557548018545383305987337 2668161013909037479490503)
                      ·
                        rfl

theorem cell23_5196225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5196225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196225 prefixEnd_5196225 := by exact prefixLift 5196225
  have htrace : WordTrace (prefixWord ++ tailWord_5196225) baseStart_5196225 baseEnd_5196225 := by
    simpa [prefixWord, tailWord_5196225, baseEnd_5196225] using wordTrace_append hprefix tailTrace_5196225
  have hstable : (prefixWord ++ tailWord_5196225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196225).length < 2 ^ (prefixWord ++ tailWord_5196225).sum := by decide
  have hdescent : baseEnd_5196225 < baseStart_5196225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196243 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_5196243 : Nat := 118140960795 + 5196243 * 2 ^ 59
def prefixEnd_5196243 : Nat := 4983230072969 + 3 ^ 40 * 5196243 * 2
def baseEnd_5196243 : Nat := 2668170256560818409065419

theorem tailTrace_5196243 : CollatzResearch.WordTrace tailWord_5196243 prefixEnd_5196243 2668170256560818409065419 := by
  unfold tailWord_5196243
  simp only [CollatzResearch.WordTrace]
  refine ⟨189522552113906533496193383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126348368075937688997462255 189522552113906533496193383)
  ·
    refine ⟨284283828170859800244290075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189522552113906533496193383 284283828170859800244290075)
    ·
      refine ⟨426425742256289700366435113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284283828170859800244290075 426425742256289700366435113)
      ·
        refine ⟨319819306692217275274826335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426425742256289700366435113 319819306692217275274826335)
        ·
          refine ⟨479728960038325912912239503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319819306692217275274826335 479728960038325912912239503)
          ·
            refine ⟨719593440057488869368359255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479728960038325912912239503 719593440057488869368359255)
            ·
              refine ⟨1079390160086233304052538883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719593440057488869368359255 1079390160086233304052538883)
              ·
                refine ⟨1619085240129349956078808325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079390160086233304052538883 1619085240129349956078808325)
                ·
                  refine ⟨303578482524253116764776561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619085240129349956078808325 303578482524253116764776561)
                  ·
                    refine ⟨227683861893189837573582421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 303578482524253116764776561 227683861893189837573582421)
                    ·
                      refine ⟨2668170256560818409065419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 227683861893189837573582421 2668170256560818409065419)
                      ·
                        rfl

theorem cell23_5196243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_5196243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196243 prefixEnd_5196243 := by exact prefixLift 5196243
  have htrace : WordTrace (prefixWord ++ tailWord_5196243) baseStart_5196243 baseEnd_5196243 := by
    simpa [prefixWord, tailWord_5196243, baseEnd_5196243] using wordTrace_append hprefix tailTrace_5196243
  have hstable : (prefixWord ++ tailWord_5196243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196243).length < 2 ^ (prefixWord ++ tailWord_5196243).sum := by decide
  have hdescent : baseEnd_5196243 < baseStart_5196243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196244 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 5]
def baseStart_5196244 : Nat := 118140960795 + 5196244 * 2 ^ 59
def prefixEnd_5196244 : Nat := 4983230072969 + 3 ^ 40 * 5196244 * 2
def baseEnd_5196244 : Nat := 296463418893496989461435

theorem tailTrace_5196244 : CollatzResearch.WordTrace tailWord_5196244 prefixEnd_5196244 296463418893496989461435 := by
  unfold tailWord_5196244
  simp only [CollatzResearch.WordTrace]
  refine ⟨94761294293451455333489893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126348392391268607111319857 94761294293451455333489893)
  ·
    refine ⟨17767742680022147875029355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94761294293451455333489893 17767742680022147875029355)
    ·
      refine ⟨26651614020033221812544033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17767742680022147875029355 26651614020033221812544033)
      ·
        refine ⟨19988710515024916359408025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26651614020033221812544033 19988710515024916359408025)
        ·
          refine ⟨14991532886268687269556019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19988710515024916359408025 14991532886268687269556019)
          ·
            refine ⟨22487299329403030904334029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14991532886268687269556019 22487299329403030904334029)
            ·
              refine ⟨8432737248526136589125261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22487299329403030904334029 8432737248526136589125261)
              ·
                refine ⟨3162276468197301220921973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8432737248526136589125261 3162276468197301220921973)
                ·
                  refine ⟨296463418893496989461435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162276468197301220921973 296463418893496989461435)
                  ·
                    rfl

theorem cell23_5196244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_5196244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196244 prefixEnd_5196244 := by exact prefixLift 5196244
  have htrace : WordTrace (prefixWord ++ tailWord_5196244) baseStart_5196244 baseEnd_5196244 := by
    simpa [prefixWord, tailWord_5196244, baseEnd_5196244] using wordTrace_append hprefix tailTrace_5196244
  have hstable : (prefixWord ++ tailWord_5196244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196244).length < 2 ^ (prefixWord ++ tailWord_5196244).sum := by decide
  have hdescent : baseEnd_5196244 < baseStart_5196244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196250 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_5196250 : Nat := 118140960795 + 5196250 * 2 ^ 59
def prefixEnd_5196250 : Nat := 4983230072969 + 3 ^ 40 * 5196250 * 2
def baseEnd_5196250 : Nat := 2668173850925399881677887

theorem tailTrace_5196250 : CollatzResearch.WordTrace tailWord_5196250 prefixEnd_5196250 2668173850925399881677887 := by
  unfold tailWord_5196250
  simp only [CollatzResearch.WordTrace]
  refine ⟨47380701856220293422924551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126348538283254115794465469 47380701856220293422924551)
  ·
    refine ⟨71071052784330440134386827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47380701856220293422924551 71071052784330440134386827)
    ·
      refine ⟨106606579176495660201580241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71071052784330440134386827 106606579176495660201580241)
      ·
        refine ⟨79954934382371745151185181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106606579176495660201580241 79954934382371745151185181)
        ·
          refine ⟨29983100393389404431694443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79954934382371745151185181 29983100393389404431694443)
          ·
            refine ⟨44974650590084106647541665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29983100393389404431694443 44974650590084106647541665)
            ·
              refine ⟨33730987942563079985656249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44974650590084106647541665 33730987942563079985656249)
              ·
                refine ⟨25298240956922309989242187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33730987942563079985656249 25298240956922309989242187)
                ·
                  refine ⟨37947361435383464983863281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25298240956922309989242187 37947361435383464983863281)
                  ·
                    refine ⟨28460521076537598737897461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37947361435383464983863281 28460521076537598737897461)
                    ·
                      refine ⟨2668173850925399881677887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28460521076537598737897461 2668173850925399881677887)
                      ·
                        rfl

theorem cell23_5196250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_5196250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196250 prefixEnd_5196250 := by exact prefixLift 5196250
  have htrace : WordTrace (prefixWord ++ tailWord_5196250) baseStart_5196250 baseEnd_5196250 := by
    simpa [prefixWord, tailWord_5196250, baseEnd_5196250] using wordTrace_append hprefix tailTrace_5196250
  have hstable : (prefixWord ++ tailWord_5196250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196250).length < 2 ^ (prefixWord ++ tailWord_5196250).sum := by decide
  have hdescent : baseEnd_5196250 < baseStart_5196250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196261 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 5]
def baseStart_5196261 : Nat := 118140960795 + 5196261 * 2 ^ 59
def prefixEnd_5196261 : Nat := 4983230072969 + 3 ^ 40 * 5196261 * 2
def baseEnd_5196261 : Nat := 296464388801399926515593

theorem tailTrace_5196261 : CollatzResearch.WordTrace tailWord_5196261 prefixEnd_5196261 296464388801399926515593 := by
  unfold tailWord_5196261
  simp only [CollatzResearch.WordTrace]
  refine ⟨189523208627841322570348637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126348805751894215046899091 189523208627841322570348637)
  ·
    refine ⟨71071203235440495963880739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189523208627841322570348637 71071203235440495963880739)
    ·
      refine ⟨106606804853160743945821109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71071203235440495963880739 106606804853160743945821109)
      ·
        refine ⟨9994387954983819744920729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106606804853160743945821109 9994387954983819744920729)
        ·
          refine ⟨7495790966237864808690547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9994387954983819744920729 7495790966237864808690547)
          ·
            refine ⟨11243686449356797213035821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495790966237864808690547 11243686449356797213035821)
            ·
              refine ⟨4216382418508798954888433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243686449356797213035821 4216382418508798954888433)
              ·
                refine ⟨3162286813881599216166325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216382418508798954888433 3162286813881599216166325)
                ·
                  refine ⟨296464388801399926515593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162286813881599216166325 296464388801399926515593)
                  ·
                    rfl

theorem cell23_5196261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_5196261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196261 prefixEnd_5196261 := by exact prefixLift 5196261
  have htrace : WordTrace (prefixWord ++ tailWord_5196261) baseStart_5196261 baseEnd_5196261 := by
    simpa [prefixWord, tailWord_5196261, baseEnd_5196261] using wordTrace_append hprefix tailTrace_5196261
  have hstable : (prefixWord ++ tailWord_5196261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196261).length < 2 ^ (prefixWord ++ tailWord_5196261).sum := by decide
  have hdescent : baseEnd_5196261 < baseStart_5196261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196317 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 6]
def baseStart_5196317 : Nat := 118140960795 + 5196317 * 2 ^ 59
def prefixEnd_5196317 : Nat := 4983230072969 + 3 ^ 40 * 5196317 * 2
def baseEnd_5196317 : Nat := 296467583792139013282231

theorem tailTrace_5196317 : CollatzResearch.WordTrace tailWord_5196317 prefixEnd_5196317 296467583792139013282231 := by
  unfold tailWord_5196317
  simp only [CollatzResearch.WordTrace]
  refine ⟨189525251115638444134387205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126350167410425629422924803 189525251115638444134387205)
  ·
    refine ⟨35535984584182208275197601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189525251115638444134387205 35535984584182208275197601)
    ·
      refine ⟨26651988438136656206398201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35535984584182208275197601 26651988438136656206398201)
      ·
        refine ⟨19988991328602492154798651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26651988438136656206398201 19988991328602492154798651)
        ·
          refine ⟨29983486992903738232197977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19988991328602492154798651 29983486992903738232197977)
          ·
            refine ⟨22487615244677803674148483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29983486992903738232197977 22487615244677803674148483)
            ·
              refine ⟨33731422867016705511222725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22487615244677803674148483 33731422867016705511222725)
              ·
                refine ⟨6324641787565632283354261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33731422867016705511222725 6324641787565632283354261)
                ·
                  refine ⟨296467583792139013282231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6324641787565632283354261 296467583792139013282231)
                  ·
                    rfl

theorem cell23_5196317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_5196317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196317 prefixEnd_5196317 := by exact prefixLift 5196317
  have htrace : WordTrace (prefixWord ++ tailWord_5196317) baseStart_5196317 baseEnd_5196317 := by
    simpa [prefixWord, tailWord_5196317, baseEnd_5196317] using wordTrace_append hprefix tailTrace_5196317
  have hstable : (prefixWord ++ tailWord_5196317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196317).length < 2 ^ (prefixWord ++ tailWord_5196317).sum := by decide
  have hdescent : baseEnd_5196317 < baseStart_5196317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196344 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_5196344 : Nat := 118140960795 + 5196344 * 2 ^ 59
def prefixEnd_5196344 : Nat := 4983230072969 + 3 ^ 40 * 5196344 * 2
def baseEnd_5196344 : Nat := 2668222118106922513902455

theorem tailTrace_5196344 : CollatzResearch.WordTrace tailWord_5196344 prefixEnd_5196344 2668222118106922513902455 := by
  unfold tailWord_5196344
  simp only [CollatzResearch.WordTrace]
  refine ⟨94763117943270313872810043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126350823924360418497080057 94763117943270313872810043)
  ·
    refine ⟨142144676914905470809215065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94763117943270313872810043 142144676914905470809215065)
    ·
      refine ⟨106608507686179103106911299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142144676914905470809215065 106608507686179103106911299)
      ·
        refine ⟨159912761529268654660366949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106608507686179103106911299 159912761529268654660366949)
        ·
          refine ⟨29983642786737872748818803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159912761529268654660366949 29983642786737872748818803)
          ·
            refine ⟨44975464180106809123228205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29983642786737872748818803 44975464180106809123228205)
            ·
              refine ⟨16865799067540053421210577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44975464180106809123228205 16865799067540053421210577)
              ·
                refine ⟨12649349300655040065907933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16865799067540053421210577 12649349300655040065907933)
                ·
                  refine ⟨4743505987745640024715475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12649349300655040065907933 4743505987745640024715475)
                  ·
                    refine ⟨7115258981618460037073213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743505987745640024715475 7115258981618460037073213)
                    ·
                      refine ⟨2668222118106922513902455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7115258981618460037073213 2668222118106922513902455)
                      ·
                        rfl

theorem cell23_5196344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_5196344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196344 prefixEnd_5196344 := by exact prefixLift 5196344
  have htrace : WordTrace (prefixWord ++ tailWord_5196344) baseStart_5196344 baseEnd_5196344 := by
    simpa [prefixWord, tailWord_5196344, baseEnd_5196344] using wordTrace_append hprefix tailTrace_5196344
  have hstable : (prefixWord ++ tailWord_5196344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196344).length < 2 ^ (prefixWord ++ tailWord_5196344).sum := by decide
  have hdescent : baseEnd_5196344 < baseStart_5196344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196387 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5196387 : Nat := 118140960795 + 5196387 * 2 ^ 59
def prefixEnd_5196387 : Nat := 4983230072969 + 3 ^ 40 * 5196387 * 2
def baseEnd_5196387 : Nat := 2668244197775065845664757

theorem tailTrace_5196387 : CollatzResearch.WordTrace tailWord_5196387 prefixEnd_5196387 2668244197775065845664757 := by
  unfold tailWord_5196387
  simp only [CollatzResearch.WordTrace]
  refine ⟨189527804225384846089435415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126351869483589897392956943 189527804225384846089435415)
  ·
    refine ⟨284291706338077269134153123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189527804225384846089435415 284291706338077269134153123)
    ·
      refine ⟨426437559507115903701229685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284291706338077269134153123 426437559507115903701229685)
      ·
        refine ⟨39978521203792115971990283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 426437559507115903701229685 39978521203792115971990283)
        ·
          refine ⟨59967781805688173957985425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39978521203792115971990283 59967781805688173957985425)
          ·
            refine ⟨44975836354266130468489069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59967781805688173957985425 44975836354266130468489069)
            ·
              refine ⟨16865938632849798925683401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44975836354266130468489069 16865938632849798925683401)
              ·
                refine ⟨12649453974637349194262551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16865938632849798925683401 12649453974637349194262551)
                ·
                  refine ⟨18974180961956023791393827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12649453974637349194262551 18974180961956023791393827)
                  ·
                    refine ⟨28461271442934035687090741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18974180961956023791393827 28461271442934035687090741)
                    ·
                      refine ⟨2668244197775065845664757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28461271442934035687090741 2668244197775065845664757)
                      ·
                        rfl

theorem cell23_5196387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5196387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196387 prefixEnd_5196387 := by exact prefixLift 5196387
  have htrace : WordTrace (prefixWord ++ tailWord_5196387) baseStart_5196387 baseEnd_5196387 := by
    simpa [prefixWord, tailWord_5196387, baseEnd_5196387] using wordTrace_append hprefix tailTrace_5196387
  have hstable : (prefixWord ++ tailWord_5196387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196387).length < 2 ^ (prefixWord ++ tailWord_5196387).sum := by decide
  have hdescent : baseEnd_5196387 < baseStart_5196387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196407 : List Nat := [1, 1, 3, 1, 1, 3, 6, 7]
def baseStart_5196407 : Nat := 118140960795 + 5196407 * 2 ^ 59
def prefixEnd_5196407 : Nat := 4983230072969 + 3 ^ 40 * 5196407 * 2
def baseEnd_5196407 : Nat := 98824239532894658052395

theorem tailTrace_5196407 : CollatzResearch.WordTrace tailWord_5196407 prefixEnd_5196407 98824239532894658052395 := by
  unfold tailWord_5196407
  simp only [CollatzResearch.WordTrace]
  refine ⟨189528533685312389505163475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126352355790208259670108983 189528533685312389505163475)
  ·
    refine ⟨284292800527968584257745213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189528533685312389505163475 284292800527968584257745213)
    ·
      refine ⟨106609800197988219096654455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284292800527968584257745213 106609800197988219096654455)
      ·
        refine ⟨159914700296982328644981683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106609800197988219096654455 159914700296982328644981683)
        ·
          refine ⟨239872050445473492967472525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159914700296982328644981683 239872050445473492967472525)
          ·
            refine ⟨89952018917052559862802197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239872050445473492967472525 89952018917052559862802197)
            ·
              refine ⟨4216500886736838743568853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89952018917052559862802197 4216500886736838743568853)
              ·
                refine ⟨98824239532894658052395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4216500886736838743568853 98824239532894658052395)
                ·
                  rfl

theorem cell23_5196407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 7].length) (baseStart_5196407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196407 prefixEnd_5196407 := by exact prefixLift 5196407
  have htrace : WordTrace (prefixWord ++ tailWord_5196407) baseStart_5196407 baseEnd_5196407 := by
    simpa [prefixWord, tailWord_5196407, baseEnd_5196407] using wordTrace_append hprefix tailTrace_5196407
  have hstable : (prefixWord ++ tailWord_5196407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196407).length < 2 ^ (prefixWord ++ tailWord_5196407).sum := by decide
  have hdescent : baseEnd_5196407 < baseStart_5196407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196455 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5196455 : Nat := 118140960795 + 5196455 * 2 ^ 59
def prefixEnd_5196455 : Nat := 4983230072969 + 3 ^ 40 * 5196455 * 2
def baseEnd_5196455 : Nat := 2668279114459571579614445

theorem tailTrace_5196455 : CollatzResearch.WordTrace tailWord_5196455 prefixEnd_5196455 2668279114459571579614445 := by
  unfold tailWord_5196455
  simp only [CollatzResearch.WordTrace]
  refine ⟨189530284389138493702910819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126353522926092329135273879 189530284389138493702910819)
  ·
    refine ⟨284295426583707740554366229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189530284389138493702910819 284295426583707740554366229)
    ·
      refine ⟨13326348121111300338485917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 284295426583707740554366229 13326348121111300338485917)
      ·
        refine ⟨4997380545416737626932219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13326348121111300338485917 4997380545416737626932219)
        ·
          refine ⟨7496070818125106440398329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997380545416737626932219 7496070818125106440398329)
          ·
            refine ⟨5622053113593829830298747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7496070818125106440398329 5622053113593829830298747)
            ·
              refine ⟨8433079670390744745448121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622053113593829830298747 8433079670390744745448121)
              ·
                refine ⟨6324809752793058559086091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433079670390744745448121 6324809752793058559086091)
                ·
                  refine ⟨9487214629189587838629137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6324809752793058559086091 9487214629189587838629137)
                  ·
                    refine ⟨7115410971892190878971853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9487214629189587838629137 7115410971892190878971853)
                    ·
                      refine ⟨2668279114459571579614445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7115410971892190878971853 2668279114459571579614445)
                      ·
                        rfl

theorem cell23_5196455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5196455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196455 prefixEnd_5196455 := by exact prefixLift 5196455
  have htrace : WordTrace (prefixWord ++ tailWord_5196455) baseStart_5196455 baseEnd_5196455 := by
    simpa [prefixWord, tailWord_5196455, baseEnd_5196455] using wordTrace_append hprefix tailTrace_5196455
  have hstable : (prefixWord ++ tailWord_5196455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196455).length < 2 ^ (prefixWord ++ tailWord_5196455).sum := by decide
  have hdescent : baseEnd_5196455 < baseStart_5196455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196494 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_5196494 : Nat := 118140960795 + 5196494 * 2 ^ 59
def prefixEnd_5196494 : Nat := 4983230072969 + 3 ^ 40 * 5196494 * 2
def baseEnd_5196494 : Nat := 2668299140205096927026765

theorem tailTrace_5196494 : CollatzResearch.WordTrace tailWord_5196494 prefixEnd_5196494 2668299140205096927026765 := by
  unfold tailWord_5196494
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691463354499650420447567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126354471223998135575720357 23691463354499650420447567)
  ·
    refine ⟨35537195031749475630671351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23691463354499650420447567 35537195031749475630671351)
    ·
      refine ⟨53305792547624213446007027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35537195031749475630671351 53305792547624213446007027)
      ·
        refine ⟨79958688821436320169010541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53305792547624213446007027 79958688821436320169010541)
        ·
          refine ⟨29984508308038620063378953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79958688821436320169010541 29984508308038620063378953)
          ·
            refine ⟨22488381231028965047534215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29984508308038620063378953 22488381231028965047534215)
            ·
              refine ⟨33732571846543447571301323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22488381231028965047534215 33732571846543447571301323)
              ·
                refine ⟨50598857769815171356951985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33732571846543447571301323 50598857769815171356951985)
                ·
                  refine ⟨37949143327361378517713989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50598857769815171356951985 37949143327361378517713989)
                  ·
                    refine ⟨7115464373880258472071373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37949143327361378517713989 7115464373880258472071373)
                    ·
                      refine ⟨2668299140205096927026765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7115464373880258472071373 2668299140205096927026765)
                      ·
                        rfl

theorem cell23_5196494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_5196494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196494 prefixEnd_5196494 := by exact prefixLift 5196494
  have htrace : WordTrace (prefixWord ++ tailWord_5196494) baseStart_5196494 baseEnd_5196494 := by
    simpa [prefixWord, tailWord_5196494, baseEnd_5196494] using wordTrace_append hprefix tailTrace_5196494
  have hstable : (prefixWord ++ tailWord_5196494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196494).length < 2 ^ (prefixWord ++ tailWord_5196494).sum := by decide
  have hdescent : baseEnd_5196494 < baseStart_5196494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196497 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 7]
def baseStart_5196497 : Nat := 118140960795 + 5196497 * 2 ^ 59
def prefixEnd_5196497 : Nat := 4983230072969 + 3 ^ 40 * 5196497 * 2
def baseEnd_5196497 : Nat := 296477853405228935032139

theorem tailTrace_5196497 : CollatzResearch.WordTrace tailWord_5196497 prefixEnd_5196497 296477853405228935032139 := by
  unfold tailWord_5196497
  simp only [CollatzResearch.WordTrace]
  refine ⟨189531816254986334875939745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126354544169990889917293163 189531816254986334875939745)
  ·
    refine ⟨142148862191239751156954809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189531816254986334875939745 142148862191239751156954809)
    ·
      refine ⟨106611646643429813367716107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142148862191239751156954809 106611646643429813367716107)
      ·
        refine ⟨159917469965144720051574161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106611646643429813367716107 159917469965144720051574161)
        ·
          refine ⟨119938102473858540038680621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159917469965144720051574161 119938102473858540038680621)
          ·
            refine ⟨44976788427696952514505233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119938102473858540038680621 44976788427696952514505233)
            ·
              refine ⟨33732591320772714385878925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44976788427696952514505233 33732591320772714385878925)
              ·
                refine ⟨12649721745289767894704597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33732591320772714385878925 12649721745289767894704597)
                ·
                  refine ⟨296477853405228935032139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12649721745289767894704597 296477853405228935032139)
                  ·
                    rfl

theorem cell23_5196497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_5196497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196497 prefixEnd_5196497 := by exact prefixLift 5196497
  have htrace : WordTrace (prefixWord ++ tailWord_5196497) baseStart_5196497 baseEnd_5196497 := by
    simpa [prefixWord, tailWord_5196497, baseEnd_5196497] using wordTrace_append hprefix tailTrace_5196497
  have hstable : (prefixWord ++ tailWord_5196497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196497).length < 2 ^ (prefixWord ++ tailWord_5196497).sum := by decide
  have hdescent : baseEnd_5196497 < baseStart_5196497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196501 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_5196501 : Nat := 118140960795 + 5196501 * 2 ^ 59
def prefixEnd_5196501 : Nat := 4983230072969 + 3 ^ 40 * 5196501 * 2
def baseEnd_5196501 : Nat := 889434244856559466546411

theorem tailTrace_5196501 : CollatzResearch.WordTrace tailWord_5196501 prefixEnd_5196501 889434244856559466546411 := by
  unfold tailWord_5196501
  simp only [CollatzResearch.WordTrace]
  refine ⟨189531962146971843559085357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126354641431314562372723571 189531962146971843559085357)
  ·
    refine ⟨71074485805114441334657009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189531962146971843559085357 71074485805114441334657009)
    ·
      refine ⟨53305864353835831000992757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71074485805114441334657009 53305864353835831000992757)
      ·
        refine ⟨4997424783172109156343071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53305864353835831000992757 4997424783172109156343071)
        ·
          refine ⟨7496137174758163734514607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997424783172109156343071 7496137174758163734514607)
          ·
            refine ⟨11244205762137245601771911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496137174758163734514607 11244205762137245601771911)
            ·
              refine ⟨16866308643205868402657867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11244205762137245601771911 16866308643205868402657867)
              ·
                refine ⟨25299462964808802603986801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16866308643205868402657867 25299462964808802603986801)
                ·
                  refine ⟨18974597223606601952990101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25299462964808802603986801 18974597223606601952990101)
                  ·
                    refine ⟨889434244856559466546411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18974597223606601952990101 889434244856559466546411)
                    ·
                      rfl

theorem cell23_5196501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_5196501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196501 prefixEnd_5196501 := by exact prefixLift 5196501
  have htrace : WordTrace (prefixWord ++ tailWord_5196501) baseStart_5196501 baseEnd_5196501 := by
    simpa [prefixWord, tailWord_5196501, baseEnd_5196501] using wordTrace_append hprefix tailTrace_5196501
  have hstable : (prefixWord ++ tailWord_5196501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196501).length < 2 ^ (prefixWord ++ tailWord_5196501).sum := by decide
  have hdescent : baseEnd_5196501 < baseStart_5196501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196504 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_5196504 : Nat := 118140960795 + 5196504 * 2 ^ 59
def prefixEnd_5196504 : Nat := 4983230072969 + 3 ^ 40 * 5196504 * 2
def baseEnd_5196504 : Nat := 2668304275011641887901719

theorem tailTrace_5196504 : CollatzResearch.WordTrace tailWord_5196504 prefixEnd_5196504 2668304275011641887901719 := by
  unfold tailWord_5196504
  simp only [CollatzResearch.WordTrace]
  refine ⟨94766035782980487535722283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126354714377307316714296377 94766035782980487535722283)
  ·
    refine ⟨142149053674470731303583425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94766035782980487535722283 142149053674470731303583425)
    ·
      refine ⟨106611790255853048477687569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142149053674470731303583425 106611790255853048477687569)
      ·
        refine ⟨79958842691889786358265677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106611790255853048477687569 79958842691889786358265677)
        ·
          refine ⟨29984566009458669884349629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79958842691889786358265677 29984566009458669884349629)
          ·
            refine ⟨11244212253547001206631111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29984566009458669884349629 11244212253547001206631111)
            ·
              refine ⟨16866318380320501809946667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11244212253547001206631111 16866318380320501809946667)
              ·
                refine ⟨25299477570480752714920001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16866318380320501809946667 25299477570480752714920001)
                ·
                  refine ⟨18974608177860564536190001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25299477570480752714920001 18974608177860564536190001)
                  ·
                    refine ⟨14230956133395423402142501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18974608177860564536190001 14230956133395423402142501)
                    ·
                      refine ⟨2668304275011641887901719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14230956133395423402142501 2668304275011641887901719)
                      ·
                        rfl

theorem cell23_5196504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_5196504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196504 prefixEnd_5196504 := by exact prefixLift 5196504
  have htrace : WordTrace (prefixWord ++ tailWord_5196504) baseStart_5196504 baseEnd_5196504 := by
    simpa [prefixWord, tailWord_5196504, baseEnd_5196504] using wordTrace_append hprefix tailTrace_5196504
  have hstable : (prefixWord ++ tailWord_5196504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196504).length < 2 ^ (prefixWord ++ tailWord_5196504).sum := by decide
  have hdescent : baseEnd_5196504 < baseStart_5196504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196508 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5196508 : Nat := 118140960795 + 5196508 * 2 ^ 59
def prefixEnd_5196508 : Nat := 4983230072969 + 3 ^ 40 * 5196508 * 2
def baseEnd_5196508 : Nat := 2668306328934259872251701

theorem tailTrace_5196508 : CollatzResearch.WordTrace tailWord_5196508 prefixEnd_5196508 2668306328934259872251701 := by
  unfold tailWord_5196508
  simp only [CollatzResearch.WordTrace]
  refine ⟨94766108728973241877295089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126354811638630989169726785 94766108728973241877295089)
  ·
    refine ⟨71074581546729931407971317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94766108728973241877295089 71074581546729931407971317)
    ·
      refine ⟨6663242020005931069497311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71074581546729931407971317 6663242020005931069497311)
      ·
        refine ⟨9994863030008896604245967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6663242020005931069497311 9994863030008896604245967)
        ·
          refine ⟨14992294545013344906368951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9994863030008896604245967 14992294545013344906368951)
          ·
            refine ⟨22488441817520017359553427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14992294545013344906368951 22488441817520017359553427)
            ·
              refine ⟨33732662726280026039330141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22488441817520017359553427 33732662726280026039330141)
              ·
                refine ⟨12649748522355009764748803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33732662726280026039330141 12649748522355009764748803)
                ·
                  refine ⟨18974622783532514647123205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12649748522355009764748803 18974622783532514647123205)
                  ·
                    refine ⟨3557741771912346496335601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18974622783532514647123205 3557741771912346496335601)
                    ·
                      refine ⟨2668306328934259872251701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557741771912346496335601 2668306328934259872251701)
                      ·
                        rfl

theorem cell23_5196508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5196508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196508 prefixEnd_5196508 := by exact prefixLift 5196508
  have htrace : WordTrace (prefixWord ++ tailWord_5196508) baseStart_5196508 baseEnd_5196508 := by
    simpa [prefixWord, tailWord_5196508, baseEnd_5196508] using wordTrace_append hprefix tailTrace_5196508
  have hstable : (prefixWord ++ tailWord_5196508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196508).length < 2 ^ (prefixWord ++ tailWord_5196508).sum := by decide
  have hdescent : baseEnd_5196508 < baseStart_5196508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196537 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5196537 : Nat := 118140960795 + 5196537 * 2 ^ 59
def prefixEnd_5196537 : Nat := 4983230072969 + 3 ^ 40 * 5196537 * 2
def baseEnd_5196537 : Nat := 2668321219873240258789067

theorem tailTrace_5196537 : CollatzResearch.WordTrace tailWord_5196537 prefixEnd_5196537 2668321219873240258789067 := by
  unfold tailWord_5196537
  simp only [CollatzResearch.WordTrace]
  refine ⟨189533275174841421707395865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126355516783227614471597243 189533275174841421707395865)
  ·
    refine ⟨142149956381131066280546899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189533275174841421707395865 142149956381131066280546899)
    ·
      refine ⟨213224934571696599420820349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142149956381131066280546899 213224934571696599420820349)
      ·
        refine ⟨79959350464386224782807631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213224934571696599420820349 79959350464386224782807631)
        ·
          refine ⟨119939025696579337174211447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79959350464386224782807631 119939025696579337174211447)
          ·
            refine ⟨179908538544869005761317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119939025696579337174211447 179908538544869005761317171)
            ·
              refine ⟨269862807817303508641975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179908538544869005761317171 269862807817303508641975757)
              ·
                refine ⟨101198552931488815740740909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269862807817303508641975757 101198552931488815740740909)
                ·
                  refine ⟨37949457349308305902777841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101198552931488815740740909 37949457349308305902777841)
                  ·
                    refine ⟨28462093011981229427083381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37949457349308305902777841 28462093011981229427083381)
                    ·
                      refine ⟨2668321219873240258789067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28462093011981229427083381 2668321219873240258789067)
                      ·
                        rfl

theorem cell23_5196537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5196537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196537 prefixEnd_5196537 := by exact prefixLift 5196537
  have htrace : WordTrace (prefixWord ++ tailWord_5196537) baseStart_5196537 baseEnd_5196537 := by
    simpa [prefixWord, tailWord_5196537, baseEnd_5196537] using wordTrace_append hprefix tailTrace_5196537
  have hstable : (prefixWord ++ tailWord_5196537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196537).length < 2 ^ (prefixWord ++ tailWord_5196537).sum := by decide
  have hdescent : baseEnd_5196537 < baseStart_5196537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196542 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_5196542 : Nat := 118140960795 + 5196542 * 2 ^ 59
def prefixEnd_5196542 : Nat := 4983230072969 + 3 ^ 40 * 5196542 * 2
def baseEnd_5196542 : Nat := 2668323787276512739226545

theorem tailTrace_5196542 : CollatzResearch.WordTrace tailWord_5196542 prefixEnd_5196542 2668323787276512739226545 := by
  unfold tailWord_5196542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691682192477913445165985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126355638359882205040885253 23691682192477913445165985)
  ·
    refine ⟨17768761644358435083874489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23691682192477913445165985 17768761644358435083874489)
    ·
      refine ⟨13326571233268826312905867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17768761644358435083874489 13326571233268826312905867)
      ·
        refine ⟨19989856849903239469358801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13326571233268826312905867 19989856849903239469358801)
        ·
          refine ⟨14992392637427429602019101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19989856849903239469358801 14992392637427429602019101)
          ·
            refine ⟨5622147239035286100757163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14992392637427429602019101 5622147239035286100757163)
            ·
              refine ⟨8433220858552929151135745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622147239035286100757163 8433220858552929151135745)
              ·
                refine ⟨6324915643914696863351809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433220858552929151135745 6324915643914696863351809)
                ·
                  refine ⟨4743686732936022647513857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6324915643914696863351809 4743686732936022647513857)
                  ·
                    refine ⟨3557765049702016985635393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4743686732936022647513857 3557765049702016985635393)
                    ·
                      refine ⟨2668323787276512739226545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557765049702016985635393 2668323787276512739226545)
                      ·
                        rfl

theorem cell23_5196542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_5196542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196542 prefixEnd_5196542 := by exact prefixLift 5196542
  have htrace : WordTrace (prefixWord ++ tailWord_5196542) baseStart_5196542 baseEnd_5196542 := by
    simpa [prefixWord, tailWord_5196542, baseEnd_5196542] using wordTrace_append hprefix tailTrace_5196542
  have hstable : (prefixWord ++ tailWord_5196542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196542).length < 2 ^ (prefixWord ++ tailWord_5196542).sum := by decide
  have hdescent : baseEnd_5196542 < baseStart_5196542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196587 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 8]
def baseStart_5196587 : Nat := 118140960795 + 5196587 * 2 ^ 59
def prefixEnd_5196587 : Nat := 4983230072969 + 3 ^ 40 * 5196587 * 2
def baseEnd_5196587 : Nat := 296482988211773895907093

theorem tailTrace_5196587 : CollatzResearch.WordTrace tailWord_5196587 prefixEnd_5196587 296482988211773895907093 := by
  unfold tailWord_5196587
  simp only [CollatzResearch.WordTrace]
  refine ⟨189535098824660280246716015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126356732549773520164477343 189535098824660280246716015)
  ·
    refine ⟨284302648236990420370074023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189535098824660280246716015 284302648236990420370074023)
    ·
      refine ⟨426453972355485630555111035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284302648236990420370074023 426453972355485630555111035)
      ·
        refine ⟨639680958533228445832666553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426453972355485630555111035 639680958533228445832666553)
        ·
          refine ⟨479760718899921334374499915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639680958533228445832666553 479760718899921334374499915)
          ·
            refine ⟨719641078349882001561749873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479760718899921334374499915 719641078349882001561749873)
            ·
              refine ⟨539730808762411501171312405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719641078349882001561749873 539730808762411501171312405)
              ·
                refine ⟨25299881660738039117405269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 539730808762411501171312405 25299881660738039117405269)
                ·
                  refine ⟨296482988211773895907093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25299881660738039117405269 296482988211773895907093)
                  ·
                    rfl

theorem cell23_5196587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 8].length) (baseStart_5196587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196587 prefixEnd_5196587 := by exact prefixLift 5196587
  have htrace : WordTrace (prefixWord ++ tailWord_5196587) baseStart_5196587 baseEnd_5196587 := by
    simpa [prefixWord, tailWord_5196587, baseEnd_5196587] using wordTrace_append hprefix tailTrace_5196587
  have hstable : (prefixWord ++ tailWord_5196587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196587).length < 2 ^ (prefixWord ++ tailWord_5196587).sum := by decide
  have hdescent : baseEnd_5196587 < baseStart_5196587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196604 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 6]
def baseStart_5196604 : Nat := 118140960795 + 5196604 * 2 ^ 59
def prefixEnd_5196604 : Nat := 4983230072969 + 3 ^ 40 * 5196604 * 2
def baseEnd_5196604 : Nat := 296483958119676832961251

theorem tailTrace_5196604 : CollatzResearch.WordTrace tailWord_5196604 prefixEnd_5196604 296483958119676832961251 := by
  unfold tailWord_5196604
  simp only [CollatzResearch.WordTrace]
  refine ⟨94767859432799346075042433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126357145910399128100056577 94767859432799346075042433)
  ·
    refine ⟨71075894574599509556281825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94767859432799346075042433 71075894574599509556281825)
    ·
      refine ⟨53306920930949632167211369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71075894574599509556281825 53306920930949632167211369)
      ·
        refine ⟨39980190698212224125408527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53306920930949632167211369 39980190698212224125408527)
        ·
          refine ⟨59970286047318336188112791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39980190698212224125408527 59970286047318336188112791)
          ·
            refine ⟨89955429070977504282169187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59970286047318336188112791 89955429070977504282169187)
            ·
              refine ⟨134933143606466256423253781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89955429070977504282169187 134933143606466256423253781)
              ·
                refine ⟨6324991106553105769840021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134933143606466256423253781 6324991106553105769840021)
                ·
                  refine ⟨296483958119676832961251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6324991106553105769840021 296483958119676832961251)
                  ·
                    rfl

theorem cell23_5196604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_5196604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196604 prefixEnd_5196604 := by exact prefixLift 5196604
  have htrace : WordTrace (prefixWord ++ tailWord_5196604) baseStart_5196604 baseEnd_5196604 := by
    simpa [prefixWord, tailWord_5196604, baseEnd_5196604] using wordTrace_append hprefix tailTrace_5196604
  have hstable : (prefixWord ++ tailWord_5196604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196604).length < 2 ^ (prefixWord ++ tailWord_5196604).sum := by decide
  have hdescent : baseEnd_5196604 < baseStart_5196604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196658 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5196658 : Nat := 118140960795 + 5196658 * 2 ^ 59
def prefixEnd_5196658 : Nat := 4983230072969 + 3 ^ 40 * 5196658 * 2
def baseEnd_5196658 : Nat := 2668383351032434285376011

theorem tailTrace_5196658 : CollatzResearch.WordTrace tailWord_5196658 prefixEnd_5196658 2668383351032434285376011 := by
  unfold tailWord_5196658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47384422101850764843137657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126358458938268706248367085 47384422101850764843137657)
  ·
    refine ⟨35538316576388073632353243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47384422101850764843137657 35538316576388073632353243)
    ·
      refine ⟨53307474864582110448529865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35538316576388073632353243 53307474864582110448529865)
      ·
        refine ⟨39980606148436582836397399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53307474864582110448529865 39980606148436582836397399)
        ·
          refine ⟨59970909222654874254596099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39980606148436582836397399 59970909222654874254596099)
          ·
            refine ⟨89956363833982311381894149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59970909222654874254596099 89956363833982311381894149)
            ·
              refine ⟨16866818218871683384105153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89956363833982311381894149 16866818218871683384105153)
              ·
                refine ⟨12650113664153762538078865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16866818218871683384105153 12650113664153762538078865)
                ·
                  refine ⟨9487585248115321903559149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12650113664153762538078865 9487585248115321903559149)
                  ·
                    refine ⟨3557844468043245713834681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9487585248115321903559149 3557844468043245713834681)
                    ·
                      refine ⟨2668383351032434285376011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557844468043245713834681 2668383351032434285376011)
                      ·
                        rfl

theorem cell23_5196658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5196658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196658 prefixEnd_5196658 := by exact prefixLift 5196658
  have htrace : WordTrace (prefixWord ++ tailWord_5196658) baseStart_5196658 baseEnd_5196658 := by
    simpa [prefixWord, tailWord_5196658, baseEnd_5196658] using wordTrace_append hprefix tailTrace_5196658
  have hstable : (prefixWord ++ tailWord_5196658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196658).length < 2 ^ (prefixWord ++ tailWord_5196658).sum := by decide
  have hdescent : baseEnd_5196658 < baseStart_5196658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196665 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 1, 1, 3]
def baseStart_5196665 : Nat := 118140960795 + 5196665 * 2 ^ 59
def prefixEnd_5196665 : Nat := 4983230072969 + 3 ^ 40 * 5196665 * 2
def baseEnd_5196665 : Nat := 2668386945397015757988479

theorem tailTrace_5196665 : CollatzResearch.WordTrace tailWord_5196665 prefixEnd_5196665 2668386945397015757988479 := by
  unfold tailWord_5196665
  simp only [CollatzResearch.WordTrace]
  refine ⟨189537943718377699568055449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126358629145585133045370299 189537943718377699568055449)
  ·
    refine ⟨142153457788783274676041587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189537943718377699568055449 142153457788783274676041587)
    ·
      refine ⟨213230186683174912014062381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142153457788783274676041587 213230186683174912014062381)
      ·
        refine ⟨79961320006190592005273393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213230186683174912014062381 79961320006190592005273393)
        ·
          refine ⟨59970990004642944003955045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79961320006190592005273393 59970990004642944003955045)
          ·
            refine ⟨11244560625870552000741571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59970990004642944003955045 11244560625870552000741571)
            ·
              refine ⟨16866840938805828001112357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11244560625870552000741571 16866840938805828001112357)
              ·
                refine ⟨3162532676026092750208567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16866840938805828001112357 3162532676026092750208567)
                ·
                  refine ⟨4743799014039139125312851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162532676026092750208567 4743799014039139125312851)
                  ·
                    refine ⟨7115698521058708687969277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743799014039139125312851 7115698521058708687969277)
                    ·
                      refine ⟨2668386945397015757988479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7115698521058708687969277 2668386945397015757988479)
                      ·
                        rfl

theorem cell23_5196665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_5196665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196665 prefixEnd_5196665 := by exact prefixLift 5196665
  have htrace : WordTrace (prefixWord ++ tailWord_5196665) baseStart_5196665 baseEnd_5196665 := by
    simpa [prefixWord, tailWord_5196665, baseEnd_5196665] using wordTrace_append hprefix tailTrace_5196665
  have hstable : (prefixWord ++ tailWord_5196665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196665).length < 2 ^ (prefixWord ++ tailWord_5196665).sum := by decide
  have hdescent : baseEnd_5196665 < baseStart_5196665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196681 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_5196681 : Nat := 118140960795 + 5196681 * 2 ^ 59
def prefixEnd_5196681 : Nat := 4983230072969 + 3 ^ 40 * 5196681 * 2
def baseEnd_5196681 : Nat := 889465053695829231796135

theorem tailTrace_5196681 : CollatzResearch.WordTrace tailWord_5196681 prefixEnd_5196681 889465053695829231796135 := by
  unfold tailWord_5196681
  simp only [CollatzResearch.WordTrace]
  refine ⟨189538527286319734300637897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126359018190879822867091931 189538527286319734300637897)
  ·
    refine ⟨142153895464739800725478423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189538527286319734300637897 142153895464739800725478423)
    ·
      refine ⟨213230843197109701088217635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142153895464739800725478423 213230843197109701088217635)
      ·
        refine ⟨319846264795664551632326453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213230843197109701088217635 319846264795664551632326453)
        ·
          refine ⟨29985587324593551715530605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 319846264795664551632326453 29985587324593551715530605)
          ·
            refine ⟨11244595246722581893323977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29985587324593551715530605 11244595246722581893323977)
            ·
              refine ⟨8433446435041936419992983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11244595246722581893323977 8433446435041936419992983)
              ·
                refine ⟨12650169652562904629989475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8433446435041936419992983 12650169652562904629989475)
                ·
                  refine ⟨18975254478844356944984213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12650169652562904629989475 18975254478844356944984213)
                  ·
                    refine ⟨889465053695829231796135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18975254478844356944984213 889465053695829231796135)
                    ·
                      rfl

theorem cell23_5196681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_5196681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196681 prefixEnd_5196681 := by exact prefixLift 5196681
  have htrace : WordTrace (prefixWord ++ tailWord_5196681) baseStart_5196681 baseEnd_5196681 := by
    simpa [prefixWord, tailWord_5196681, baseEnd_5196681] using wordTrace_append hprefix tailTrace_5196681
  have hstable : (prefixWord ++ tailWord_5196681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196681).length < 2 ^ (prefixWord ++ tailWord_5196681).sum := by decide
  have hdescent : baseEnd_5196681 < baseStart_5196681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196684 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_5196684 : Nat := 118140960795 + 5196684 * 2 ^ 59
def prefixEnd_5196684 : Nat := 4983230072969 + 3 ^ 40 * 5196684 * 2
def baseEnd_5196684 : Nat := 2668396701529451183650891

theorem tailTrace_5196684 : CollatzResearch.WordTrace tailWord_5196684 prefixEnd_5196684 2668396701529451183650891 := by
  unfold tailWord_5196684
  simp only [CollatzResearch.WordTrace]
  refine ⟨94769318352654432906498553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126359091136872577208664737 94769318352654432906498553)
  ·
    refine ⟨71076988764490824679873915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94769318352654432906498553 71076988764490824679873915)
    ·
      refine ⟨106615483146736237019810873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71076988764490824679873915 106615483146736237019810873)
      ·
        refine ⟨79961612360052177764858155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106615483146736237019810873 79961612360052177764858155)
        ·
          refine ⟨119942418540078266647287233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79961612360052177764858155 119942418540078266647287233)
          ·
            refine ⟨89956813905058699985465425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119942418540078266647287233 89956813905058699985465425)
            ·
              refine ⟨67467610428794024989099069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89956813905058699985465425 67467610428794024989099069)
              ·
                refine ⟨25300353910797759370912151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67467610428794024989099069 25300353910797759370912151)
                ·
                  refine ⟨37950530866196639056368227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25300353910797759370912151 37950530866196639056368227)
                  ·
                    refine ⟨56925796299294958584552341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37950530866196639056368227 56925796299294958584552341)
                    ·
                      refine ⟨2668396701529451183650891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56925796299294958584552341 2668396701529451183650891)
                      ·
                        rfl

theorem cell23_5196684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_5196684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196684 prefixEnd_5196684 := by exact prefixLift 5196684
  have htrace : WordTrace (prefixWord ++ tailWord_5196684) baseStart_5196684 baseEnd_5196684 := by
    simpa [prefixWord, tailWord_5196684, baseEnd_5196684] using wordTrace_append hprefix tailTrace_5196684
  have hstable : (prefixWord ++ tailWord_5196684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196684).length < 2 ^ (prefixWord ++ tailWord_5196684).sum := by decide
  have hdescent : baseEnd_5196684 < baseStart_5196684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196701 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5196701 : Nat := 118140960795 + 5196701 * 2 ^ 59
def prefixEnd_5196701 : Nat := 4983230072969 + 3 ^ 40 * 5196701 * 2
def baseEnd_5196701 : Nat := 2668405430700577617138313

theorem tailTrace_5196701 : CollatzResearch.WordTrace tailWord_5196701 prefixEnd_5196701 2668405430700577617138313 := by
  unfold tailWord_5196701
  simp only [CollatzResearch.WordTrace]
  refine ⟨189539256746247277716365957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126359504497498185144243971 189539256746247277716365957)
  ·
    refine ⟨35538610639921364571818617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189539256746247277716365957 35538610639921364571818617)
    ·
      refine ⟨26653957979941023428863963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35538610639921364571818617 26653957979941023428863963)
      ·
        refine ⟨39980936969911535143295945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26653957979941023428863963 39980936969911535143295945)
        ·
          refine ⟨29985702727433651357471959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39980936969911535143295945 29985702727433651357471959)
          ·
            refine ⟨44978554091150477036207939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29985702727433651357471959 44978554091150477036207939)
            ·
              refine ⟨67467831136725715554311909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44978554091150477036207939 67467831136725715554311909)
              ·
                refine ⟨12650218338136071666433483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67467831136725715554311909 12650218338136071666433483)
                ·
                  refine ⟨18975327507204107499650225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12650218338136071666433483 18975327507204107499650225)
                  ·
                    refine ⟨14231495630403080624737669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18975327507204107499650225 14231495630403080624737669)
                    ·
                      refine ⟨2668405430700577617138313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14231495630403080624737669 2668405430700577617138313)
                      ·
                        rfl

theorem cell23_5196701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5196701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196701 prefixEnd_5196701 := by exact prefixLift 5196701
  have htrace : WordTrace (prefixWord ++ tailWord_5196701) baseStart_5196701 baseEnd_5196701 := by
    simpa [prefixWord, tailWord_5196701, baseEnd_5196701] using wordTrace_append hprefix tailTrace_5196701
  have hstable : (prefixWord ++ tailWord_5196701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196701).length < 2 ^ (prefixWord ++ tailWord_5196701).sum := by decide
  have hdescent : baseEnd_5196701 < baseStart_5196701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196705 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5196705 : Nat := 118140960795 + 5196705 * 2 ^ 59
def prefixEnd_5196705 : Nat := 4983230072969 + 3 ^ 40 * 5196705 * 2
def baseEnd_5196705 : Nat := 2668407484623195601488295

theorem tailTrace_5196705 : CollatzResearch.WordTrace tailWord_5196705 prefixEnd_5196705 2668407484623195601488295 := by
  unfold tailWord_5196705
  simp only [CollatzResearch.WordTrace]
  refine ⟨189539402638232786399511569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126359601758821857599674379 189539402638232786399511569)
  ·
    refine ⟨142154551978674589799633677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189539402638232786399511569 142154551978674589799633677)
    ·
      refine ⟨53307956992002971174862629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142154551978674589799633677 53307956992002971174862629)
      ·
        refine ⟨9995241936000557095286743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53307956992002971174862629 9995241936000557095286743)
        ·
          refine ⟨14992862904000835642930115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9995241936000557095286743 14992862904000835642930115)
          ·
            refine ⟨22489294356001253464395173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14992862904000835642930115 22489294356001253464395173)
            ·
              refine ⟨4216742691750235024574095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22489294356001253464395173 4216742691750235024574095)
              ·
                refine ⟨6325114037625352536861143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216742691750235024574095 6325114037625352536861143)
                ·
                  refine ⟨9487671056438028805291715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325114037625352536861143 9487671056438028805291715)
                  ·
                    refine ⟨14231506584657043207937573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9487671056438028805291715 14231506584657043207937573)
                    ·
                      refine ⟨2668407484623195601488295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14231506584657043207937573 2668407484623195601488295)
                      ·
                        rfl

theorem cell23_5196705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5196705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196705 prefixEnd_5196705 := by exact prefixLift 5196705
  have htrace : WordTrace (prefixWord ++ tailWord_5196705) baseStart_5196705 baseEnd_5196705 := by
    simpa [prefixWord, tailWord_5196705, baseEnd_5196705] using wordTrace_append hprefix tailTrace_5196705
  have hstable : (prefixWord ++ tailWord_5196705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196705).length < 2 ^ (prefixWord ++ tailWord_5196705).sum := by decide
  have hdescent : baseEnd_5196705 < baseStart_5196705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196708 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_5196708 : Nat := 118140960795 + 5196708 * 2 ^ 59
def prefixEnd_5196708 : Nat := 4983230072969 + 3 ^ 40 * 5196708 * 2
def baseEnd_5196708 : Nat := 2668409025065159089750781

theorem tailTrace_5196708 : CollatzResearch.WordTrace tailWord_5196708 prefixEnd_5196708 2668409025065159089750781 := by
  unfold tailWord_5196708
  simp only [CollatzResearch.WordTrace]
  refine ⟨94769756028610958955935389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126359674704814611941247185 94769756028610958955935389)
  ·
    refine ⟨35538658510729109608475771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94769756028610958955935389 35538658510729109608475771)
    ·
      refine ⟨53307987766093664412713657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35538658510729109608475771 53307987766093664412713657)
      ·
        refine ⟨39980990824570248309535243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53307987766093664412713657 39980990824570248309535243)
        ·
          refine ⟨59971486236855372464302865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39980990824570248309535243 59971486236855372464302865)
          ·
            refine ⟨44978614677641529348227149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59971486236855372464302865 44978614677641529348227149)
            ·
              refine ⟨16866980504115573505585181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44978614677641529348227149 16866980504115573505585181)
              ·
                refine ⟨6325117689043340064594443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16866980504115573505585181 6325117689043340064594443)
                ·
                  refine ⟨9487676533565010096891665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325117689043340064594443 9487676533565010096891665)
                  ·
                    refine ⟨7115757400173757572668749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9487676533565010096891665 7115757400173757572668749)
                    ·
                      refine ⟨2668409025065159089750781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7115757400173757572668749 2668409025065159089750781)
                      ·
                        rfl

theorem cell23_5196708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_5196708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196708 prefixEnd_5196708 := by exact prefixLift 5196708
  have htrace : WordTrace (prefixWord ++ tailWord_5196708) baseStart_5196708 baseEnd_5196708 := by
    simpa [prefixWord, tailWord_5196708, baseEnd_5196708] using wordTrace_append hprefix tailTrace_5196708
  have hstable : (prefixWord ++ tailWord_5196708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196708).length < 2 ^ (prefixWord ++ tailWord_5196708).sum := by decide
  have hdescent : baseEnd_5196708 < baseStart_5196708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196711 : List Nat := [1, 1, 6, 1, 3, 1, 10]
def baseStart_5196711 : Nat := 118140960795 + 5196711 * 2 ^ 59
def prefixEnd_5196711 : Nat := 4983230072969 + 3 ^ 40 * 5196711 * 2
def baseEnd_5196711 : Nat := 32943340314902747876707

theorem tailTrace_5196711 : CollatzResearch.WordTrace tailWord_5196711 prefixEnd_5196711 32943340314902747876707 := by
  unfold tailWord_5196711
  simp only [CollatzResearch.WordTrace]
  refine ⟨189539621476211049424229987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126359747650807366282819991 189539621476211049424229987)
  ·
    refine ⟨284309432214316574136344981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189539621476211049424229987 284309432214316574136344981)
    ·
      refine ⟨13327004635046089412641171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 284309432214316574136344981 13327004635046089412641171)
      ·
        refine ⟨19990506952569134118961757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13327004635046089412641171 19990506952569134118961757)
        ·
          refine ⟨7496440107213425294610659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19990506952569134118961757 7496440107213425294610659)
          ·
            refine ⟨11244660160820137941915989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496440107213425294610659 11244660160820137941915989)
            ·
              refine ⟨32943340314902747876707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11244660160820137941915989 32943340314902747876707)
              ·
                rfl

theorem cell23_5196711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 10].length) (baseStart_5196711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196711 prefixEnd_5196711 := by exact prefixLift 5196711
  have htrace : WordTrace (prefixWord ++ tailWord_5196711) baseStart_5196711 baseEnd_5196711 := by
    simpa [prefixWord, tailWord_5196711, baseEnd_5196711] using wordTrace_append hprefix tailTrace_5196711
  have hstable : (prefixWord ++ tailWord_5196711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196711).length < 2 ^ (prefixWord ++ tailWord_5196711).sum := by decide
  have hdescent : baseEnd_5196711 < baseStart_5196711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196789 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5196789 : Nat := 118140960795 + 5196789 * 2 ^ 59
def prefixEnd_5196789 : Nat := 4983230072969 + 3 ^ 40 * 5196789 * 2
def baseEnd_5196789 : Nat := 2668450616998173272837909

theorem tailTrace_5196789 : CollatzResearch.WordTrace tailWord_5196789 prefixEnd_5196789 2668450616998173272837909 := by
  unfold tailWord_5196789
  simp only [CollatzResearch.WordTrace]
  refine ⟨189542466369928468745569421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126361644246618979163712947 189542466369928468745569421)
  ·
    refine ⟨71078424888723175779588533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189542466369928468745569421 71078424888723175779588533)
    ·
      refine ⟨6663602333317797729336425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71078424888723175779588533 6663602333317797729336425)
      ·
        refine ⟨4997701749988348297002319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6663602333317797729336425 4997701749988348297002319)
        ·
          refine ⟨7496552624982522445503479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4997701749988348297002319 7496552624982522445503479)
          ·
            refine ⟨11244828937473783668255219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496552624982522445503479 11244828937473783668255219)
            ·
              refine ⟨16867243406210675502382829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11244828937473783668255219 16867243406210675502382829)
              ·
                refine ⟨6325216277329003313393561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16867243406210675502382829 6325216277329003313393561)
                ·
                  refine ⟨4743912207996752485045171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325216277329003313393561 4743912207996752485045171)
                  ·
                    refine ⟨7115868311995128727567757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743912207996752485045171 7115868311995128727567757)
                    ·
                      refine ⟨2668450616998173272837909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7115868311995128727567757 2668450616998173272837909)
                      ·
                        rfl

theorem cell23_5196789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5196789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196789 prefixEnd_5196789 := by exact prefixLift 5196789
  have htrace : WordTrace (prefixWord ++ tailWord_5196789) baseStart_5196789 baseEnd_5196789 := by
    simpa [prefixWord, tailWord_5196789, baseEnd_5196789] using wordTrace_append hprefix tailTrace_5196789
  have hstable : (prefixWord ++ tailWord_5196789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196789).length < 2 ^ (prefixWord ++ tailWord_5196789).sum := by decide
  have hdescent : baseEnd_5196789 < baseStart_5196789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196829 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_5196829 : Nat := 118140960795 + 5196829 * 2 ^ 59
def prefixEnd_5196829 : Nat := 4983230072969 + 3 ^ 40 * 5196829 * 2
def baseEnd_5196829 : Nat := 2668471156224353116337725

theorem tailTrace_5196829 : CollatzResearch.WordTrace tailWord_5196829 prefixEnd_5196829 2668471156224353116337725 := by
  unfold tailWord_5196829
  simp only [CollatzResearch.WordTrace]
  refine ⟨189543925289783555577025541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126362616859855703718017027 189543925289783555577025541)
  ·
    refine ⟨35539485991834416670692289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189543925289783555577025541 35539485991834416670692289)
    ·
      refine ⟨26654614493875812503019217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35539485991834416670692289 26654614493875812503019217)
      ·
        refine ⟨19990960870406859377264413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26654614493875812503019217 19990960870406859377264413)
        ·
          refine ⟨7496610326402572266474155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19990960870406859377264413 7496610326402572266474155)
          ·
            refine ⟨11244915489603858399711233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496610326402572266474155 11244915489603858399711233)
            ·
              refine ⟨8433686617202893799783425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11244915489603858399711233 8433686617202893799783425)
              ·
                refine ⟨6325264962902170349837569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433686617202893799783425 6325264962902170349837569)
                ·
                  refine ⟨4743948722176627762378177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325264962902170349837569 4743948722176627762378177)
                  ·
                    refine ⟨3557961541632470821783633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4743948722176627762378177 3557961541632470821783633)
                    ·
                      refine ⟨2668471156224353116337725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557961541632470821783633 2668471156224353116337725)
                      ·
                        rfl

theorem cell23_5196829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_5196829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196829 prefixEnd_5196829 := by exact prefixLift 5196829
  have htrace : WordTrace (prefixWord ++ tailWord_5196829) baseStart_5196829 baseEnd_5196829 := by
    simpa [prefixWord, tailWord_5196829, baseEnd_5196829] using wordTrace_append hprefix tailTrace_5196829
  have hstable : (prefixWord ++ tailWord_5196829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196829).length < 2 ^ (prefixWord ++ tailWord_5196829).sum := by decide
  have hdescent : baseEnd_5196829 < baseStart_5196829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196835 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 5]
def baseStart_5196835 : Nat := 118140960795 + 5196835 * 2 ^ 59
def prefixEnd_5196835 : Nat := 4983230072969 + 3 ^ 40 * 5196835 * 2
def baseEnd_5196835 : Nat := 296497137456475565873633

theorem tailTrace_5196835 : CollatzResearch.WordTrace tailWord_5196835 prefixEnd_5196835 296497137456475565873633 := by
  unfold tailWord_5196835
  simp only [CollatzResearch.WordTrace]
  refine ⟨189544144127761818601743959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126362762751841212401162639 189544144127761818601743959)
  ·
    refine ⟨284316216191642727902615939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189544144127761818601743959 284316216191642727902615939)
    ·
      refine ⟨426474324287464091853923909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284316216191642727902615939 426474324287464091853923909)
      ·
        refine ⟨79963935803899517222610733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 426474324287464091853923909 79963935803899517222610733)
        ·
          refine ⟨29986475926462318958479025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79963935803899517222610733 29986475926462318958479025)
          ·
            refine ⟨22489856944846739218859269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29986475926462318958479025 22489856944846739218859269)
            ·
              refine ⟨4216848177158763603536113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22489856944846739218859269 4216848177158763603536113)
              ·
                refine ⟨3162636132869072702652085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216848177158763603536113 3162636132869072702652085)
                ·
                  refine ⟨296497137456475565873633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162636132869072702652085 296497137456475565873633)
                  ·
                    rfl

theorem cell23_5196835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 5].length) (baseStart_5196835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196835 prefixEnd_5196835 := by exact prefixLift 5196835
  have htrace : WordTrace (prefixWord ++ tailWord_5196835) baseStart_5196835 baseEnd_5196835 := by
    simpa [prefixWord, tailWord_5196835, baseEnd_5196835] using wordTrace_append hprefix tailTrace_5196835
  have hstable : (prefixWord ++ tailWord_5196835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196835).length < 2 ^ (prefixWord ++ tailWord_5196835).sum := by decide
  have hdescent : baseEnd_5196835 < baseStart_5196835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196851 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_5196851 : Nat := 118140960795 + 5196851 * 2 ^ 59
def prefixEnd_5196851 : Nat := 4983230072969 + 3 ^ 40 * 5196851 * 2
def baseEnd_5196851 : Nat := 2668482452798752030262623

theorem tailTrace_5196851 : CollatzResearch.WordTrace tailWord_5196851 prefixEnd_5196851 2668482452798752030262623 := by
  unfold tailWord_5196851
  simp only [CollatzResearch.WordTrace]
  refine ⟨189544727695703853334326407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126363151797135902222884271 189544727695703853334326407)
  ·
    refine ⟨284317091543555780001489611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189544727695703853334326407 284317091543555780001489611)
    ·
      refine ⟨426475637315333670002234417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284317091543555780001489611 426475637315333670002234417)
      ·
        refine ⟨319856727986500252501675813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426475637315333670002234417 319856727986500252501675813)
        ·
          refine ⟨59973136497468797344064215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319856727986500252501675813 59973136497468797344064215)
          ·
            refine ⟨89959704746203196016096323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59973136497468797344064215 89959704746203196016096323)
            ·
              refine ⟨134939557119304794024144485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89959704746203196016096323 134939557119304794024144485)
              ·
                refine ⟨25301166959869648879527091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134939557119304794024144485 25301166959869648879527091)
                ·
                  refine ⟨37951750439804473319290637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25301166959869648879527091 37951750439804473319290637)
                  ·
                    refine ⟨14231906414926677494733989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37951750439804473319290637 14231906414926677494733989)
                    ·
                      refine ⟨2668482452798752030262623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14231906414926677494733989 2668482452798752030262623)
                      ·
                        rfl

theorem cell23_5196851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_5196851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196851 prefixEnd_5196851 := by exact prefixLift 5196851
  have htrace : WordTrace (prefixWord ++ tailWord_5196851) baseStart_5196851 baseEnd_5196851 := by
    simpa [prefixWord, tailWord_5196851, baseEnd_5196851] using wordTrace_append hprefix tailTrace_5196851
  have hstable : (prefixWord ++ tailWord_5196851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196851).length < 2 ^ (prefixWord ++ tailWord_5196851).sum := by decide
  have hdescent : baseEnd_5196851 < baseStart_5196851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196878 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_5196878 : Nat := 118140960795 + 5196878 * 2 ^ 59
def prefixEnd_5196878 : Nat := 4983230072969 + 3 ^ 40 * 5196878 * 2
def baseEnd_5196878 : Nat := 889498772258807808208333

theorem tailTrace_5196878 : CollatzResearch.WordTrace tailWord_5196878 prefixEnd_5196878 889498772258807808208333 := by
  unfold tailWord_5196878
  simp only [CollatzResearch.WordTrace]
  refine ⟨23693214058325754618194911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126363808311070691297039525 23693214058325754618194911)
  ·
    refine ⟨35539821087488631927292367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23693214058325754618194911 35539821087488631927292367)
    ·
      refine ⟨53309731631232947890938551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35539821087488631927292367 53309731631232947890938551)
      ·
        refine ⟨79964597446849421836407827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53309731631232947890938551 79964597446849421836407827)
        ·
          refine ⟨119946896170274132754611741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79964597446849421836407827 119946896170274132754611741)
          ·
            refine ⟨44980086063852799782979403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119946896170274132754611741 44980086063852799782979403)
            ·
              refine ⟨67470129095779199674469105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44980086063852799782979403 67470129095779199674469105)
              ·
                refine ⟨50602596821834399755851829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67470129095779199674469105 50602596821834399755851829)
                ·
                  refine ⟨4743993452046974977111109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50602596821834399755851829 4743993452046974977111109)
                  ·
                    refine ⟨889498772258807808208333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4743993452046974977111109 889498772258807808208333)
                    ·
                      rfl

theorem cell23_5196878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_5196878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196878 prefixEnd_5196878 := by exact prefixLift 5196878
  have htrace : WordTrace (prefixWord ++ tailWord_5196878) baseStart_5196878 baseEnd_5196878 := by
    simpa [prefixWord, tailWord_5196878, baseEnd_5196878] using wordTrace_append hprefix tailTrace_5196878
  have hstable : (prefixWord ++ tailWord_5196878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196878).length < 2 ^ (prefixWord ++ tailWord_5196878).sum := by decide
  have hdescent : baseEnd_5196878 < baseStart_5196878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196881 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_5196881 : Nat := 118140960795 + 5196881 * 2 ^ 59
def prefixEnd_5196881 : Nat := 4983230072969 + 3 ^ 40 * 5196881 * 2
def baseEnd_5196881 : Nat := 2668497857218386912887485

theorem tailTrace_5196881 : CollatzResearch.WordTrace tailWord_5196881 prefixEnd_5196881 2668497857218386912887485 := by
  unfold tailWord_5196881
  simp only [CollatzResearch.WordTrace]
  refine ⟨189545821885595168457918497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126363881257063445638612331 189545821885595168457918497)
  ·
    refine ⟨142159366414196376343438873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189545821885595168457918497 142159366414196376343438873)
    ·
      refine ⟨106619524810647282257579155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142159366414196376343438873 106619524810647282257579155)
      ·
        refine ⟨159929287215970923386368733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106619524810647282257579155 159929287215970923386368733)
        ·
          refine ⟨59973482705989096269888275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159929287215970923386368733 59973482705989096269888275)
          ·
            refine ⟨89960224058983644404832413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59973482705989096269888275 89960224058983644404832413)
            ·
              refine ⟨33735084022118866651812155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89960224058983644404832413 33735084022118866651812155)
              ·
                refine ⟨50602626033178299977718233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33735084022118866651812155 50602626033178299977718233)
                ·
                  refine ⟨37951969524883724983288675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50602626033178299977718233 37951969524883724983288675)
                  ·
                    refine ⟨56927954287325587474933013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37951969524883724983288675 56927954287325587474933013)
                    ·
                      refine ⟨2668497857218386912887485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56927954287325587474933013 2668497857218386912887485)
                      ·
                        rfl

theorem cell23_5196881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_5196881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196881 prefixEnd_5196881 := by exact prefixLift 5196881
  have htrace : WordTrace (prefixWord ++ tailWord_5196881) baseStart_5196881 baseEnd_5196881 := by
    simpa [prefixWord, tailWord_5196881, baseEnd_5196881] using wordTrace_append hprefix tailTrace_5196881
  have hstable : (prefixWord ++ tailWord_5196881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196881).length < 2 ^ (prefixWord ++ tailWord_5196881).sum := by decide
  have hdescent : baseEnd_5196881 < baseStart_5196881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196888 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_5196888 : Nat := 118140960795 + 5196888 * 2 ^ 59
def prefixEnd_5196888 : Nat := 4983230072969 + 3 ^ 40 * 5196888 * 2
def baseEnd_5196888 : Nat := 2668501451582968385499953

theorem tailTrace_5196888 : CollatzResearch.WordTrace tailWord_5196888 prefixEnd_5196888 2668501451582968385499953 := by
  unfold tailWord_5196888
  simp only [CollatzResearch.WordTrace]
  refine ⟨94773038598284904326711659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126364051464379872435615545 94773038598284904326711659)
  ·
    refine ⟨142159557897427356490067489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94773038598284904326711659 142159557897427356490067489)
    ·
      refine ⟨106619668423070517367550617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142159557897427356490067489 106619668423070517367550617)
      ·
        refine ⟨79964751317302888025662963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106619668423070517367550617 79964751317302888025662963)
        ·
          refine ⟨119947126975954332038494445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79964751317302888025662963 119947126975954332038494445)
          ·
            refine ⟨44980172615982874514435417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119947126975954332038494445 44980172615982874514435417)
            ·
              refine ⟨33735129461987155885826563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44980172615982874514435417 33735129461987155885826563)
              ·
                refine ⟨50602694192980733828739845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33735129461987155885826563 50602694192980733828739845)
                ·
                  refine ⟨9488005161183887592888721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50602694192980733828739845 9488005161183887592888721)
                  ·
                    refine ⟨7116003870887915694666541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9488005161183887592888721 7116003870887915694666541)
                    ·
                      refine ⟨2668501451582968385499953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116003870887915694666541 2668501451582968385499953)
                      ·
                        rfl

theorem cell23_5196888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_5196888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196888 prefixEnd_5196888 := by exact prefixLift 5196888
  have htrace : WordTrace (prefixWord ++ tailWord_5196888) baseStart_5196888 baseEnd_5196888 := by
    simpa [prefixWord, tailWord_5196888, baseEnd_5196888] using wordTrace_append hprefix tailTrace_5196888
  have hstable : (prefixWord ++ tailWord_5196888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196888).length < 2 ^ (prefixWord ++ tailWord_5196888).sum := by decide
  have hdescent : baseEnd_5196888 < baseStart_5196888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196895 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 1, 4]
def baseStart_5196895 : Nat := 118140960795 + 5196895 * 2 ^ 59
def prefixEnd_5196895 : Nat := 4983230072969 + 3 ^ 40 * 5196895 * 2
def baseEnd_5196895 : Nat := 889501681982516619370807

theorem tailTrace_5196895 : CollatzResearch.WordTrace tailWord_5196895 prefixEnd_5196895 889501681982516619370807 := by
  unfold tailWord_5196895
  simp only [CollatzResearch.WordTrace]
  refine ⟨189546332507544448848928139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126364221671696299232618759 189546332507544448848928139)
  ·
    refine ⟨284319498761316673273392209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189546332507544448848928139 284319498761316673273392209)
    ·
      refine ⟨213239624070987504955044157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284319498761316673273392209 213239624070987504955044157)
      ·
        refine ⟨79964859026620314358141559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213239624070987504955044157 79964859026620314358141559)
        ·
          refine ⟨119947288539930471537212339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79964859026620314358141559 119947288539930471537212339)
          ·
            refine ⟨179920932809895707305818509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119947288539930471537212339 179920932809895707305818509)
            ·
              refine ⟨67470349803710890239681941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179920932809895707305818509 67470349803710890239681941)
              ·
                refine ⟨3162672647048947979985091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67470349803710890239681941 3162672647048947979985091)
                ·
                  refine ⟨4744008970573421969977637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162672647048947979985091 4744008970573421969977637)
                  ·
                    refine ⟨889501681982516619370807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744008970573421969977637 889501681982516619370807)
                    ·
                      rfl

theorem cell23_5196895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 4].length) (baseStart_5196895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196895 prefixEnd_5196895 := by exact prefixLift 5196895
  have htrace : WordTrace (prefixWord ++ tailWord_5196895) baseStart_5196895 baseEnd_5196895 := by
    simpa [prefixWord, tailWord_5196895, baseEnd_5196895] using wordTrace_append hprefix tailTrace_5196895
  have hstable : (prefixWord ++ tailWord_5196895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196895).length < 2 ^ (prefixWord ++ tailWord_5196895).sum := by decide
  have hdescent : baseEnd_5196895 < baseStart_5196895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196911 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_5196911 : Nat := 118140960795 + 5196911 * 2 ^ 59
def prefixEnd_5196911 : Nat := 4983230072969 + 3 ^ 40 * 5196911 * 2
def baseEnd_5196911 : Nat := 2668513261638021795512347

theorem tailTrace_5196911 : CollatzResearch.WordTrace tailWord_5196911 prefixEnd_5196911 2668513261638021795512347 := by
  unfold tailWord_5196911
  simp only [CollatzResearch.WordTrace]
  refine ⟨189546916075486483581510587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126364610716990989054340391 189546916075486483581510587)
  ·
    refine ⟨284320374113229725372265881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189546916075486483581510587 284320374113229725372265881)
    ·
      refine ⟨213240280584922294029199411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284320374113229725372265881 213240280584922294029199411)
      ·
        refine ⟨319860420877383441043799117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213240280584922294029199411 319860420877383441043799117)
        ·
          refine ⟨119947657829018790391424669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319860420877383441043799117 119947657829018790391424669)
          ·
            refine ⟨44980371685882046396784251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119947657829018790391424669 44980371685882046396784251)
            ·
              refine ⟨67470557528823069595176377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44980371685882046396784251 67470557528823069595176377)
              ·
                refine ⟨50602918146617302196382283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67470557528823069595176377 50602918146617302196382283)
                ·
                  refine ⟨75904377219925953294573425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50602918146617302196382283 75904377219925953294573425)
                  ·
                    refine ⟨56928282914944464970930069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75904377219925953294573425 56928282914944464970930069)
                    ·
                      refine ⟨2668513261638021795512347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56928282914944464970930069 2668513261638021795512347)
                      ·
                        rfl

theorem cell23_5196911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_5196911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196911 prefixEnd_5196911 := by exact prefixLift 5196911
  have htrace : WordTrace (prefixWord ++ tailWord_5196911) baseStart_5196911 baseEnd_5196911 := by
    simpa [prefixWord, tailWord_5196911, baseEnd_5196911] using wordTrace_append hprefix tailTrace_5196911
  have hstable : (prefixWord ++ tailWord_5196911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196911).length < 2 ^ (prefixWord ++ tailWord_5196911).sum := by decide
  have hdescent : baseEnd_5196911 < baseStart_5196911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196929 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 1, 4]
def baseStart_5196929 : Nat := 118140960795 + 5196929 * 2 ^ 59
def prefixEnd_5196929 : Nat := 4983230072969 + 3 ^ 40 * 5196929 * 2
def baseEnd_5196929 : Nat := 889507501429934241695755

theorem tailTrace_5196929 : CollatzResearch.WordTrace tailWord_5196929 prefixEnd_5196929 889507501429934241695755 := by
  unfold tailWord_5196929
  simp only [CollatzResearch.WordTrace]
  refine ⟨189547572589421272655665841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126365048392947515103777227 189547572589421272655665841)
  ·
    refine ⟨142160679442065954491749381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189547572589421272655665841 142160679442065954491749381)
    ·
      refine ⟨26655127395387366467203009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142160679442065954491749381 26655127395387366467203009)
      ·
        refine ⟨19991345546540524850402257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26655127395387366467203009 19991345546540524850402257)
        ·
          refine ⟨14993509159905393637801693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19991345546540524850402257 14993509159905393637801693)
          ·
            refine ⟨5622565934964522614175635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14993509159905393637801693 5622565934964522614175635)
            ·
              refine ⟨8433848902446783921263453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622565934964522614175635 8433848902446783921263453)
              ·
                refine ⟨3162693338417543970473795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8433848902446783921263453 3162693338417543970473795)
                ·
                  refine ⟨4744040007626315955710693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162693338417543970473795 4744040007626315955710693)
                  ·
                    refine ⟨889507501429934241695755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744040007626315955710693 889507501429934241695755)
                    ·
                      rfl

theorem cell23_5196929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_5196929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196929 prefixEnd_5196929 := by exact prefixLift 5196929
  have htrace : WordTrace (prefixWord ++ tailWord_5196929) baseStart_5196929 baseEnd_5196929 := by
    simpa [prefixWord, tailWord_5196929, baseEnd_5196929] using wordTrace_append hprefix tailTrace_5196929
  have hstable : (prefixWord ++ tailWord_5196929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196929).length < 2 ^ (prefixWord ++ tailWord_5196929).sum := by decide
  have hdescent : baseEnd_5196929 < baseStart_5196929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196952 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5196952 : Nat := 118140960795 + 5196952 * 2 ^ 59
def prefixEnd_5196952 : Nat := 4983230072969 + 3 ^ 40 * 5196952 * 2
def baseEnd_5196952 : Nat := 2668534314344856135099659

theorem tailTrace_5196952 : CollatzResearch.WordTrace tailWord_5196952 prefixEnd_5196952 2668534314344856135099659 := by
  unfold tailWord_5196952
  simp only [CollatzResearch.WordTrace]
  refine ⟨94774205734168973791876555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126365607645558631722502073 94774205734168973791876555)
  ·
    refine ⟨142161308601253460687814833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94774205734168973791876555 142161308601253460687814833)
    ·
      refine ⟨106620981450940095515861125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142161308601253460687814833 106620981450940095515861125)
      ·
        refine ⟨19991434022051267909223961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106620981450940095515861125 19991434022051267909223961)
        ·
          refine ⟨14993575516538450931917971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19991434022051267909223961 14993575516538450931917971)
          ·
            refine ⟨22490363274807676397876957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14993575516538450931917971 22490363274807676397876957)
            ·
              refine ⟨8433886228052878649203859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22490363274807676397876957 8433886228052878649203859)
              ·
                refine ⟨12650829342079317973805789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8433886228052878649203859 12650829342079317973805789)
                ·
                  refine ⟨4744061003279744240177171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12650829342079317973805789 4744061003279744240177171)
                  ·
                    refine ⟨7116091504919616360265757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744061003279744240177171 7116091504919616360265757)
                    ·
                      refine ⟨2668534314344856135099659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116091504919616360265757 2668534314344856135099659)
                      ·
                        rfl

theorem cell23_5196952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5196952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196952 prefixEnd_5196952 := by exact prefixLift 5196952
  have htrace : WordTrace (prefixWord ++ tailWord_5196952) baseStart_5196952 baseEnd_5196952 := by
    simpa [prefixWord, tailWord_5196952, baseEnd_5196952] using wordTrace_append hprefix tailTrace_5196952
  have hstable : (prefixWord ++ tailWord_5196952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196952).length < 2 ^ (prefixWord ++ tailWord_5196952).sum := by decide
  have hdescent : baseEnd_5196952 < baseStart_5196952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196959 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 6]
def baseStart_5196959 : Nat := 118140960795 + 5196959 * 2 ^ 59
def prefixEnd_5196959 : Nat := 4983230072969 + 3 ^ 40 * 5196959 * 2
def baseEnd_5196959 : Nat := 296504212078826400856903

theorem tailTrace_5196959 : CollatzResearch.WordTrace tailWord_5196959 prefixEnd_5196959 296504212078826400856903 := by
  unfold tailWord_5196959
  simp only [CollatzResearch.WordTrace]
  refine ⟨189548666779312587779257931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126365777852875058519505287 189548666779312587779257931)
  ·
    refine ⟨284323000168968881668886897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189548666779312587779257931 284323000168968881668886897)
    ·
      refine ⟨213242250126726661251665173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284323000168968881668886897 213242250126726661251665173)
      ·
        refine ⟨9995730474690312246171805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213242250126726661251665173 9995730474690312246171805)
        ·
          refine ⟨3748398928008867092314427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9995730474690312246171805 3748398928008867092314427)
          ·
            refine ⟨5622598392013300638471641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748398928008867092314427 5622598392013300638471641)
            ·
              refine ⟨4216948794009975478853731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5622598392013300638471641 4216948794009975478853731)
              ·
                refine ⟨6325423191014963218280597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216948794009975478853731 6325423191014963218280597)
                ·
                  refine ⟨296504212078826400856903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6325423191014963218280597 296504212078826400856903)
                  ·
                    rfl

theorem cell23_5196959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 6].length) (baseStart_5196959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196959 prefixEnd_5196959 := by exact prefixLift 5196959
  have htrace : WordTrace (prefixWord ++ tailWord_5196959) baseStart_5196959 baseEnd_5196959 := by
    simpa [prefixWord, tailWord_5196959, baseEnd_5196959] using wordTrace_append hprefix tailTrace_5196959
  have hstable : (prefixWord ++ tailWord_5196959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196959).length < 2 ^ (prefixWord ++ tailWord_5196959).sum := by decide
  have hdescent : baseEnd_5196959 < baseStart_5196959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196975 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_5196975 : Nat := 118140960795 + 5196975 * 2 ^ 59
def prefixEnd_5196975 : Nat := 4983230072969 + 3 ^ 40 * 5196975 * 2
def baseEnd_5196975 : Nat := 2668546124399909545112053

theorem tailTrace_5196975 : CollatzResearch.WordTrace tailWord_5196975 prefixEnd_5196975 2668546124399909545112053 := by
  unfold tailWord_5196975
  simp only [CollatzResearch.WordTrace]
  refine ⟨189549250347254622511840379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126366166898169748341226919 189549250347254622511840379)
  ·
    refine ⟨284323875520881933767760569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189549250347254622511840379 284323875520881933767760569)
    ·
      refine ⟨213242906640661450325820427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284323875520881933767760569 213242906640661450325820427)
      ·
        refine ⟨319864359960992175488730641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213242906640661450325820427 319864359960992175488730641)
        ·
          refine ⟨239898269970744131616547981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319864359960992175488730641 239898269970744131616547981)
          ·
            refine ⟨89961851239029049356205493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239898269970744131616547981 89961851239029049356205493)
            ·
              refine ⟨8433923553658973377144265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89961851239029049356205493 8433923553658973377144265)
              ·
                refine ⟨6325442665244230032858199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433923553658973377144265 6325442665244230032858199)
                ·
                  refine ⟨9488163997866345049287299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325442665244230032858199 9488163997866345049287299)
                  ·
                    refine ⟨14232245996799517573930949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9488163997866345049287299 14232245996799517573930949)
                    ·
                      refine ⟨2668546124399909545112053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14232245996799517573930949 2668546124399909545112053)
                      ·
                        rfl

theorem cell23_5196975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_5196975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196975 prefixEnd_5196975 := by exact prefixLift 5196975
  have htrace : WordTrace (prefixWord ++ tailWord_5196975) baseStart_5196975 baseEnd_5196975 := by
    simpa [prefixWord, tailWord_5196975, baseEnd_5196975] using wordTrace_append hprefix tailTrace_5196975
  have hstable : (prefixWord ++ tailWord_5196975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196975).length < 2 ^ (prefixWord ++ tailWord_5196975).sum := by decide
  have hdescent : baseEnd_5196975 < baseStart_5196975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197002 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_5197002 : Nat := 118140960795 + 5197002 * 2 ^ 59
def prefixEnd_5197002 : Nat := 4983230072969 + 3 ^ 40 * 5197002 * 2
def baseEnd_5197002 : Nat := 889519996125860313158143

theorem tailTrace_5197002 : CollatzResearch.WordTrace tailWord_5197002 prefixEnd_5197002 889519996125860313158143 := by
  unfold tailWord_5197002
  simp only [CollatzResearch.WordTrace]
  refine ⟨47387558779539201530768315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126366823412104537415382173 47387558779539201530768315)
  ·
    refine ⟨71081338169308802296152473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47387558779539201530768315 71081338169308802296152473)
    ·
      refine ⟨53311003626981601722114355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71081338169308802296152473 53311003626981601722114355)
      ·
        refine ⟨79966505440472402583171533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53311003626981601722114355 79966505440472402583171533)
        ·
          refine ⟨29987439540177150968689325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79966505440472402583171533 29987439540177150968689325)
          ·
            refine ⟨11245289827566431613258497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29987439540177150968689325 11245289827566431613258497)
            ·
              refine ⟨8433967370674823709943873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11245289827566431613258497 8433967370674823709943873)
              ·
                refine ⟨6325475528006117782457905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433967370674823709943873 6325475528006117782457905)
                ·
                  refine ⟨4744106646004588336843429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325475528006117782457905 4744106646004588336843429)
                  ·
                    refine ⟨889519996125860313158143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744106646004588336843429 889519996125860313158143)
                    ·
                      rfl

theorem cell23_5197002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_5197002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197002 prefixEnd_5197002 := by exact prefixLift 5197002
  have htrace : WordTrace (prefixWord ++ tailWord_5197002) baseStart_5197002 baseEnd_5197002 := by
    simpa [prefixWord, tailWord_5197002, baseEnd_5197002] using wordTrace_append hprefix tailTrace_5197002
  have hstable : (prefixWord ++ tailWord_5197002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197002).length < 2 ^ (prefixWord ++ tailWord_5197002).sum := by decide
  have hdescent : baseEnd_5197002 < baseStart_5197002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197025 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_5197025 : Nat := 118140960795 + 5197025 * 2 ^ 59
def prefixEnd_5197025 : Nat := 4983230072969 + 3 ^ 40 * 5197025 * 2
def baseEnd_5197025 : Nat := 2668571798432634349486823

theorem tailTrace_5197025 : CollatzResearch.WordTrace tailWord_5197025 prefixEnd_5197025 2668571798432634349486823 := by
  unfold tailWord_5197025
  simp only [CollatzResearch.WordTrace]
  refine ⟨189551073997073481051160529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126367382664715654034107019 189551073997073481051160529)
  ·
    refine ⟨142163305497805110788370397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189551073997073481051160529 142163305497805110788370397)
    ·
      refine ⟨53311239561676916545638899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142163305497805110788370397 53311239561676916545638899)
      ·
        refine ⟨79966859342515374818458349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53311239561676916545638899 79966859342515374818458349)
        ·
          refine ⟨29987572253443265556921881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79966859342515374818458349 29987572253443265556921881)
          ·
            refine ⟨22490679190082449167691411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29987572253443265556921881 22490679190082449167691411)
            ·
              refine ⟨33736018785123673751537117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22490679190082449167691411 33736018785123673751537117)
              ·
                refine ⟨12651007044421377656826419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33736018785123673751537117 12651007044421377656826419)
                ·
                  refine ⟨18976510566632066485239629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12651007044421377656826419 18976510566632066485239629)
                  ·
                    refine ⟨7116191462487024931964861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18976510566632066485239629 7116191462487024931964861)
                    ·
                      refine ⟨2668571798432634349486823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116191462487024931964861 2668571798432634349486823)
                      ·
                        rfl

theorem cell23_5197025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_5197025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197025 prefixEnd_5197025 := by exact prefixLift 5197025
  have htrace : WordTrace (prefixWord ++ tailWord_5197025) baseStart_5197025 baseEnd_5197025 := by
    simpa [prefixWord, tailWord_5197025, baseEnd_5197025] using wordTrace_append hprefix tailTrace_5197025
  have hstable : (prefixWord ++ tailWord_5197025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197025).length < 2 ^ (prefixWord ++ tailWord_5197025).sum := by decide
  have hdescent : baseEnd_5197025 < baseStart_5197025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197059 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 3]
def baseStart_5197059 : Nat := 118140960795 + 5197059 * 2 ^ 59
def prefixEnd_5197059 : Nat := 4983230072969 + 3 ^ 40 * 5197059 * 2
def baseEnd_5197059 : Nat := 2668589256774887216461667

theorem tailTrace_5197059 : CollatzResearch.WordTrace tailWord_5197059 prefixEnd_5197059 2668589256774887216461667 := by
  unfold tailWord_5197059
  simp only [CollatzResearch.WordTrace]
  refine ⟨189552314078950304857898231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126368209385966869905265487 189552314078950304857898231)
  ·
    refine ⟨284328471118425457286847347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189552314078950304857898231 284328471118425457286847347)
    ·
      refine ⟨426492706677638185930271021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284328471118425457286847347 426492706677638185930271021)
      ·
        refine ⟨159934765004114319723851633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426492706677638185930271021 159934765004114319723851633)
        ·
          refine ⟨119951073753085739792888725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159934765004114319723851633 119951073753085739792888725)
          ·
            refine ⟨5622706582175894052791659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119951073753085739792888725 5622706582175894052791659)
            ·
              refine ⟨8434059873263841079187489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622706582175894052791659 8434059873263841079187489)
              ·
                refine ⟨6325544904947880809390617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8434059873263841079187489 6325544904947880809390617)
                ·
                  refine ⟨4744158678710910607042963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325544904947880809390617 4744158678710910607042963)
                  ·
                    refine ⟨7116238018066365910564445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744158678710910607042963 7116238018066365910564445)
                    ·
                      refine ⟨2668589256774887216461667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116238018066365910564445 2668589256774887216461667)
                      ·
                        rfl

theorem cell23_5197059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_5197059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197059 prefixEnd_5197059 := by exact prefixLift 5197059
  have htrace : WordTrace (prefixWord ++ tailWord_5197059) baseStart_5197059 baseEnd_5197059 := by
    simpa [prefixWord, tailWord_5197059, baseEnd_5197059] using wordTrace_append hprefix tailTrace_5197059
  have hstable : (prefixWord ++ tailWord_5197059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197059).length < 2 ^ (prefixWord ++ tailWord_5197059).sum := by decide
  have hdescent : baseEnd_5197059 < baseStart_5197059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197152 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_5197152 : Nat := 118140960795 + 5197152 * 2 ^ 59
def prefixEnd_5197152 : Nat := 4983230072969 + 3 ^ 40 * 5197152 * 2
def baseEnd_5197152 : Nat := 889545670158585117532913

theorem tailTrace_5197152 : CollatzResearch.WordTrace tailWord_5197152 prefixEnd_5197152 889545670158585117532913 := by
  unfold tailWord_5197152
  simp only [CollatzResearch.WordTrace]
  refine ⟨94777853033806690870516855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126370470711742254494022473 94777853033806690870516855)
  ·
    refine ⟨142166779550710036305775283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94777853033806690870516855 142166779550710036305775283)
    ·
      refine ⟨213250169326065054458662925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142166779550710036305775283 213250169326065054458662925)
      ·
        refine ⟨79968813497274395421998597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213250169326065054458662925 79968813497274395421998597)
        ·
          refine ⟨14994152530738949141624737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79968813497274395421998597 14994152530738949141624737)
          ·
            refine ⟨11245614398054211856218553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14994152530738949141624737 11245614398054211856218553)
            ·
              refine ⟨8434210798540658892163915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11245614398054211856218553 8434210798540658892163915)
              ·
                refine ⟨12651316197810988338245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434210798540658892163915 12651316197810988338245873)
                ·
                  refine ⟨9488487148358241253684405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12651316197810988338245873 9488487148358241253684405)
                  ·
                    refine ⟨889545670158585117532913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9488487148358241253684405 889545670158585117532913)
                    ·
                      rfl

theorem cell23_5197152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_5197152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197152 prefixEnd_5197152 := by exact prefixLift 5197152
  have htrace : WordTrace (prefixWord ++ tailWord_5197152) baseStart_5197152 baseEnd_5197152 := by
    simpa [prefixWord, tailWord_5197152, baseEnd_5197152] using wordTrace_append hprefix tailTrace_5197152
  have hstable : (prefixWord ++ tailWord_5197152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197152).length < 2 ^ (prefixWord ++ tailWord_5197152).sum := by decide
  have hdescent : baseEnd_5197152 < baseStart_5197152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197173 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 5]
def baseStart_5197173 : Nat := 118140960795 + 5197173 * 2 ^ 59
def prefixEnd_5197173 : Nat := 4983230072969 + 3 ^ 40 * 5197173 * 2
def baseEnd_5197173 : Nat := 296516421507722196715127

theorem tailTrace_5197173 : CollatzResearch.WordTrace tailWord_5197173 prefixEnd_5197173 296516421507722196715127 := by
  unfold tailWord_5197173
  simp only [CollatzResearch.WordTrace]
  refine ⟨189556472000537302327548173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126370981333691534885032115 189556472000537302327548173)
  ·
    refine ⟨71083677000201488372830565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189556472000537302327548173 71083677000201488372830565)
    ·
      refine ⟨13328189437537779069905731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71083677000201488372830565 13328189437537779069905731)
      ·
        refine ⟨19992284156306668604858597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13328189437537779069905731 19992284156306668604858597)
        ·
          refine ⟨3748553279307500363410987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19992284156306668604858597 3748553279307500363410987)
          ·
            refine ⟨5622829918961250545116481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748553279307500363410987 5622829918961250545116481)
            ·
              refine ⟨4217122439220937908837361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5622829918961250545116481 4217122439220937908837361)
              ·
                refine ⟨3162841829415703431628021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217122439220937908837361 3162841829415703431628021)
                ·
                  refine ⟨296516421507722196715127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162841829415703431628021 296516421507722196715127)
                  ·
                    rfl

theorem cell23_5197173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_5197173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197173 prefixEnd_5197173 := by exact prefixLift 5197173
  have htrace : WordTrace (prefixWord ++ tailWord_5197173) baseStart_5197173 baseEnd_5197173 := by
    simpa [prefixWord, tailWord_5197173, baseEnd_5197173] using wordTrace_append hprefix tailTrace_5197173
  have hstable : (prefixWord ++ tailWord_5197173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197173).length < 2 ^ (prefixWord ++ tailWord_5197173).sum := by decide
  have hdescent : baseEnd_5197173 < baseStart_5197173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197195 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 6]
def baseStart_5197195 : Nat := 118140960795 + 5197195 * 2 ^ 59
def prefixEnd_5197195 : Nat := 4983230072969 + 3 ^ 40 * 5197195 * 2
def baseEnd_5197195 : Nat := 296517676682655409373449

theorem tailTrace_5197195 : CollatzResearch.WordTrace tailWord_5197195 prefixEnd_5197195 296517676682655409373449 := by
  unfold tailWord_5197195
  simp only [CollatzResearch.WordTrace]
  refine ⟨189557274406457600084849039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126371516270971733389899359 189557274406457600084849039)
  ·
    refine ⟨284335911609686400127273559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189557274406457600084849039 284335911609686400127273559)
    ·
      refine ⟨426503867414529600190910339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284335911609686400127273559 426503867414529600190910339)
      ·
        refine ⟨639755801121794400286365509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426503867414529600190910339 639755801121794400286365509)
        ·
          refine ⟨119954212710336450053693533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 639755801121794400286365509 119954212710336450053693533)
          ·
            refine ⟨44982829766376168770135075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119954212710336450053693533 44982829766376168770135075)
            ·
              refine ⟨67474244649564253155202613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44982829766376168770135075 67474244649564253155202613)
              ·
                refine ⟨6325710435896648733300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67474244649564253155202613 6325710435896648733300245)
                ·
                  refine ⟨296517676682655409373449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6325710435896648733300245 296517676682655409373449)
                  ·
                    rfl

theorem cell23_5197195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 6].length) (baseStart_5197195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197195 prefixEnd_5197195 := by exact prefixLift 5197195
  have htrace : WordTrace (prefixWord ++ tailWord_5197195) baseStart_5197195 baseEnd_5197195 := by
    simpa [prefixWord, tailWord_5197195, baseEnd_5197195] using wordTrace_append hprefix tailTrace_5197195
  have hstable : (prefixWord ++ tailWord_5197195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197195).length < 2 ^ (prefixWord ++ tailWord_5197195).sum := by decide
  have hdescent : baseEnd_5197195 < baseStart_5197195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197209 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_5197209 : Nat := 118140960795 + 5197209 * 2 ^ 59
def prefixEnd_5197209 : Nat := 4983230072969 + 3 ^ 40 * 5197209 * 2
def baseEnd_5197209 : Nat := 2668666278873061629585977

theorem tailTrace_5197209 : CollatzResearch.WordTrace tailWord_5197209 prefixEnd_5197209 2668666278873061629585977 := by
  unfold tailWord_5197209
  simp only [CollatzResearch.WordTrace]
  refine ⟨189557785028406880475858681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126371856685604586983905787 189557785028406880475858681)
  ·
    refine ⟨142168338771305160356894011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189557785028406880475858681 142168338771305160356894011)
    ·
      refine ⟨213252508156957740535341017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142168338771305160356894011 213252508156957740535341017)
      ·
        refine ⟨159939381117718305401505763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213252508156957740535341017 159939381117718305401505763)
        ·
          refine ⟨239909071676577458102258645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159939381117718305401505763 239909071676577458102258645)
          ·
            refine ⟨5622868867419784174271687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239909071676577458102258645 5622868867419784174271687)
            ·
              refine ⟨8434303301129676261407531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622868867419784174271687 8434303301129676261407531)
              ·
                refine ⟨12651454951694514392111297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434303301129676261407531 12651454951694514392111297)
                ·
                  refine ⟨9488591213770885794083473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12651454951694514392111297 9488591213770885794083473)
                  ·
                    refine ⟨7116443410328164345562605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9488591213770885794083473 7116443410328164345562605)
                    ·
                      refine ⟨2668666278873061629585977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116443410328164345562605 2668666278873061629585977)
                      ·
                        rfl

theorem cell23_5197209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_5197209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197209 prefixEnd_5197209 := by exact prefixLift 5197209
  have htrace : WordTrace (prefixWord ++ tailWord_5197209) baseStart_5197209 baseEnd_5197209 := by
    simpa [prefixWord, tailWord_5197209, baseEnd_5197209] using wordTrace_append hprefix tailTrace_5197209
  have hstable : (prefixWord ++ tailWord_5197209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197209).length < 2 ^ (prefixWord ++ tailWord_5197209).sum := by decide
  have hdescent : baseEnd_5197209 < baseStart_5197209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197229 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 6]
def baseStart_5197229 : Nat := 118140960795 + 5197229 * 2 ^ 59
def prefixEnd_5197229 : Nat := 4983230072969 + 3 ^ 40 * 5197229 * 2
def baseEnd_5197229 : Nat := 296519616498461283481765

theorem tailTrace_5197229 : CollatzResearch.WordTrace tailWord_5197229 prefixEnd_5197229 296519616498461283481765 := by
  unfold tailWord_5197229
  simp only [CollatzResearch.WordTrace]
  refine ⟨189558514488334423891586741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126372342992222949261057827 189558514488334423891586741)
  ·
    refine ⟨17771110733281352239836257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189558514488334423891586741 17771110733281352239836257)
    ·
      refine ⟨13328333049961014179877193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17771110733281352239836257 13328333049961014179877193)
      ·
        refine ⟨9996249787470760634907895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13328333049961014179877193 9996249787470760634907895)
        ·
          refine ⟨14994374681206140952361843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996249787470760634907895 14994374681206140952361843)
          ·
            refine ⟨22491562021809211428542765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14994374681206140952361843 22491562021809211428542765)
            ·
              refine ⟨8434335758178454285703537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22491562021809211428542765 8434335758178454285703537)
              ·
                refine ⟨6325751818633840714277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8434335758178454285703537 6325751818633840714277653)
                ·
                  refine ⟨296519616498461283481765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6325751818633840714277653 296519616498461283481765)
                  ·
                    rfl

theorem cell23_5197229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_5197229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197229 prefixEnd_5197229 := by exact prefixLift 5197229
  have htrace : WordTrace (prefixWord ++ tailWord_5197229) baseStart_5197229 baseEnd_5197229 := by
    simpa [prefixWord, tailWord_5197229, baseEnd_5197229] using wordTrace_append hprefix tailTrace_5197229
  have hstable : (prefixWord ++ tailWord_5197229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197229).length < 2 ^ (prefixWord ++ tailWord_5197229).sum := by decide
  have hdescent : baseEnd_5197229 < baseStart_5197229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197239 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_5197239 : Nat := 118140960795 + 5197239 * 2 ^ 59
def prefixEnd_5197239 : Nat := 4983230072969 + 3 ^ 40 * 5197239 * 2
def baseEnd_5197239 : Nat := 2668681683292696512210839

theorem tailTrace_5197239 : CollatzResearch.WordTrace tailWord_5197239 prefixEnd_5197239 2668681683292696512210839 := by
  unfold tailWord_5197239
  simp only [CollatzResearch.WordTrace]
  refine ⟨189558879218298195599450771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126372586145532130399633847 189558879218298195599450771)
  ·
    refine ⟨284338318827447293399176157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189558879218298195599450771 284338318827447293399176157)
    ·
      refine ⟨106626869560292735024691059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284338318827447293399176157 106626869560292735024691059)
      ·
        refine ⟨159940304340439102537036589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106626869560292735024691059 159940304340439102537036589)
        ·
          refine ⟨59977614127664663451388721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159940304340439102537036589 59977614127664663451388721)
          ·
            refine ⟨44983210595748497588541541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59977614127664663451388721 44983210595748497588541541)
            ·
              refine ⟨8434351986702843297851539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44983210595748497588541541 8434351986702843297851539)
              ·
                refine ⟨12651527980054264946777309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434351986702843297851539 12651527980054264946777309)
                ·
                  refine ⟨4744322992520349355041491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12651527980054264946777309 4744322992520349355041491)
                  ·
                    refine ⟨7116484488780524032562237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744322992520349355041491 7116484488780524032562237)
                    ·
                      refine ⟨2668681683292696512210839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116484488780524032562237 2668681683292696512210839)
                      ·
                        rfl

theorem cell23_5197239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_5197239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197239 prefixEnd_5197239 := by exact prefixLift 5197239
  have htrace : WordTrace (prefixWord ++ tailWord_5197239) baseStart_5197239 baseEnd_5197239 := by
    simpa [prefixWord, tailWord_5197239, baseEnd_5197239] using wordTrace_append hprefix tailTrace_5197239
  have hstable : (prefixWord ++ tailWord_5197239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197239).length < 2 ^ (prefixWord ++ tailWord_5197239).sum := by decide
  have hdescent : baseEnd_5197239 < baseStart_5197239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197262 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_5197262 : Nat := 118140960795 + 5197262 * 2 ^ 59
def prefixEnd_5197262 : Nat := 4983230072969 + 3 ^ 40 * 5197262 * 2
def baseEnd_5197262 : Nat := 2668693493347749922223233

theorem tailTrace_5197262 : CollatzResearch.WordTrace tailWord_5197262 prefixEnd_5197262 2668693493347749922223233 := by
  unfold tailWord_5197262
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694964762151858815942255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126373145398143247018358693 23694964762151858815942255)
  ·
    refine ⟨35542447143227788223913383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23694964762151858815942255 35542447143227788223913383)
    ·
      refine ⟨53313670714841682335870075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35542447143227788223913383 53313670714841682335870075)
      ·
        refine ⟨79970506072262523503805113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53313670714841682335870075 79970506072262523503805113)
        ·
          refine ⟨59977879554196892627853835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79970506072262523503805113 59977879554196892627853835)
          ·
            refine ⟨89966819331295338941780753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59977879554196892627853835 89966819331295338941780753)
            ·
              refine ⟨67475114498471504206335565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89966819331295338941780753 67475114498471504206335565)
              ·
                refine ⟨25303167936926814077375837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67475114498471504206335565 25303167936926814077375837)
                ·
                  refine ⟨9488687976347555279015939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25303167936926814077375837 9488687976347555279015939)
                  ·
                    refine ⟨14233031964521332918523909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9488687976347555279015939 14233031964521332918523909)
                    ·
                      refine ⟨2668693493347749922223233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14233031964521332918523909 2668693493347749922223233)
                      ·
                        rfl

theorem cell23_5197262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_5197262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197262 prefixEnd_5197262 := by exact prefixLift 5197262
  have htrace : WordTrace (prefixWord ++ tailWord_5197262) baseStart_5197262 baseEnd_5197262 := by
    simpa [prefixWord, tailWord_5197262, baseEnd_5197262] using wordTrace_append hprefix tailTrace_5197262
  have hstable : (prefixWord ++ tailWord_5197262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197262).length < 2 ^ (prefixWord ++ tailWord_5197262).sum := by decide
  have hdescent : baseEnd_5197262 < baseStart_5197262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197272 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_5197272 : Nat := 118140960795 + 5197272 * 2 ^ 59
def prefixEnd_5197272 : Nat := 4983230072969 + 3 ^ 40 * 5197272 * 2
def baseEnd_5197272 : Nat := 889566209384764961032729

theorem tailTrace_5197272 : CollatzResearch.WordTrace tailWord_5197272 prefixEnd_5197272 889566209384764961032729 := by
  unfold tailWord_5197272
  simp only [CollatzResearch.WordTrace]
  refine ⟨94780041413589321117701035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126373388551452428156934713 94780041413589321117701035)
  ·
    refine ⟨142170062120383981676551553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94780041413589321117701035 142170062120383981676551553)
    ·
      refine ⟨106627546590287986257413665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142170062120383981676551553 106627546590287986257413665)
      ·
        refine ⟨79970659942715989693060249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106627546590287986257413665 79970659942715989693060249)
        ·
          refine ⟨59977994957036992269795187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79970659942715989693060249 59977994957036992269795187)
          ·
            refine ⟨89966992435555488404692781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59977994957036992269795187 89966992435555488404692781)
            ·
              refine ⟨33737622163333308151759793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89966992435555488404692781 33737622163333308151759793)
              ·
                refine ⟨25303216622499981113819845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33737622163333308151759793 25303216622499981113819845)
                ·
                  refine ⟨4744353116718746458841221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25303216622499981113819845 4744353116718746458841221)
                  ·
                    refine ⟨889566209384764961032729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744353116718746458841221 889566209384764961032729)
                    ·
                      rfl

theorem cell23_5197272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_5197272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197272 prefixEnd_5197272 := by exact prefixLift 5197272
  have htrace : WordTrace (prefixWord ++ tailWord_5197272) baseStart_5197272 baseEnd_5197272 := by
    simpa [prefixWord, tailWord_5197272, baseEnd_5197272] using wordTrace_append hprefix tailTrace_5197272
  have hstable : (prefixWord ++ tailWord_5197272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197272).length < 2 ^ (prefixWord ++ tailWord_5197272).sum := by decide
  have hdescent : baseEnd_5197272 < baseStart_5197272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197273 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 1, 1, 3]
def baseStart_5197273 : Nat := 118140960795 + 5197273 * 2 ^ 59
def prefixEnd_5197273 : Nat := 4983230072969 + 3 ^ 40 * 5197273 * 2
def baseEnd_5197273 : Nat := 2668699141634949379185683

theorem tailTrace_5197273 : CollatzResearch.WordTrace tailWord_5197273 prefixEnd_5197273 2668699141634949379185683 := by
  unfold tailWord_5197273
  simp only [CollatzResearch.WordTrace]
  refine ⟨189560119300175019406188473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126373412866783346270792315 189560119300175019406188473)
  ·
    refine ⟨142170089475131264554641355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189560119300175019406188473 142170089475131264554641355)
    ·
      refine ⟨213255134212696896831962033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142170089475131264554641355 213255134212696896831962033)
      ·
        refine ⟨159941350659522672623971525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213255134212696896831962033 159941350659522672623971525)
        ·
          refine ⟨29989003248660501116994661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159941350659522672623971525 29989003248660501116994661)
          ·
            refine ⟨5622938109123843959436499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29989003248660501116994661 5622938109123843959436499)
            ·
              refine ⟨8434407163685765939154749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622938109123843959436499 8434407163685765939154749)
              ·
                refine ⟨3162902686382162227183031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8434407163685765939154749 3162902686382162227183031)
                ·
                  refine ⟨4744354029573243340774547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162902686382162227183031 4744354029573243340774547)
                  ·
                    refine ⟨7116531044359865011161821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744354029573243340774547 7116531044359865011161821)
                    ·
                      refine ⟨2668699141634949379185683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116531044359865011161821 2668699141634949379185683)
                      ·
                        rfl

theorem cell23_5197273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_5197273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197273 prefixEnd_5197273 := by exact prefixLift 5197273
  have htrace : WordTrace (prefixWord ++ tailWord_5197273) baseStart_5197273 baseEnd_5197273 := by
    simpa [prefixWord, tailWord_5197273, baseEnd_5197273] using wordTrace_append hprefix tailTrace_5197273
  have hstable : (prefixWord ++ tailWord_5197273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197273).length < 2 ^ (prefixWord ++ tailWord_5197273).sum := by decide
  have hdescent : baseEnd_5197273 < baseStart_5197273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197290 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_5197290 : Nat := 118140960795 + 5197290 * 2 ^ 59
def prefixEnd_5197290 : Nat := 4983230072969 + 3 ^ 40 * 5197290 * 2
def baseEnd_5197290 : Nat := 2668707870806075812673105

theorem tailTrace_5197290 : CollatzResearch.WordTrace tailWord_5197290 prefixEnd_5197290 2668707870806075812673105 := by
  unfold tailWord_5197290
  simp only [CollatzResearch.WordTrace]
  refine ⟨47390184835278357827389331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126373826227408954206371549 47390184835278357827389331)
  ·
    refine ⟨71085277252917536741083997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47390184835278357827389331 71085277252917536741083997)
    ·
      refine ⟨26656978969844076277906499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71085277252917536741083997 26656978969844076277906499)
      ·
        refine ⟨39985468454766114416859749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26656978969844076277906499 39985468454766114416859749)
        ·
          refine ⟨7497275335268646453161203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39985468454766114416859749 7497275335268646453161203)
          ·
            refine ⟨11245913002902969679741805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497275335268646453161203 11245913002902969679741805)
            ·
              refine ⟨4217217376088613629903177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11245913002902969679741805 4217217376088613629903177)
              ·
                refine ⟨3162913032066460222427383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217217376088613629903177 3162913032066460222427383)
                ·
                  refine ⟨4744369548099690333641075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162913032066460222427383 4744369548099690333641075)
                  ·
                    refine ⟨7116554322149535500461613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744369548099690333641075 7116554322149535500461613)
                    ·
                      refine ⟨2668707870806075812673105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116554322149535500461613 2668707870806075812673105)
                      ·
                        rfl

theorem cell23_5197290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_5197290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197290 prefixEnd_5197290 := by exact prefixLift 5197290
  have htrace : WordTrace (prefixWord ++ tailWord_5197290) baseStart_5197290 baseEnd_5197290 := by
    simpa [prefixWord, tailWord_5197290, baseEnd_5197290] using wordTrace_append hprefix tailTrace_5197290
  have hstable : (prefixWord ++ tailWord_5197290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197290).length < 2 ^ (prefixWord ++ tailWord_5197290).sum := by decide
  have hdescent : baseEnd_5197290 < baseStart_5197290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197296 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2]
def baseStart_5197296 : Nat := 118140960795 + 5197296 * 2 ^ 59
def prefixEnd_5197296 : Nat := 4983230072969 + 3 ^ 40 * 5197296 * 2
def baseEnd_5197296 : Nat := 2668710951690002789198077

theorem tailTrace_5197296 : CollatzResearch.WordTrace tailWord_5197296 prefixEnd_5197296 2668710951690002789198077 := by
  unfold tailWord_5197296
  simp only [CollatzResearch.WordTrace]
  refine ⟨94780479089545847167137871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126373972119394462889517161 94780479089545847167137871)
  ·
    refine ⟨142170718634318770750706807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94780479089545847167137871 142170718634318770750706807)
    ·
      refine ⟨213256077951478156126060211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142170718634318770750706807 213256077951478156126060211)
      ·
        refine ⟨319884116927217234189090317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213256077951478156126060211 319884116927217234189090317)
        ·
          refine ⟨119956543847706462820908869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319884116927217234189090317 119956543847706462820908869)
          ·
            refine ⟨22491851971444961778920413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119956543847706462820908869 22491851971444961778920413)
            ·
              refine ⟨8434444489291860667095155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22491851971444961778920413 8434444489291860667095155)
              ·
                refine ⟨12651666733937791000642733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434444489291860667095155 12651666733937791000642733)
                ·
                  refine ⟨4744375025226671625241025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12651666733937791000642733 4744375025226671625241025)
                  ·
                    refine ⟨3558281268920003718930769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744375025226671625241025 3558281268920003718930769)
                    ·
                      refine ⟨2668710951690002789198077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558281268920003718930769 2668710951690002789198077)
                      ·
                        rfl

theorem cell23_5197296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2].length) (baseStart_5197296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197296 prefixEnd_5197296 := by exact prefixLift 5197296
  have htrace : WordTrace (prefixWord ++ tailWord_5197296) baseStart_5197296 baseEnd_5197296 := by
    simpa [prefixWord, tailWord_5197296, baseEnd_5197296] using wordTrace_append hprefix tailTrace_5197296
  have hstable : (prefixWord ++ tailWord_5197296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197296).length < 2 ^ (prefixWord ++ tailWord_5197296).sum := by decide
  have hdescent : baseEnd_5197296 < baseStart_5197296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197302 : List Nat := [5, 1, 1, 1, 2, 2, 1, 10]
def baseStart_5197302 : Nat := 118140960795 + 5197302 * 2 ^ 59
def prefixEnd_5197302 : Nat := 4983230072969 + 3 ^ 40 * 5197302 * 2
def baseEnd_5197302 : Nat := 98841260465701102434187

theorem tailTrace_5197302 : CollatzResearch.WordTrace tailWord_5197302 prefixEnd_5197302 98841260465701102434187 := by
  unfold tailWord_5197302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847573563566872334937135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126374118011379971572662773 11847573563566872334937135)
  ·
    refine ⟨17771360345350308502405703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11847573563566872334937135 17771360345350308502405703)
    ·
      refine ⟨26657040518025462753608555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17771360345350308502405703 26657040518025462753608555)
      ·
        refine ⟨39985560777038194130412833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26657040518025462753608555 39985560777038194130412833)
        ·
          refine ⟨29989170582778645597809625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39985560777038194130412833 29989170582778645597809625)
          ·
            refine ⟨22491877937083984198357219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29989170582778645597809625 22491877937083984198357219)
            ·
              refine ⟨33737816905625976297535829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22491877937083984198357219 33737816905625976297535829)
              ·
                refine ⟨98841260465701102434187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33737816905625976297535829 98841260465701102434187)
                ·
                  rfl

theorem cell23_5197302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_5197302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197302 prefixEnd_5197302 := by exact prefixLift 5197302
  have htrace : WordTrace (prefixWord ++ tailWord_5197302) baseStart_5197302 baseEnd_5197302 := by
    simpa [prefixWord, tailWord_5197302, baseEnd_5197302] using wordTrace_append hprefix tailTrace_5197302
  have hstable : (prefixWord ++ tailWord_5197302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197302).length < 2 ^ (prefixWord ++ tailWord_5197302).sum := by decide
  have hdescent : baseEnd_5197302 < baseStart_5197302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197305 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5197305 : Nat := 118140960795 + 5197305 * 2 ^ 59
def prefixEnd_5197305 : Nat := 4983230072969 + 3 ^ 40 * 5197305 * 2
def baseEnd_5197305 : Nat := 2668715573015893253985535

theorem tailTrace_5197305 : CollatzResearch.WordTrace tailWord_5197305 prefixEnd_5197305 2668715573015893253985535 := by
  unfold tailWord_5197305
  simp only [CollatzResearch.WordTrace]
  refine ⟨189561286436059088871353369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126374190957372725914235579 189561286436059088871353369)
  ·
    refine ⟨142170964827044316653515027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189561286436059088871353369 142170964827044316653515027)
    ·
      refine ⟨213256447240566474980272541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142170964827044316653515027 213256447240566474980272541)
      ·
        refine ⟨79971167715212428117602203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213256447240566474980272541 79971167715212428117602203)
        ·
          refine ⟨119956751572818642176403305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79971167715212428117602203 119956751572818642176403305)
          ·
            refine ⟨89967563679613981632302479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119956751572818642176403305 89967563679613981632302479)
            ·
              refine ⟨134951345519420972448453719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89967563679613981632302479 134951345519420972448453719)
              ·
                refine ⟨202427018279131458672680579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134951345519420972448453719 202427018279131458672680579)
                ·
                  refine ⟨303640527418697188009020869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202427018279131458672680579 303640527418697188009020869)
                  ·
                    refine ⟨56932598891005722751691413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303640527418697188009020869 56932598891005722751691413)
                    ·
                      refine ⟨2668715573015893253985535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56932598891005722751691413 2668715573015893253985535)
                      ·
                        rfl

theorem cell23_5197305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5197305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197305 prefixEnd_5197305 := by exact prefixLift 5197305
  have htrace : WordTrace (prefixWord ++ tailWord_5197305) baseStart_5197305 baseEnd_5197305 := by
    simpa [prefixWord, tailWord_5197305, baseEnd_5197305] using wordTrace_append hprefix tailTrace_5197305
  have hstable : (prefixWord ++ tailWord_5197305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197305).length < 2 ^ (prefixWord ++ tailWord_5197305).sum := by decide
  have hdescent : baseEnd_5197305 < baseStart_5197305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197310 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5197310 : Nat := 118140960795 + 5197310 * 2 ^ 59
def prefixEnd_5197310 : Nat := 4983230072969 + 3 ^ 40 * 5197310 * 2
def baseEnd_5197310 : Nat := 889572713473055244807671

theorem tailTrace_5197310 : CollatzResearch.WordTrace tailWord_5197310 prefixEnd_5197310 889572713473055244807671 := by
  unfold tailWord_5197310
  simp only [CollatzResearch.WordTrace]
  refine ⟨23695183600130121840660673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126374312534027316483523589 23695183600130121840660673)
  ·
    refine ⟨17771387700097591380495505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23695183600130121840660673 17771387700097591380495505)
    ·
      refine ⟨13328540775073193535371629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17771387700097591380495505 13328540775073193535371629)
      ·
        refine ⟨4998202790652447575764361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13328540775073193535371629 4998202790652447575764361)
        ·
          refine ⟨3748652092989335681823271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4998202790652447575764361 3748652092989335681823271)
          ·
            refine ⟨5622978139484003522734907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748652092989335681823271 5622978139484003522734907)
            ·
              refine ⟨8434467209226005284102361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622978139484003522734907 8434467209226005284102361)
              ·
                refine ⟨6325850406919503963076771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8434467209226005284102361 6325850406919503963076771)
                ·
                  refine ⟨9488775610379255944615157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325850406919503963076771 9488775610379255944615157)
                  ·
                    refine ⟨889572713473055244807671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9488775610379255944615157 889572713473055244807671)
                    ·
                      rfl

theorem cell23_5197310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5197310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197310 prefixEnd_5197310 := by exact prefixLift 5197310
  have htrace : WordTrace (prefixWord ++ tailWord_5197310) baseStart_5197310 baseEnd_5197310 := by
    simpa [prefixWord, tailWord_5197310, baseEnd_5197310] using wordTrace_append hprefix tailTrace_5197310
  have hstable : (prefixWord ++ tailWord_5197310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197310).length < 2 ^ (prefixWord ++ tailWord_5197310).sum := by decide
  have hdescent : baseEnd_5197310 < baseStart_5197310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197313 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_5197313 : Nat := 118140960795 + 5197313 * 2 ^ 59
def prefixEnd_5197313 : Nat := 4983230072969 + 3 ^ 40 * 5197313 * 2
def baseEnd_5197313 : Nat := 2668719680861129222685499

theorem tailTrace_5197313 : CollatzResearch.WordTrace tailWord_5197313 prefixEnd_5197313 2668719680861129222685499 := by
  unfold tailWord_5197313
  simp only [CollatzResearch.WordTrace]
  refine ⟨189561578220030106237644593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126374385480020070825096395 189561578220030106237644593)
  ·
    refine ⟨142171183665022579678233445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189561578220030106237644593 142171183665022579678233445)
    ·
      refine ⟨26657096937191733689668771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142171183665022579678233445 26657096937191733689668771)
      ·
        refine ⟨39985645405787600534503157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26657096937191733689668771 39985645405787600534503157)
        ·
          refine ⟨3748654256792587550109671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39985645405787600534503157 3748654256792587550109671)
          ·
            refine ⟨5622981385188881325164507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748654256792587550109671 5622981385188881325164507)
            ·
              refine ⟨8434472077783321987746761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622981385188881325164507 8434472077783321987746761)
              ·
                refine ⟨6325854058337491490810071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8434472077783321987746761 6325854058337491490810071)
                ·
                  refine ⟨9488781087506237236215107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325854058337491490810071 9488781087506237236215107)
                  ·
                    refine ⟨14233171631259355854322661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9488781087506237236215107 14233171631259355854322661)
                    ·
                      refine ⟨2668719680861129222685499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14233171631259355854322661 2668719680861129222685499)
                      ·
                        rfl

theorem cell23_5197313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_5197313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197313 prefixEnd_5197313 := by exact prefixLift 5197313
  have htrace : WordTrace (prefixWord ++ tailWord_5197313) baseStart_5197313 baseEnd_5197313 := by
    simpa [prefixWord, tailWord_5197313, baseEnd_5197313] using wordTrace_append hprefix tailTrace_5197313
  have hstable : (prefixWord ++ tailWord_5197313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197313).length < 2 ^ (prefixWord ++ tailWord_5197313).sum := by decide
  have hdescent : baseEnd_5197313 < baseStart_5197313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197315 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 7]
def baseStart_5197315 : Nat := 118140960795 + 5197315 * 2 ^ 59
def prefixEnd_5197315 : Nat := 4983230072969 + 3 ^ 40 * 5197315 * 2
def baseEnd_5197315 : Nat := 889573569274146071620163

theorem tailTrace_5197315 : CollatzResearch.WordTrace tailWord_5197315 prefixEnd_5197315 889573569274146071620163 := by
  unfold tailWord_5197315
  simp only [CollatzResearch.WordTrace]
  refine ⟨189561651166022860579217399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126374434110681907052811599 189561651166022860579217399)
  ·
    refine ⟨284342476749034290868826099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189561651166022860579217399 284342476749034290868826099)
    ·
      refine ⟨426513715123551436303239149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284342476749034290868826099 426513715123551436303239149)
      ·
        refine ⟨159942643171331788613714681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426513715123551436303239149 159942643171331788613714681)
        ·
          refine ⟨119956982378498841460286011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159942643171331788613714681 119956982378498841460286011)
          ·
            refine ⟨179935473567748262190429017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119956982378498841460286011 179935473567748262190429017)
            ·
              refine ⟨134951605175811196642821763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179935473567748262190429017 134951605175811196642821763)
              ·
                refine ⟨202427407763716794964232645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134951605175811196642821763 202427407763716794964232645)
                ·
                  refine ⟨37955138955696899055793621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202427407763716794964232645 37955138955696899055793621)
                  ·
                    refine ⟨889573569274146071620163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37955138955696899055793621 889573569274146071620163)
                    ·
                      rfl

theorem cell23_5197315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_5197315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197315 prefixEnd_5197315 := by exact prefixLift 5197315
  have htrace : WordTrace (prefixWord ++ tailWord_5197315) baseStart_5197315 baseEnd_5197315 := by
    simpa [prefixWord, tailWord_5197315, baseEnd_5197315] using wordTrace_append hprefix tailTrace_5197315
  have hstable : (prefixWord ++ tailWord_5197315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197315).length < 2 ^ (prefixWord ++ tailWord_5197315).sum := by decide
  have hdescent : baseEnd_5197315 < baseStart_5197315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197316 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5197316 : Nat := 118140960795 + 5197316 * 2 ^ 59
def prefixEnd_5197316 : Nat := 4983230072969 + 3 ^ 40 * 5197316 * 2
def baseEnd_5197316 : Nat := 2668721221303092710947985

theorem tailTrace_5197316 : CollatzResearch.WordTrace tailWord_5197316 prefixEnd_5197316 2668721221303092710947985 := by
  unfold tailWord_5197316
  simp only [CollatzResearch.WordTrace]
  refine ⟨94780843819509618875001901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126374458426012825166669201 94780843819509618875001901)
  ·
    refine ⟨35542816432316107078125713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94780843819509618875001901 35542816432316107078125713)
    ·
      refine ⟨26657112324237080308594285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35542816432316107078125713 26657112324237080308594285)
      ·
        refine ⟨9996417121588905115722857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26657112324237080308594285 9996417121588905115722857)
        ·
          refine ⟨7497312841191678836792143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996417121588905115722857 7497312841191678836792143)
          ·
            refine ⟨11245969261787518255188215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497312841191678836792143 11245969261787518255188215)
            ·
              refine ⟨16868953892681277382782323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11245969261787518255188215 16868953892681277382782323)
              ·
                refine ⟨25303430839021916074173485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16868953892681277382782323 25303430839021916074173485)
                ·
                  refine ⟨9488786564633218527815057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25303430839021916074173485 9488786564633218527815057)
                  ·
                    refine ⟨7116589923474913895861293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9488786564633218527815057 7116589923474913895861293)
                    ·
                      refine ⟨2668721221303092710947985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116589923474913895861293 2668721221303092710947985)
                      ·
                        rfl

theorem cell23_5197316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5197316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197316 prefixEnd_5197316 := by exact prefixLift 5197316
  have htrace : WordTrace (prefixWord ++ tailWord_5197316) baseStart_5197316 baseEnd_5197316 := by
    simpa [prefixWord, tailWord_5197316, baseEnd_5197316] using wordTrace_append hprefix tailTrace_5197316
  have hstable : (prefixWord ++ tailWord_5197316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197316).length < 2 ^ (prefixWord ++ tailWord_5197316).sum := by decide
  have hdescent : baseEnd_5197316 < baseStart_5197316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197346 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_5197346 : Nat := 118140960795 + 5197346 * 2 ^ 59
def prefixEnd_5197346 : Nat := 4983230072969 + 3 ^ 40 * 5197346 * 2
def baseEnd_5197346 : Nat := 2668736625722727593572847

theorem tailTrace_5197346 : CollatzResearch.WordTrace tailWord_5197346 prefixEnd_5197346 2668736625722727593572847 := by
  unfold tailWord_5197346
  simp only [CollatzResearch.WordTrace]
  refine ⟨47390695457227638218398973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126375187885940368582397261 47390695457227638218398973)
  ·
    refine ⟨17771510796460364331899615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47390695457227638218398973 17771510796460364331899615)
    ·
      refine ⟨26657266194690546497849423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17771510796460364331899615 26657266194690546497849423)
      ·
        refine ⟨39985899292035819746774135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26657266194690546497849423 39985899292035819746774135)
        ·
          refine ⟨59978848938053729620161203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39985899292035819746774135 59978848938053729620161203)
          ·
            refine ⟨89968273407080594430241805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59978848938053729620161203 89968273407080594430241805)
            ·
              refine ⟨33738102527655222911340677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89968273407080594430241805 33738102527655222911340677)
              ·
                refine ⟨6325894223935354295876377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33738102527655222911340677 6325894223935354295876377)
                ·
                  refine ⟨4744420667951515721907283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6325894223935354295876377 4744420667951515721907283)
                  ·
                    refine ⟨7116631001927273582860925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744420667951515721907283 7116631001927273582860925)
                    ·
                      refine ⟨2668736625722727593572847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7116631001927273582860925 2668736625722727593572847)
                      ·
                        rfl

theorem cell23_5197346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_5197346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197346 prefixEnd_5197346 := by exact prefixLift 5197346
  have htrace : WordTrace (prefixWord ++ tailWord_5197346) baseStart_5197346 baseEnd_5197346 := by
    simpa [prefixWord, tailWord_5197346, baseEnd_5197346] using wordTrace_append hprefix tailTrace_5197346
  have hstable : (prefixWord ++ tailWord_5197346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197346).length < 2 ^ (prefixWord ++ tailWord_5197346).sum := by decide
  have hdescent : baseEnd_5197346 < baseStart_5197346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197347 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 1, 2, 2]
def baseStart_5197347 : Nat := 118140960795 + 5197347 * 2 ^ 59
def prefixEnd_5197347 : Nat := 4983230072969 + 3 ^ 40 * 5197347 * 2
def baseEnd_5197347 : Nat := 2668737139203382089660343

theorem tailTrace_5197347 : CollatzResearch.WordTrace tailWord_5197347 prefixEnd_5197347 2668737139203382089660343 := by
  unfold tailWord_5197347
  simp only [CollatzResearch.WordTrace]
  refine ⟨189562818301906930044382295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126375212201271286696254863 189562818301906930044382295)
  ·
    refine ⟨284344227452860395066573443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189562818301906930044382295 284344227452860395066573443)
    ·
      refine ⟨426516341179290592599860165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284344227452860395066573443 426516341179290592599860165)
      ·
        refine ⟨79971813971116986112473781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 426516341179290592599860165 79971813971116986112473781)
        ·
          refine ⟨7497357559792217448044417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79971813971116986112473781 7497357559792217448044417)
          ·
            refine ⟨5623018169844163086033313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7497357559792217448044417 5623018169844163086033313)
            ·
              refine ⟨4217263627383122314524985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5623018169844163086033313 4217263627383122314524985)
              ·
                refine ⟨3162947720537341735893739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217263627383122314524985 3162947720537341735893739)
                ·
                  refine ⟨4744421580806012603840609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162947720537341735893739 4744421580806012603840609)
                  ·
                    refine ⟨3558316185604509452880457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744421580806012603840609 3558316185604509452880457)
                    ·
                      refine ⟨2668737139203382089660343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558316185604509452880457 2668737139203382089660343)
                      ·
                        rfl

theorem cell23_5197347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_5197347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197347 prefixEnd_5197347 := by exact prefixLift 5197347
  have htrace : WordTrace (prefixWord ++ tailWord_5197347) baseStart_5197347 baseEnd_5197347 := by
    simpa [prefixWord, tailWord_5197347, baseEnd_5197347] using wordTrace_append hprefix tailTrace_5197347
  have hstable : (prefixWord ++ tailWord_5197347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197347).length < 2 ^ (prefixWord ++ tailWord_5197347).sum := by decide
  have hdescent : baseEnd_5197347 < baseStart_5197347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197386 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_5197386 : Nat := 118140960795 + 5197386 * 2 ^ 59
def prefixEnd_5197386 : Nat := 4983230072969 + 3 ^ 40 * 5197386 * 2
def baseEnd_5197386 : Nat := 2668757164948907437072663

theorem tailTrace_5197386 : CollatzResearch.WordTrace tailWord_5197386 prefixEnd_5197386 2668757164948907437072663 := by
  unfold tailWord_5197386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391060187191409926263003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126376160499177093136701341 47391060187191409926263003)
  ·
    refine ⟨71086590280787114889394505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47391060187191409926263003 71086590280787114889394505)
    ·
      refine ⟨53314942710590336167045879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71086590280787114889394505 53314942710590336167045879)
      ·
        refine ⟨79972414065885504250568819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53314942710590336167045879 79972414065885504250568819)
        ·
          refine ⟨119958621098828256375853229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79972414065885504250568819 119958621098828256375853229)
          ·
            refine ⟨44984482912060596140944961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119958621098828256375853229 44984482912060596140944961)
            ·
              refine ⟨33738362184045447105708721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44984482912060596140944961 33738362184045447105708721)
              ·
                refine ⟨25303771638034085329281541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33738362184045447105708721 25303771638034085329281541)
                ·
                  refine ⟨4744457182131390999240289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25303771638034085329281541 4744457182131390999240289)
                  ·
                    refine ⟨3558342886598543249430217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744457182131390999240289 3558342886598543249430217)
                    ·
                      refine ⟨2668757164948907437072663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558342886598543249430217 2668757164948907437072663)
                      ·
                        rfl

theorem cell23_5197386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_5197386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197386 prefixEnd_5197386 := by exact prefixLift 5197386
  have htrace : WordTrace (prefixWord ++ tailWord_5197386) baseStart_5197386 baseEnd_5197386 := by
    simpa [prefixWord, tailWord_5197386, baseEnd_5197386] using wordTrace_append hprefix tailTrace_5197386
  have hstable : (prefixWord ++ tailWord_5197386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197386).length < 2 ^ (prefixWord ++ tailWord_5197386).sum := by decide
  have hdescent : baseEnd_5197386 < baseStart_5197386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197409 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 5]
def baseStart_5197409 : Nat := 118140960795 + 5197409 * 2 ^ 59
def prefixEnd_5197409 : Nat := 4983230072969 + 3 ^ 40 * 5197409 * 2
def baseEnd_5197409 : Nat := 296529886111551205231673

theorem tailTrace_5197409 : CollatzResearch.WordTrace tailWord_5197409 prefixEnd_5197409 296529886111551205231673 := by
  unfold tailWord_5197409
  simp only [CollatzResearch.WordTrace]
  refine ⟨189565079627682314633139281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126376719751788209755426187 189565079627682314633139281)
  ·
    refine ⟨142173809720761735974854461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189565079627682314633139281 142173809720761735974854461)
    ·
      refine ⟨53315178645285650990570423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142173809720761735974854461 53315178645285650990570423)
      ·
        refine ⟨79972767967928476485855635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53315178645285650990570423 79972767967928476485855635)
        ·
          refine ⟨119959151951892714728783453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79972767967928476485855635 119959151951892714728783453)
          ·
            refine ⟨44984681981959768023293795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119959151951892714728783453 44984681981959768023293795)
            ·
              refine ⟨67477022972939652034940693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44984681981959768023293795 67477022972939652034940693)
              ·
                refine ⟨3162985451856546189137845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67477022972939652034940693 3162985451856546189137845)
                ·
                  refine ⟨296529886111551205231673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162985451856546189137845 296529886111551205231673)
                  ·
                    rfl

theorem cell23_5197409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 5].length) (baseStart_5197409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197409 prefixEnd_5197409 := by exact prefixLift 5197409
  have htrace : WordTrace (prefixWord ++ tailWord_5197409) baseStart_5197409 baseEnd_5197409 := by
    simpa [prefixWord, tailWord_5197409, baseEnd_5197409] using wordTrace_append hprefix tailTrace_5197409
  have hstable : (prefixWord ++ tailWord_5197409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197409).length < 2 ^ (prefixWord ++ tailWord_5197409).sum := by decide
  have hdescent : baseEnd_5197409 < baseStart_5197409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197460 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 5]
def baseStart_5197460 : Nat := 118140960795 + 5197460 * 2 ^ 59
def prefixEnd_5197460 : Nat := 4983230072969 + 3 ^ 40 * 5197460 * 2
def baseEnd_5197460 : Nat := 296532795835260016394147

theorem tailTrace_5197460 : CollatzResearch.WordTrace tailWord_5197460 prefixEnd_5197460 296532795835260016394147 := by
  unfold tailWord_5197460
  simp only [CollatzResearch.WordTrace]
  refine ⟨94783469875248775171622917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126377959833665033562163889 94783469875248775171622917)
  ·
    refine ⟨17771900601609145344679297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94783469875248775171622917 17771900601609145344679297)
    ·
      refine ⟨13328925451206859008509473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17771900601609145344679297 13328925451206859008509473)
      ·
        refine ⟨9996694088405144256382105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13328925451206859008509473 9996694088405144256382105)
        ·
          refine ⟨7497520566303858192286579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996694088405144256382105 7497520566303858192286579)
          ·
            refine ⟨11246280849455787288429869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497520566303858192286579 11246280849455787288429869)
            ·
              refine ⟨4217355318545920233161201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11246280849455787288429869 4217355318545920233161201)
              ·
                refine ⟨3163016488909440174870901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217355318545920233161201 3163016488909440174870901)
                ·
                  refine ⟨296532795835260016394147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163016488909440174870901 296532795835260016394147)
                  ·
                    rfl

theorem cell23_5197460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_5197460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197460 prefixEnd_5197460 := by exact prefixLift 5197460
  have htrace : WordTrace (prefixWord ++ tailWord_5197460) baseStart_5197460 baseEnd_5197460 := by
    simpa [prefixWord, tailWord_5197460, baseEnd_5197460] using wordTrace_append hprefix tailTrace_5197460
  have hstable : (prefixWord ++ tailWord_5197460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197460).length < 2 ^ (prefixWord ++ tailWord_5197460).sum := by decide
  have hdescent : baseEnd_5197460 < baseStart_5197460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197493 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5197493 : Nat := 118140960795 + 5197493 * 2 ^ 59
def prefixEnd_5197493 : Nat := 4983230072969 + 3 ^ 40 * 5197493 * 2
def baseEnd_5197493 : Nat := 2668812107378938518434671

theorem tailTrace_5197493 : CollatzResearch.WordTrace tailWord_5197493 prefixEnd_5197493 2668812107378938518434671 := by
  unfold tailWord_5197493
  simp only [CollatzResearch.WordTrace]
  refine ⟨189568143359377996979197133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126378762239585331319464755 189568143359377996979197133)
  ·
    refine ⟨71088053759766748867198925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189568143359377996979197133 71088053759766748867198925)
    ·
      refine ⟨26658020159912530825199597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71088053759766748867198925 26658020159912530825199597)
      ·
        refine ⟨9996757559967199059449849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26658020159912530825199597 9996757559967199059449849)
        ·
          refine ⟨7497568169975399294587387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996757559967199059449849 7497568169975399294587387)
          ·
            refine ⟨11246352254963098941881081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497568169975399294587387 11246352254963098941881081)
            ·
              refine ⟨8434764191222324206410811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11246352254963098941881081 8434764191222324206410811)
              ·
                refine ⟨12652146286833486309616217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434764191222324206410811 12652146286833486309616217)
                ·
                  refine ⟨9489109715125114732212163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12652146286833486309616217 9489109715125114732212163)
                  ·
                    refine ⟨14233664572687672098318245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9489109715125114732212163 14233664572687672098318245)
                    ·
                      refine ⟨2668812107378938518434671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14233664572687672098318245 2668812107378938518434671)
                      ·
                        rfl

theorem cell23_5197493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5197493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197493 prefixEnd_5197493 := by exact prefixLift 5197493
  have htrace : WordTrace (prefixWord ++ tailWord_5197493) baseStart_5197493 baseEnd_5197493 := by
    simpa [prefixWord, tailWord_5197493, baseEnd_5197493] using wordTrace_append hprefix tailTrace_5197493
  have hstable : (prefixWord ++ tailWord_5197493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197493).length < 2 ^ (prefixWord ++ tailWord_5197493).sum := by decide
  have hdescent : baseEnd_5197493 < baseStart_5197493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197510 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5197510 : Nat := 118140960795 + 5197510 * 2 ^ 59
def prefixEnd_5197510 : Nat := 4983230072969 + 3 ^ 40 * 5197510 * 2
def baseEnd_5197510 : Nat := 2668820836550064951922093

theorem tailTrace_5197510 : CollatzResearch.WordTrace tailWord_5197510 prefixEnd_5197510 2668820836550064951922093 := by
  unfold tailWord_5197510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5924023856259887777580187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126379175600210939255043989 5924023856259887777580187)
  ·
    refine ⟨8886035784389831666370281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5924023856259887777580187 8886035784389831666370281)
    ·
      refine ⟨6664526838292373749777711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8886035784389831666370281 6664526838292373749777711)
      ·
        refine ⟨9996790257438560624666567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664526838292373749777711 9996790257438560624666567)
        ·
          refine ⟨14995185386157840936999851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996790257438560624666567 14995185386157840936999851)
          ·
            refine ⟨22492778079236761405499777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14995185386157840936999851 22492778079236761405499777)
            ·
              refine ⟨16869583559427571054124833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22492778079236761405499777 16869583559427571054124833)
              ·
                refine ⟨12652187669570678290593625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16869583559427571054124833 12652187669570678290593625)
                ·
                  refine ⟨9489140752178008717945219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12652187669570678290593625 9489140752178008717945219)
                  ·
                    refine ⟨14233711128267013076917829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9489140752178008717945219 14233711128267013076917829)
                    ·
                      refine ⟨2668820836550064951922093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14233711128267013076917829 2668820836550064951922093)
                      ·
                        rfl

theorem cell23_5197510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5197510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197510 prefixEnd_5197510 := by exact prefixLift 5197510
  have htrace : WordTrace (prefixWord ++ tailWord_5197510) baseStart_5197510 baseEnd_5197510 := by
    simpa [prefixWord, tailWord_5197510, baseEnd_5197510] using wordTrace_append hprefix tailTrace_5197510
  have hstable : (prefixWord ++ tailWord_5197510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197510).length < 2 ^ (prefixWord ++ tailWord_5197510).sum := by decide
  have hdescent : baseEnd_5197510 < baseStart_5197510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197529 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_5197529 : Nat := 118140960795 + 5197529 * 2 ^ 59
def prefixEnd_5197529 : Nat := 4983230072969 + 3 ^ 40 * 5197529 * 2
def baseEnd_5197529 : Nat := 889610197560833459194835

theorem tailTrace_5197529 : CollatzResearch.WordTrace tailWord_5197529 prefixEnd_5197529 889610197560833459194835 := by
  unfold tailWord_5197529
  simp only [CollatzResearch.WordTrace]
  refine ⟨189569456387247575127507641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126379637591498383418338427 189569456387247575127507641)
  ·
    refine ⟨142177092290435681345630731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189569456387247575127507641 142177092290435681345630731)
    ·
      refine ⟨213265638435653522018446097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142177092290435681345630731 213265638435653522018446097)
      ·
        refine ⟨159949228826740141513834573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213265638435653522018446097 159949228826740141513834573)
        ·
          refine ⟨59980960810027553067687965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159949228826740141513834573 59980960810027553067687965)
          ·
            refine ⟨22492860303760332400382987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59980960810027553067687965 22492860303760332400382987)
            ·
              refine ⟨33739290455640498600574481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22492860303760332400382987 33739290455640498600574481)
              ·
                refine ⟨25304467841730373950430861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33739290455640498600574481 25304467841730373950430861)
                ·
                  refine ⟨9489175440648890231411573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25304467841730373950430861 9489175440648890231411573)
                  ·
                    refine ⟨889610197560833459194835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9489175440648890231411573 889610197560833459194835)
                    ·
                      rfl

theorem cell23_5197529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_5197529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197529 prefixEnd_5197529 := by exact prefixLift 5197529
  have htrace : WordTrace (prefixWord ++ tailWord_5197529) baseStart_5197529 baseEnd_5197529 := by
    simpa [prefixWord, tailWord_5197529, baseEnd_5197529] using wordTrace_append hprefix tailTrace_5197529
  have hstable : (prefixWord ++ tailWord_5197529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197529).length < 2 ^ (prefixWord ++ tailWord_5197529).sum := by decide
  have hdescent : baseEnd_5197529 < baseStart_5197529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197536 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2]
def baseStart_5197536 : Nat := 118140960795 + 5197536 * 2 ^ 59
def prefixEnd_5197536 : Nat := 4983230072969 + 3 ^ 40 * 5197536 * 2
def baseEnd_5197536 : Nat := 2668834187047081850196973

theorem tailTrace_5197536 : CollatzResearch.WordTrace tailWord_5197536 prefixEnd_5197536 2668834187047081850196973 := by
  unfold tailWord_5197536
  simp only [CollatzResearch.WordTrace]
  refine ⟨94784855849111107661506231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126379807798814810215341641 94784855849111107661506231)
  ·
    refine ⟨142177283773666661492259347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94784855849111107661506231 142177283773666661492259347)
    ·
      refine ⟨213265925660499992238389021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142177283773666661492259347 213265925660499992238389021)
      ·
        refine ⟨79974722122687497089395883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213265925660499992238389021 79974722122687497089395883)
        ·
          refine ⟨119962083184031245634093825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79974722122687497089395883 119962083184031245634093825)
          ·
            refine ⟨89971562388023434225570369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119962083184031245634093825 89971562388023434225570369)
            ·
              refine ⟨67478671791017575669177777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89971562388023434225570369 67478671791017575669177777)
              ·
                refine ⟨50609003843263181751883333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67478671791017575669177777 50609003843263181751883333)
                ·
                  refine ⟨9489188220611846578478125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50609003843263181751883333 9489188220611846578478125)
                  ·
                    refine ⟨3558445582729442466929297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9489188220611846578478125 3558445582729442466929297)
                    ·
                      refine ⟨2668834187047081850196973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558445582729442466929297 2668834187047081850196973)
                      ·
                        rfl

theorem cell23_5197536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_5197536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197536 prefixEnd_5197536 := by exact prefixLift 5197536
  have htrace : WordTrace (prefixWord ++ tailWord_5197536) baseStart_5197536 baseEnd_5197536 := by
    simpa [prefixWord, tailWord_5197536, baseEnd_5197536] using wordTrace_append hprefix tailTrace_5197536
  have hstable : (prefixWord ++ tailWord_5197536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197536).length < 2 ^ (prefixWord ++ tailWord_5197536).sum := by decide
  have hdescent : baseEnd_5197536 < baseStart_5197536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197553 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_5197553 : Nat := 118140960795 + 5197553 * 2 ^ 59
def prefixEnd_5197553 : Nat := 4983230072969 + 3 ^ 40 * 5197553 * 2
def baseEnd_5197553 : Nat := 2668842916218208283684395

theorem tailTrace_5197553 : CollatzResearch.WordTrace tailWord_5197553 prefixEnd_5197553 2668842916218208283684395 := by
  unfold tailWord_5197553
  simp only [CollatzResearch.WordTrace]
  refine ⟨189570331739160627226381313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126380221159440418150920875 189570331739160627226381313)
  ·
    refine ⟨142177748804370470419785985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189570331739160627226381313 142177748804370470419785985)
    ·
      refine ⟨106633311603277852814839489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142177748804370470419785985 106633311603277852814839489)
      ·
        refine ⟨79974983702458389611129617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106633311603277852814839489 79974983702458389611129617)
        ·
          refine ⟨59981237776843792208347213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79974983702458389611129617 59981237776843792208347213)
          ·
            refine ⟨22492964166316422078130205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59981237776843792208347213 22492964166316422078130205)
            ·
              refine ⟨8434861562368658279298827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22492964166316422078130205 8434861562368658279298827)
              ·
                refine ⟨12652292343552987418948241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8434861562368658279298827 12652292343552987418948241)
                ·
                  refine ⟨9489219257664740564211181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12652292343552987418948241 9489219257664740564211181)
                  ·
                    refine ⟨3558457221624277711579193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9489219257664740564211181 3558457221624277711579193)
                    ·
                      refine ⟨2668842916218208283684395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558457221624277711579193 2668842916218208283684395)
                      ·
                        rfl

theorem cell23_5197553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_5197553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197553 prefixEnd_5197553 := by exact prefixLift 5197553
  have htrace : WordTrace (prefixWord ++ tailWord_5197553) baseStart_5197553 baseEnd_5197553 := by
    simpa [prefixWord, tailWord_5197553, baseEnd_5197553] using wordTrace_append hprefix tailTrace_5197553
  have hstable : (prefixWord ++ tailWord_5197553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197553).length < 2 ^ (prefixWord ++ tailWord_5197553).sum := by decide
  have hdescent : baseEnd_5197553 < baseStart_5197553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197559 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 1, 6]
def baseStart_5197559 : Nat := 118140960795 + 5197559 * 2 ^ 59
def prefixEnd_5197559 : Nat := 4983230072969 + 3 ^ 40 * 5197559 * 2
def baseEnd_5197559 : Nat := 889615332367378420069789

theorem tailTrace_5197559 : CollatzResearch.WordTrace tailWord_5197559 prefixEnd_5197559 889615332367378420069789 := by
  unfold tailWord_5197559
  simp only [CollatzResearch.WordTrace]
  refine ⟨189570550577138890251099731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126380367051425926834066487 189570550577138890251099731)
  ·
    refine ⟨284355825865708335376649597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189570550577138890251099731 284355825865708335376649597)
    ·
      refine ⟨106633434699640625766243599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284355825865708335376649597 106633434699640625766243599)
      ·
        refine ⟨159950152049460938649365399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106633434699640625766243599 159950152049460938649365399)
        ·
          refine ⟨239925228074191407974048099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159950152049460938649365399 239925228074191407974048099)
          ·
            refine ⟨359887842111287111961072149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239925228074191407974048099 359887842111287111961072149)
            ·
              refine ⟨16869742598966583373175257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 359887842111287111961072149 16869742598966583373175257)
              ·
                refine ⟨12652306949224937529881443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16869742598966583373175257 12652306949224937529881443)
                ·
                  refine ⟨18978460423837406294822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12652306949224937529881443 18978460423837406294822165)
                  ·
                    refine ⟨889615332367378420069789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18978460423837406294822165 889615332367378420069789)
                    ·
                      rfl

theorem cell23_5197559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_5197559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197559 prefixEnd_5197559 := by exact prefixLift 5197559
  have htrace : WordTrace (prefixWord ++ tailWord_5197559) baseStart_5197559 baseEnd_5197559 := by
    simpa [prefixWord, tailWord_5197559, baseEnd_5197559] using wordTrace_append hprefix tailTrace_5197559
  have hstable : (prefixWord ++ tailWord_5197559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197559).length < 2 ^ (prefixWord ++ tailWord_5197559).sum := by decide
  have hdescent : baseEnd_5197559 < baseStart_5197559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197576 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_5197576 : Nat := 118140960795 + 5197576 * 2 ^ 59
def prefixEnd_5197576 : Nat := 4983230072969 + 3 ^ 40 * 5197576 * 2
def baseEnd_5197576 : Nat := 889618242091087231232263

theorem tailTrace_5197576 : CollatzResearch.WordTrace tailWord_5197576 prefixEnd_5197576 889618242091087231232263 := by
  unfold tailWord_5197576
  simp only [CollatzResearch.WordTrace]
  refine ⟨94785585309038651077234291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126380780412051534769645721 94785585309038651077234291)
  ·
    refine ⟨142178377963557976615851437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94785585309038651077234291 142178377963557976615851437)
    ·
      refine ⟨53316891736334241230944289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142178377963557976615851437 53316891736334241230944289)
      ·
        refine ⟨39987668802250680923208217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53316891736334241230944289 39987668802250680923208217)
        ·
          refine ⟨29990751601688010692406163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39987668802250680923208217 29990751601688010692406163)
          ·
            refine ⟨44986127402532016038609245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29990751601688010692406163 44986127402532016038609245)
            ·
              refine ⟨16869797775949506014478467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44986127402532016038609245 16869797775949506014478467)
              ·
                refine ⟨25304696663924259021717701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16869797775949506014478467 25304696663924259021717701)
                ·
                  refine ⟨4744630624485798566572069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25304696663924259021717701 4744630624485798566572069)
                  ·
                    refine ⟨889618242091087231232263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744630624485798566572069 889618242091087231232263)
                    ·
                      rfl

theorem cell23_5197576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_5197576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197576 prefixEnd_5197576 := by exact prefixLift 5197576
  have htrace : WordTrace (prefixWord ++ tailWord_5197576) baseStart_5197576 baseEnd_5197576 := by
    simpa [prefixWord, tailWord_5197576, baseEnd_5197576] using wordTrace_append hprefix tailTrace_5197576
  have hstable : (prefixWord ++ tailWord_5197576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197576).length < 2 ^ (prefixWord ++ tailWord_5197576).sum := by decide
  have hdescent : baseEnd_5197576 < baseStart_5197576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197579 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_5197579 : Nat := 118140960795 + 5197579 * 2 ^ 59
def prefixEnd_5197579 : Nat := 4983230072969 + 3 ^ 40 * 5197579 * 2
def baseEnd_5197579 : Nat := 2668856266715225181959275

theorem tailTrace_5197579 : CollatzResearch.WordTrace tailWord_5197579 prefixEnd_5197579 2668856266715225181959275 := by
  unfold tailWord_5197579
  simp only [CollatzResearch.WordTrace]
  refine ⟨189571280037066433666827791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126380853358044289111218527 189571280037066433666827791)
  ·
    refine ⟨284356920055599650500241687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189571280037066433666827791 284356920055599650500241687)
    ·
      refine ⟨426535380083399475750362531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284356920055599650500241687 426535380083399475750362531)
      ·
        refine ⟨639803070125099213625543797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426535380083399475750362531 639803070125099213625543797)
        ·
          refine ⟨59981537824228051277394731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 639803070125099213625543797 59981537824228051277394731)
          ·
            refine ⟨89972306736342076916092097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59981537824228051277394731 89972306736342076916092097)
            ·
              refine ⟨67479230052256557687069073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89972306736342076916092097 67479230052256557687069073)
              ·
                refine ⟨50609422539192418265301805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67479230052256557687069073 50609422539192418265301805)
                ·
                  refine ⟨18978533452197156849488177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50609422539192418265301805 18978533452197156849488177)
                  ·
                    refine ⟨14233900089147867637116133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18978533452197156849488177 14233900089147867637116133)
                    ·
                      refine ⟨2668856266715225181959275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14233900089147867637116133 2668856266715225181959275)
                      ·
                        rfl

theorem cell23_5197579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_5197579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197579 prefixEnd_5197579 := by exact prefixLift 5197579
  have htrace : WordTrace (prefixWord ++ tailWord_5197579) baseStart_5197579 baseEnd_5197579 := by
    simpa [prefixWord, tailWord_5197579, baseEnd_5197579] using wordTrace_append hprefix tailTrace_5197579
  have hstable : (prefixWord ++ tailWord_5197579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197579).length < 2 ^ (prefixWord ++ tailWord_5197579).sum := by decide
  have hdescent : baseEnd_5197579 < baseStart_5197579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197617 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 1, 2, 2]
def baseStart_5197617 : Nat := 118140960795 + 5197617 * 2 ^ 59
def prefixEnd_5197617 : Nat := 4983230072969 + 3 ^ 40 * 5197617 * 2
def baseEnd_5197617 : Nat := 2668875778980096033284101

theorem tailTrace_5197617 : CollatzResearch.WordTrace tailWord_5197617 prefixEnd_5197617 2668875778980096033284101 := by
  unfold tailWord_5197617
  simp only [CollatzResearch.WordTrace]
  refine ⟨189572666010928766156711105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126381777340619177437807403 189572666010928766156711105)
  ·
    refine ⟨142179499508196574617533329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189572666010928766156711105 142179499508196574617533329)
    ·
      refine ⟨106634624631147430963149997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142179499508196574617533329 106634624631147430963149997)
      ·
        refine ⟨39987984236680286611181249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106634624631147430963149997 39987984236680286611181249)
        ·
          refine ⟨29990988177510214958385937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39987984236680286611181249 29990988177510214958385937)
          ·
            refine ⟨22493241133132661218789453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29990988177510214958385937 22493241133132661218789453)
            ·
              refine ⟨8434965424924747957046045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22493241133132661218789453 8434965424924747957046045)
              ·
                refine ⟨3163112034346780483892267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8434965424924747957046045 3163112034346780483892267)
                ·
                  refine ⟨4744668051520170725838401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163112034346780483892267 4744668051520170725838401)
                  ·
                    refine ⟨3558501038640128044378801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744668051520170725838401 3558501038640128044378801)
                    ·
                      refine ⟨2668875778980096033284101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558501038640128044378801 2668875778980096033284101)
                      ·
                        rfl

theorem cell23_5197617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_5197617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197617 prefixEnd_5197617 := by exact prefixLift 5197617
  have htrace : WordTrace (prefixWord ++ tailWord_5197617) baseStart_5197617 baseEnd_5197617 := by
    simpa [prefixWord, tailWord_5197617, baseEnd_5197617] using wordTrace_append hprefix tailTrace_5197617
  have hstable : (prefixWord ++ tailWord_5197617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197617).length < 2 ^ (prefixWord ++ tailWord_5197617).sum := by decide
  have hdescent : baseEnd_5197617 < baseStart_5197617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197620 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5197620 : Nat := 118140960795 + 5197620 * 2 ^ 59
def prefixEnd_5197620 : Nat := 4983230072969 + 3 ^ 40 * 5197620 * 2
def baseEnd_5197620 : Nat := 2668877319422059521546587

theorem tailTrace_5197620 : CollatzResearch.WordTrace tailWord_5197620 prefixEnd_5197620 2668877319422059521546587 := by
  unfold tailWord_5197620
  simp only [CollatzResearch.WordTrace]
  refine ⟨94786387714958948834535157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126381850286611931779380209 94786387714958948834535157)
  ·
    refine ⟨8886223848277401453237671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94786387714958948834535157 8886223848277401453237671)
    ·
      refine ⟨13329335772416102179856507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886223848277401453237671 13329335772416102179856507)
      ·
        refine ⟨19994003658624153269784761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13329335772416102179856507 19994003658624153269784761)
        ·
          refine ⟨14995502743968114952338571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19994003658624153269784761 14995502743968114952338571)
          ·
            refine ⟨22493254115952172428507857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14995502743968114952338571 22493254115952172428507857)
            ·
              refine ⟨16869940586964129321380893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22493254115952172428507857 16869940586964129321380893)
              ·
                refine ⟨6326227720111548495517835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16869940586964129321380893 6326227720111548495517835)
                ·
                  refine ⟨9489341580167322743276753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6326227720111548495517835 9489341580167322743276753)
                  ·
                    refine ⟨7117006185125492057457565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9489341580167322743276753 7117006185125492057457565)
                    ·
                      refine ⟨2668877319422059521546587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7117006185125492057457565 2668877319422059521546587)
                      ·
                        rfl

theorem cell23_5197620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5197620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197620 prefixEnd_5197620 := by exact prefixLift 5197620
  have htrace : WordTrace (prefixWord ++ tailWord_5197620) baseStart_5197620 baseEnd_5197620 := by
    simpa [prefixWord, tailWord_5197620, baseEnd_5197620] using wordTrace_append hprefix tailTrace_5197620
  have hstable : (prefixWord ++ tailWord_5197620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197620).length < 2 ^ (prefixWord ++ tailWord_5197620).sum := by decide
  have hdescent : baseEnd_5197620 < baseStart_5197620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197650 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_5197650 : Nat := 118140960795 + 5197650 * 2 ^ 59
def prefixEnd_5197650 : Nat := 4983230072969 + 3 ^ 40 * 5197650 * 2
def baseEnd_5197650 : Nat := 2668892723841694404171449

theorem tailTrace_5197650 : CollatzResearch.WordTrace tailWord_5197650 prefixEnd_5197650 2668892723841694404171449 := by
  unfold tailWord_5197650
  simp only [CollatzResearch.WordTrace]
  refine ⟨47393467404952303198165601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126382579746539475195108269 47393467404952303198165601)
  ·
    refine ⟨35545100553714227398624201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47393467404952303198165601 35545100553714227398624201)
    ·
      refine ⟨26658825415285670548968151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35545100553714227398624201 26658825415285670548968151)
      ·
        refine ⟨39988238122928505823452227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26658825415285670548968151 39988238122928505823452227)
        ·
          refine ⟨59982357184392758735178341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39988238122928505823452227 59982357184392758735178341)
          ·
            refine ⟨11246691972073642262845939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59982357184392758735178341 11246691972073642262845939)
            ·
              refine ⟨16870037958110463394268909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11246691972073642262845939 16870037958110463394268909)
              ·
                refine ⟨6326264234291423772850841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16870037958110463394268909 6326264234291423772850841)
                ·
                  refine ⟨4744698175718567829638131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6326264234291423772850841 4744698175718567829638131)
                  ·
                    refine ⟨7117047263577851744457197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4744698175718567829638131 7117047263577851744457197)
                    ·
                      refine ⟨2668892723841694404171449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7117047263577851744457197 2668892723841694404171449)
                      ·
                        rfl

theorem cell23_5197650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_5197650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197650 prefixEnd_5197650 := by exact prefixLift 5197650
  have htrace : WordTrace (prefixWord ++ tailWord_5197650) baseStart_5197650 baseEnd_5197650 := by
    simpa [prefixWord, tailWord_5197650, baseEnd_5197650] using wordTrace_append hprefix tailTrace_5197650
  have hstable : (prefixWord ++ tailWord_5197650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197650).length < 2 ^ (prefixWord ++ tailWord_5197650).sum := by decide
  have hdescent : baseEnd_5197650 < baseStart_5197650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197673 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 6, 2, 2]
def baseStart_5197673 : Nat := 118140960795 + 5197673 * 2 ^ 59
def prefixEnd_5197673 : Nat := 4983230072969 + 3 ^ 40 * 5197673 * 2
def baseEnd_5197673 : Nat := 2668904533896747814183843

theorem tailTrace_5197673 : CollatzResearch.WordTrace tailWord_5197673 prefixEnd_5197673 2668904533896747814183843 := by
  unfold tailWord_5197673
  simp only [CollatzResearch.WordTrace]
  refine ⟨189574708498725887720749673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126383138999150591813833115 189574708498725887720749673)
  ·
    refine ⟨142181031374044415790562255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189574708498725887720749673 142181031374044415790562255)
    ·
      refine ⟨213271547061066623685843383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142181031374044415790562255 213271547061066623685843383)
      ·
        refine ⟨319907320591599935528765075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213271547061066623685843383 319907320591599935528765075)
        ·
          refine ⟨479860980887399903293147613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319907320591599935528765075 479860980887399903293147613)
          ·
            refine ⟨179947867832774963734930355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 479860980887399903293147613 179947867832774963734930355)
            ·
              refine ⟨269921801749162445602395533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179947867832774963734930355 269921801749162445602395533)
              ·
                refine ⟨101220675655935917100898325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269921801749162445602395533 101220675655935917100898325)
                ·
                  refine ⟨4744719171371996114104609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101220675655935917100898325 4744719171371996114104609)
                  ·
                    refine ⟨3558539378528997085578457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744719171371996114104609 3558539378528997085578457)
                    ·
                      refine ⟨2668904533896747814183843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558539378528997085578457 2668904533896747814183843)
                      ·
                        rfl

theorem cell23_5197673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2, 2].length) (baseStart_5197673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197673 prefixEnd_5197673 := by exact prefixLift 5197673
  have htrace : WordTrace (prefixWord ++ tailWord_5197673) baseStart_5197673 baseEnd_5197673 := by
    simpa [prefixWord, tailWord_5197673, baseEnd_5197673] using wordTrace_append hprefix tailTrace_5197673
  have hstable : (prefixWord ++ tailWord_5197673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197673).length < 2 ^ (prefixWord ++ tailWord_5197673).sum := by decide
  have hdescent : baseEnd_5197673 < baseStart_5197673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197676 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_5197676 : Nat := 118140960795 + 5197676 * 2 ^ 59
def prefixEnd_5197676 : Nat := 4983230072969 + 3 ^ 40 * 5197676 * 2
def baseEnd_5197676 : Nat := 2668906074338711302446329

theorem tailTrace_5197676 : CollatzResearch.WordTrace tailWord_5197676 prefixEnd_5197676 2668906074338711302446329 := by
  unfold tailWord_5197676
  simp only [CollatzResearch.WordTrace]
  refine ⟨94787408958857509616554441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126383211945143346155405921 94787408958857509616554441)
  ·
    refine ⟨71090556719143132212415831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94787408958857509616554441 71090556719143132212415831)
    ·
      refine ⟨106635835078714698318623747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71090556719143132212415831 106635835078714698318623747)
      ·
        refine ⟨159953752618072047477935621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106635835078714698318623747 159953752618072047477935621)
        ·
          refine ⟨29991328615888508902112929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159953752618072047477935621 29991328615888508902112929)
          ·
            refine ⟨22493496461916381676584697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29991328615888508902112929 22493496461916381676584697)
            ·
              refine ⟨16870122346437286257438523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22493496461916381676584697 16870122346437286257438523)
              ·
                refine ⟨25305183519655929386157785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16870122346437286257438523 25305183519655929386157785)
                ·
                  refine ⟨18978887639741947039618339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25305183519655929386157785 18978887639741947039618339)
                  ·
                    refine ⟨28468331459612920559427509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18978887639741947039618339 28468331459612920559427509)
                    ·
                      refine ⟨2668906074338711302446329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28468331459612920559427509 2668906074338711302446329)
                      ·
                        rfl

theorem cell23_5197676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_5197676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197676 prefixEnd_5197676 := by exact prefixLift 5197676
  have htrace : WordTrace (prefixWord ++ tailWord_5197676) baseStart_5197676 baseEnd_5197676 := by
    simpa [prefixWord, tailWord_5197676, baseEnd_5197676] using wordTrace_append hprefix tailTrace_5197676
  have hstable : (prefixWord ++ tailWord_5197676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197676).length < 2 ^ (prefixWord ++ tailWord_5197676).sum := by decide
  have hdescent : baseEnd_5197676 < baseStart_5197676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197690 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_5197690 : Nat := 118140960795 + 5197690 * 2 ^ 59
def prefixEnd_5197690 : Nat := 4983230072969 + 3 ^ 40 * 5197690 * 2
def baseEnd_5197690 : Nat := 2668913263067874247671265

theorem tailTrace_5197690 : CollatzResearch.WordTrace tailWord_5197690 prefixEnd_5197690 2668913263067874247671265 := by
  unfold tailWord_5197690
  simp only [CollatzResearch.WordTrace]
  refine ⟨47393832134916074906029631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126383552359776199749412349 47393832134916074906029631)
  ·
    refine ⟨71090748202374112359044447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47393832134916074906029631 71090748202374112359044447)
    ·
      refine ⟨106636122303561168538566671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71090748202374112359044447 106636122303561168538566671)
      ·
        refine ⟨159954183455341752807850007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106636122303561168538566671 159954183455341752807850007)
        ·
          refine ⟨239931275183012629211775011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159954183455341752807850007 239931275183012629211775011)
          ·
            refine ⟨359896912774518943817662517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239931275183012629211775011 359896912774518943817662517)
            ·
              refine ⟨33740335572611150982905861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 359896912774518943817662517 33740335572611150982905861)
              ·
                refine ⟨6326312919864590809294849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33740335572611150982905861 6326312919864590809294849)
                ·
                  refine ⟨4744734689898443106971137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6326312919864590809294849 4744734689898443106971137)
                  ·
                    refine ⟨3558551017423832330228353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4744734689898443106971137 3558551017423832330228353)
                    ·
                      refine ⟨2668913263067874247671265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558551017423832330228353 2668913263067874247671265)
                      ·
                        rfl

theorem cell23_5197690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_5197690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197690 prefixEnd_5197690 := by exact prefixLift 5197690
  have htrace : WordTrace (prefixWord ++ tailWord_5197690) baseStart_5197690 baseEnd_5197690 := by
    simpa [prefixWord, tailWord_5197690, baseEnd_5197690] using wordTrace_append hprefix tailTrace_5197690
  have hstable : (prefixWord ++ tailWord_5197690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197690).length < 2 ^ (prefixWord ++ tailWord_5197690).sum := by decide
  have hdescent : baseEnd_5197690 < baseStart_5197690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197703 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_5197703 : Nat := 118140960795 + 5197703 * 2 ^ 59
def prefixEnd_5197703 : Nat := 4983230072969 + 3 ^ 40 * 5197703 * 2
def baseEnd_5197703 : Nat := 2668919938316382696808705

theorem tailTrace_5197703 : CollatzResearch.WordTrace tailWord_5197703 prefixEnd_5197703 2668919938316382696808705 := by
  unfold tailWord_5197703
  simp only [CollatzResearch.WordTrace]
  refine ⟨189575802688617202844341763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126383868459078135229561175 189575802688617202844341763)
  ·
    refine ⟨284363704032925804266512645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189575802688617202844341763 284363704032925804266512645)
    ·
      refine ⟨53318194506173588299971121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284363704032925804266512645 53318194506173588299971121)
      ·
        refine ⟨39988645879630191224978341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53318194506173588299971121 39988645879630191224978341)
        ·
          refine ⟨7497871102430660854683439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39988645879630191224978341 7497871102430660854683439)
          ·
            refine ⟨11246806653645991282025159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497871102430660854683439 11246806653645991282025159)
            ·
              refine ⟨16870209980468986923037739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11246806653645991282025159 16870209980468986923037739)
              ·
                refine ⟨25305314970703480384556609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16870209980468986923037739 25305314970703480384556609)
                ·
                  refine ⟨18978986228027610288417457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25305314970703480384556609 18978986228027610288417457)
                  ·
                    refine ⟨14234239671020707716313093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18978986228027610288417457 14234239671020707716313093)
                    ·
                      refine ⟨2668919938316382696808705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14234239671020707716313093 2668919938316382696808705)
                      ·
                        rfl

theorem cell23_5197703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_5197703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197703 prefixEnd_5197703 := by exact prefixLift 5197703
  have htrace : WordTrace (prefixWord ++ tailWord_5197703) baseStart_5197703 baseEnd_5197703 := by
    simpa [prefixWord, tailWord_5197703, baseEnd_5197703] using wordTrace_append hprefix tailTrace_5197703
  have hstable : (prefixWord ++ tailWord_5197703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197703).length < 2 ^ (prefixWord ++ tailWord_5197703).sum := by decide
  have hdescent : baseEnd_5197703 < baseStart_5197703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197783 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_5197783 : Nat := 118140960795 + 5197783 * 2 ^ 59
def prefixEnd_5197783 : Nat := 4983230072969 + 3 ^ 40 * 5197783 * 2
def baseEnd_5197783 : Nat := 2668961016768742383808337

theorem tailTrace_5197783 : CollatzResearch.WordTrace tailWord_5197783 prefixEnd_5197783 2668961016768742383808337 := by
  unfold tailWord_5197783
  simp only [CollatzResearch.WordTrace]
  refine ⟨189578720528327376507254003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126385813685551584338169335 189578720528327376507254003)
  ·
    refine ⟨284368080792491064760881005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189578720528327376507254003 284368080792491064760881005)
    ·
      refine ⟨106638030297184149285330377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284368080792491064760881005 106638030297184149285330377)
      ·
        refine ⟨79978522722888111963997783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106638030297184149285330377 79978522722888111963997783)
        ·
          refine ⟨119967784084332167945996675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79978522722888111963997783 119967784084332167945996675)
          ·
            refine ⟨179951676126498251918995013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119967784084332167945996675 179951676126498251918995013)
            ·
              refine ⟨33740939273718422234811565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179951676126498251918995013 33740939273718422234811565)
              ·
                refine ⟨12652852227644408338054337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33740939273718422234811565 12652852227644408338054337)
                ·
                  refine ⟨9489639170733306253540753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12652852227644408338054337 9489639170733306253540753)
                  ·
                    refine ⟨7117229378049979690155565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9489639170733306253540753 7117229378049979690155565)
                    ·
                      refine ⟨2668961016768742383808337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7117229378049979690155565 2668961016768742383808337)
                      ·
                        rfl

theorem cell23_5197783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_5197783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197783 prefixEnd_5197783 := by exact prefixLift 5197783
  have htrace : WordTrace (prefixWord ++ tailWord_5197783) baseStart_5197783 baseEnd_5197783 := by
    simpa [prefixWord, tailWord_5197783, baseEnd_5197783] using wordTrace_append hprefix tailTrace_5197783
  have hstable : (prefixWord ++ tailWord_5197783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197783).length < 2 ^ (prefixWord ++ tailWord_5197783).sum := by decide
  have hdescent : baseEnd_5197783 < baseStart_5197783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197807 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 1, 4]
def baseStart_5197807 : Nat := 118140960795 + 5197807 * 2 ^ 59
def prefixEnd_5197807 : Nat := 4983230072969 + 3 ^ 40 * 5197807 * 2
def baseEnd_5197807 : Nat := 889657780101483429969409

theorem tailTrace_5197807 : CollatzResearch.WordTrace tailWord_5197807 prefixEnd_5197807 889657780101483429969409 := by
  unfold tailWord_5197807
  simp only [CollatzResearch.WordTrace]
  refine ⟨189579595880240428606127675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126386397253493619070751783 189579595880240428606127675)
  ·
    refine ⟨284369393820360642909191513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189579595880240428606127675 284369393820360642909191513)
    ·
      refine ⟨213277045365270482181893635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284369393820360642909191513 213277045365270482181893635)
      ·
        refine ⟨319915568047905723272840453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213277045365270482181893635 319915568047905723272840453)
        ·
          refine ⟨59984169008982323113657585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319915568047905723272840453 59984169008982323113657585)
          ·
            refine ⟨44988126756736742335243189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59984169008982323113657585 44988126756736742335243189)
            ·
              refine ⟨4217636883444069593929049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44988126756736742335243189 4217636883444069593929049)
              ·
                refine ⟨3163227662583052195446787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217636883444069593929049 3163227662583052195446787)
                ·
                  refine ⟨4744841493874578293170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163227662583052195446787 4744841493874578293170181)
                  ·
                    refine ⟨889657780101483429969409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4744841493874578293170181 889657780101483429969409)
                    ·
                      rfl

theorem cell23_5197807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 4].length) (baseStart_5197807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197807 prefixEnd_5197807 := by exact prefixLift 5197807
  have htrace : WordTrace (prefixWord ++ tailWord_5197807) baseStart_5197807 baseEnd_5197807 := by
    simpa [prefixWord, tailWord_5197807, baseEnd_5197807] using wordTrace_append hprefix tailTrace_5197807
  have hstable : (prefixWord ++ tailWord_5197807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197807).length < 2 ^ (prefixWord ++ tailWord_5197807).sum := by decide
  have hdescent : baseEnd_5197807 < baseStart_5197807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197823 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 5, 2]
def baseStart_5197823 : Nat := 118140960795 + 5197823 * 2 ^ 59
def prefixEnd_5197823 : Nat := 4983230072969 + 3 ^ 40 * 5197823 * 2
def baseEnd_5197823 : Nat := 2668981555994922227308153

theorem tailTrace_5197823 : CollatzResearch.WordTrace tailWord_5197823 prefixEnd_5197823 2668981555994922227308153 := by
  unfold tailWord_5197823
  simp only [CollatzResearch.WordTrace]
  refine ⟨189580179448182463338710123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126386786298788308892473415 189580179448182463338710123)
  ·
    refine ⟨284370269172273695008065185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189580179448182463338710123 284370269172273695008065185)
    ·
      refine ⟨213277701879205271256048889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284370269172273695008065185 213277701879205271256048889)
      ·
        refine ⟨159958276409403953442036667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213277701879205271256048889 159958276409403953442036667)
        ·
          refine ⟨239937414614105930163055001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159958276409403953442036667 239937414614105930163055001)
          ·
            refine ⟨179953060960579447622291251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239937414614105930163055001 179953060960579447622291251)
            ·
              refine ⟨269929591440869171433436877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179953060960579447622291251 269929591440869171433436877)
              ·
                refine ⟨101223596790325939287538829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269929591440869171433436877 101223596790325939287538829)
                ·
                  refine ⟨37958848796372227232827061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101223596790325939287538829 37958848796372227232827061)
                  ·
                    refine ⟨3558642074659896303077537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37958848796372227232827061 3558642074659896303077537)
                    ·
                      refine ⟨2668981555994922227308153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558642074659896303077537 2668981555994922227308153)
                      ·
                        rfl

theorem cell23_5197823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_5197823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197823 prefixEnd_5197823 := by exact prefixLift 5197823
  have htrace : WordTrace (prefixWord ++ tailWord_5197823) baseStart_5197823 baseEnd_5197823 := by
    simpa [prefixWord, tailWord_5197823, baseEnd_5197823] using wordTrace_append hprefix tailTrace_5197823
  have hstable : (prefixWord ++ tailWord_5197823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197823).length < 2 ^ (prefixWord ++ tailWord_5197823).sum := by decide
  have hdescent : baseEnd_5197823 < baseStart_5197823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197870 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5197870 : Nat := 118140960795 + 5197870 * 2 ^ 59
def prefixEnd_5197870 : Nat := 4983230072969 + 3 ^ 40 * 5197870 * 2
def baseEnd_5197870 : Nat := 2669005689585683543420437

theorem tailTrace_5197870 : CollatzResearch.WordTrace tailWord_5197870 prefixEnd_5197870 2669005689585683543420437 := by
  unfold tailWord_5197870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697736709876523795708883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126387929119341460243780709 23697736709876523795708883)
  ·
    refine ⟨35546605064814785693563325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23697736709876523795708883 35546605064814785693563325)
    ·
      refine ⟨13329976899305544635086247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35546605064814785693563325 13329976899305544635086247)
      ·
        refine ⟨19994965348958316952629371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13329976899305544635086247 19994965348958316952629371)
        ·
          refine ⟨29992448023437475428944057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19994965348958316952629371 29992448023437475428944057)
          ·
            refine ⟨22494336017578106571708043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29992448023437475428944057 22494336017578106571708043)
            ·
              refine ⟨33741504026367159857562065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22494336017578106571708043 33741504026367159857562065)
              ·
                refine ⟨25306128019775369893171549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33741504026367159857562065 25306128019775369893171549)
                ·
                  refine ⟨9489798007415763709939331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25306128019775369893171549 9489798007415763709939331)
                  ·
                    refine ⟨14234697011123645564908997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9489798007415763709939331 14234697011123645564908997)
                    ·
                      refine ⟨2669005689585683543420437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14234697011123645564908997 2669005689585683543420437)
                      ·
                        rfl

theorem cell23_5197870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5197870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197870 prefixEnd_5197870 := by exact prefixLift 5197870
  have htrace : WordTrace (prefixWord ++ tailWord_5197870) baseStart_5197870 baseEnd_5197870 := by
    simpa [prefixWord, tailWord_5197870, baseEnd_5197870] using wordTrace_append hprefix tailTrace_5197870
  have hstable : (prefixWord ++ tailWord_5197870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197870).length < 2 ^ (prefixWord ++ tailWord_5197870).sum := by decide
  have hdescent : baseEnd_5197870 < baseStart_5197870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197880 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_5197880 : Nat := 118140960795 + 5197880 * 2 ^ 59
def prefixEnd_5197880 : Nat := 4983230072969 + 3 ^ 40 * 5197880 * 2
def baseEnd_5197880 : Nat := 889670274797409501431797

theorem tailTrace_5197880 : CollatzResearch.WordTrace tailWord_5197880 prefixEnd_5197880 889670274797409501431797 := by
  unfold tailWord_5197880
  simp only [CollatzResearch.WordTrace]
  refine ⟨94791129204487981036767547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126388172272650641382356729 94791129204487981036767547)
  ·
    refine ⟨142186693806731971555151321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94791129204487981036767547 142186693806731971555151321)
    ·
      refine ⟨106640020355048978666363491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142186693806731971555151321 106640020355048978666363491)
      ·
        refine ⟨159960030532573467999545237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106640020355048978666363491 159960030532573467999545237)
        ·
          refine ⟨7498126431214381312478683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159960030532573467999545237 7498126431214381312478683)
          ·
            refine ⟨11247189646821571968718025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7498126431214381312478683 11247189646821571968718025)
            ·
              refine ⟨8435392235116178976538519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11247189646821571968718025 8435392235116178976538519)
              ·
                refine ⟨12653088352674268464807779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8435392235116178976538519 12653088352674268464807779)
                ·
                  refine ⟨18979632529011402697211669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12653088352674268464807779 18979632529011402697211669)
                  ·
                    refine ⟨889670274797409501431797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18979632529011402697211669 889670274797409501431797)
                    ·
                      rfl

theorem cell23_5197880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_5197880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197880 prefixEnd_5197880 := by exact prefixLift 5197880
  have htrace : WordTrace (prefixWord ++ tailWord_5197880) baseStart_5197880 baseEnd_5197880 := by
    simpa [prefixWord, tailWord_5197880, baseEnd_5197880] using wordTrace_append hprefix tailTrace_5197880
  have hstable : (prefixWord ++ tailWord_5197880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197880).length < 2 ^ (prefixWord ++ tailWord_5197880).sum := by decide
  have hdescent : baseEnd_5197880 < baseStart_5197880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197963 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3]
def baseStart_5197963 : Nat := 118140960795 + 5197963 * 2 ^ 59
def prefixEnd_5197963 : Nat := 4983230072969 + 3 ^ 40 * 5197963 * 2
def baseEnd_5197963 : Nat := 2669053443286551679557509

theorem tailTrace_5197963 : CollatzResearch.WordTrace tailWord_5197963 prefixEnd_5197963 2669053443286551679557509 := by
  unfold tailWord_5197963
  simp only [CollatzResearch.WordTrace]
  refine ⟨189585285667675267248806543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126390190445116844832537695 189585285667675267248806543)
  ·
    refine ⟨284377928501512900873209815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189585285667675267248806543 284377928501512900873209815)
    ·
      refine ⟨426566892752269351309814723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284377928501512900873209815 426566892752269351309814723)
      ·
        refine ⟨639850339128404026964722085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426566892752269351309814723 639850339128404026964722085)
        ·
          refine ⟨119971938586575755055885391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 639850339128404026964722085 119971938586575755055885391)
          ·
            refine ⟨179957907879863632583828087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119971938586575755055885391 179957907879863632583828087)
            ·
              refine ⟨269936861819795448875742131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179957907879863632583828087 269936861819795448875742131)
              ·
                refine ⟨404905292729693173313613197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269936861819795448875742131 404905292729693173313613197)
                ·
                  refine ⟨151839484773634939992604949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404905292729693173313613197 151839484773634939992604949)
                  ·
                    refine ⟨7117475848764137812153357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 151839484773634939992604949 7117475848764137812153357)
                    ·
                      refine ⟨2669053443286551679557509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7117475848764137812153357 2669053443286551679557509)
                      ·
                        rfl

theorem cell23_5197963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3].length) (baseStart_5197963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197963 prefixEnd_5197963 := by exact prefixLift 5197963
  have htrace : WordTrace (prefixWord ++ tailWord_5197963) baseStart_5197963 baseEnd_5197963 := by
    simpa [prefixWord, tailWord_5197963, baseEnd_5197963] using wordTrace_append hprefix tailTrace_5197963
  have hstable : (prefixWord ++ tailWord_5197963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197963).length < 2 ^ (prefixWord ++ tailWord_5197963).sum := by decide
  have hdescent : baseEnd_5197963 < baseStart_5197963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197980 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5197980 : Nat := 118140960795 + 5197980 * 2 ^ 59
def prefixEnd_5197980 : Nat := 4983230072969 + 3 ^ 40 * 5197980 * 2
def baseEnd_5197980 : Nat := 2669062172457678113044931

theorem tailTrace_5197980 : CollatzResearch.WordTrace tailWord_5197980 prefixEnd_5197980 2669062172457678113044931 := by
  unfold tailWord_5197980
  simp only [CollatzResearch.WordTrace]
  refine ⟨94792952854306839576087697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126390603805742452768116929 94792952854306839576087697)
  ·
    refine ⟨71094714640730129682065773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94792952854306839576087697 71094714640730129682065773)
    ·
      refine ⟨26660517990273798630774665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71094714640730129682065773 26660517990273798630774665)
      ·
        refine ⟨19995388492705348973080999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26660517990273798630774665 19995388492705348973080999)
        ·
          refine ⟨29993082739058023459621499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19995388492705348973080999 29993082739058023459621499)
          ·
            refine ⟨44989624108587035189432249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29993082739058023459621499 44989624108587035189432249)
            ·
              refine ⟨33742218081440276392074187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44989624108587035189432249 33742218081440276392074187)
              ·
                refine ⟨50613327122160414588111281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33742218081440276392074187 50613327122160414588111281)
                ·
                  refine ⟨37959995341620310941083461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50613327122160414588111281 37959995341620310941083461)
                  ·
                    refine ⟨7117499126553808301453149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37959995341620310941083461 7117499126553808301453149)
                    ·
                      refine ⟨2669062172457678113044931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7117499126553808301453149 2669062172457678113044931)
                      ·
                        rfl

theorem cell23_5197980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5197980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197980 prefixEnd_5197980 := by exact prefixLift 5197980
  have htrace : WordTrace (prefixWord ++ tailWord_5197980) baseStart_5197980 baseEnd_5197980 := by
    simpa [prefixWord, tailWord_5197980, baseEnd_5197980] using wordTrace_append hprefix tailTrace_5197980
  have hstable : (prefixWord ++ tailWord_5197980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197980).length < 2 ^ (prefixWord ++ tailWord_5197980).sum := by decide
  have hdescent : baseEnd_5197980 < baseStart_5197980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5197988 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_5197988 : Nat := 118140960795 + 5197988 * 2 ^ 59
def prefixEnd_5197988 : Nat := 4983230072969 + 3 ^ 40 * 5197988 * 2
def baseEnd_5197988 : Nat := 2669066280302914081744895

theorem tailTrace_5197988 : CollatzResearch.WordTrace tailWord_5197988 prefixEnd_5197988 2669066280302914081744895 := by
  unfold tailWord_5197988
  simp only [CollatzResearch.WordTrace]
  refine ⟨94793098746292348259233309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126390798328389797678977745 94793098746292348259233309)
  ·
    refine ⟨35547412029859630597212491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94793098746292348259233309 35547412029859630597212491)
    ·
      refine ⟨53321118044789445895818737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35547412029859630597212491 53321118044789445895818737)
      ·
        refine ⟨39990838533592084421864053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53321118044789445895818737 39990838533592084421864053)
        ·
          refine ⟨3749141112524257914549755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39990838533592084421864053 3749141112524257914549755)
          ·
            refine ⟨5623711668786386871824633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749141112524257914549755 5623711668786386871824633)
            ·
              refine ⟨4217783751589790153868475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5623711668786386871824633 4217783751589790153868475)
              ·
                refine ⟨6326675627384685230802713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217783751589790153868475 6326675627384685230802713)
                ·
                  refine ⟨4745006720538513923102035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6326675627384685230802713 4745006720538513923102035)
                  ·
                    refine ⟨7117510080807770884653053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4745006720538513923102035 7117510080807770884653053)
                    ·
                      refine ⟨2669066280302914081744895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7117510080807770884653053 2669066280302914081744895)
                      ·
                        rfl

theorem cell23_5197988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_5197988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5197988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5197988 prefixEnd_5197988 := by exact prefixLift 5197988
  have htrace : WordTrace (prefixWord ++ tailWord_5197988) baseStart_5197988 baseEnd_5197988 := by
    simpa [prefixWord, tailWord_5197988, baseEnd_5197988] using wordTrace_append hprefix tailTrace_5197988
  have hstable : (prefixWord ++ tailWord_5197988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5197988).length < 2 ^ (prefixWord ++ tailWord_5197988).sum := by decide
  have hdescent : baseEnd_5197988 < baseStart_5197988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5197988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198028 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5198028 : Nat := 118140960795 + 5198028 * 2 ^ 59
def prefixEnd_5198028 : Nat := 4983230072969 + 3 ^ 40 * 5198028 * 2
def baseEnd_5198028 : Nat := 2669086819529093925244711

theorem tailTrace_5198028 : CollatzResearch.WordTrace tailWord_5198028 prefixEnd_5198028 2669086819529093925244711 := by
  unfold tailWord_5198028
  simp only [CollatzResearch.WordTrace]
  refine ⟨94793828206219891674961369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126391770941626522233281825 94793828206219891674961369)
  ·
    refine ⟨71095371154664918756221027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94793828206219891674961369 71095371154664918756221027)
    ·
      refine ⟨106643056731997378134331541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71095371154664918756221027 106643056731997378134331541)
      ·
        refine ⟨4998893284312377100046791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106643056731997378134331541 4998893284312377100046791)
        ·
          refine ⟨7498339926468565650070187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998893284312377100046791 7498339926468565650070187)
          ·
            refine ⟨11247509889702848475105281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7498339926468565650070187 11247509889702848475105281)
            ·
              refine ⟨8435632417277136356328961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11247509889702848475105281 8435632417277136356328961)
              ·
                refine ⟨6326724312957852267246721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8435632417277136356328961 6326724312957852267246721)
                ·
                  refine ⟨4745043234718389200435041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6326724312957852267246721 4745043234718389200435041)
                  ·
                    refine ⟨3558782426038791900326281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4745043234718389200435041 3558782426038791900326281)
                    ·
                      refine ⟨2669086819529093925244711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558782426038791900326281 2669086819529093925244711)
                      ·
                        rfl

theorem cell23_5198028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5198028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198028 prefixEnd_5198028 := by exact prefixLift 5198028
  have htrace : WordTrace (prefixWord ++ tailWord_5198028) baseStart_5198028 baseEnd_5198028 := by
    simpa [prefixWord, tailWord_5198028, baseEnd_5198028] using wordTrace_append hprefix tailTrace_5198028
  have hstable : (prefixWord ++ tailWord_5198028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198028).length < 2 ^ (prefixWord ++ tailWord_5198028).sum := by decide
  have hdescent : baseEnd_5198028 < baseStart_5198028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198034 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_5198034 : Nat := 118140960795 + 5198034 * 2 ^ 59
def prefixEnd_5198034 : Nat := 4983230072969 + 3 ^ 40 * 5198034 * 2
def baseEnd_5198034 : Nat := 296565544490335655752187

theorem tailTrace_5198034 : CollatzResearch.WordTrace tailWord_5198034 prefixEnd_5198034 296565544490335655752187 := by
  unfold tailWord_5198034
  simp only [CollatzResearch.WordTrace]
  refine ⟨47396968812604511593660289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126391916833612030916427437 47396968812604511593660289)
  ·
    refine ⟨35547726609453383695245217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47396968812604511593660289 35547726609453383695245217)
    ·
      refine ⟨26660794957090037771433913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35547726609453383695245217 26660794957090037771433913)
      ·
        refine ⟨19995596217817528328575435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26660794957090037771433913 19995596217817528328575435)
        ·
          refine ⟨29993394326726292492863153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19995596217817528328575435 29993394326726292492863153)
          ·
            refine ⟨22495045745044719369647365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29993394326726292492863153 22495045745044719369647365)
            ·
              refine ⟨4217821077195884881808881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22495045745044719369647365 4217821077195884881808881)
              ·
                refine ⟨3163365807896913661356661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217821077195884881808881 3163365807896913661356661)
                ·
                  refine ⟨296565544490335655752187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163365807896913661356661 296565544490335655752187)
                  ·
                    rfl

theorem cell23_5198034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_5198034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198034 prefixEnd_5198034 := by exact prefixLift 5198034
  have htrace : WordTrace (prefixWord ++ tailWord_5198034) baseStart_5198034 baseEnd_5198034 := by
    simpa [prefixWord, tailWord_5198034, baseEnd_5198034] using wordTrace_append hprefix tailTrace_5198034
  have hstable : (prefixWord ++ tailWord_5198034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198034).length < 2 ^ (prefixWord ++ tailWord_5198034).sum := by decide
  have hdescent : baseEnd_5198034 < baseStart_5198034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198040 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_5198040 : Nat := 118140960795 + 5198040 * 2 ^ 59
def prefixEnd_5198040 : Nat := 4983230072969 + 3 ^ 40 * 5198040 * 2
def baseEnd_5198040 : Nat := 2669092981296947878294655

theorem tailTrace_5198040 : CollatzResearch.WordTrace tailWord_5198040 prefixEnd_5198040 2669092981296947878294655 := by
  unfold tailWord_5198040
  simp only [CollatzResearch.WordTrace]
  refine ⟨94794047044198154699679787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126392062725597539599573049 94794047044198154699679787)
  ·
    refine ⟨142191070566297232049519681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94794047044198154699679787 142191070566297232049519681)
    ·
      refine ⟨106643302924722924037139761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142191070566297232049519681 106643302924722924037139761)
      ·
        refine ⟨79982477193542193027854821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106643302924722924037139761 79982477193542193027854821)
        ·
          refine ⟨14996714473789161192722779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79982477193542193027854821 14996714473789161192722779)
          ·
            refine ⟨22495071710683741789084169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14996714473789161192722779 22495071710683741789084169)
            ·
              refine ⟨16871303783012806341813127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22495071710683741789084169 16871303783012806341813127)
              ·
                refine ⟨25306955674519209512719691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16871303783012806341813127 25306955674519209512719691)
                ·
                  refine ⟨37960433511778814269079537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25306955674519209512719691 37960433511778814269079537)
                  ·
                    refine ⟨28470325133834110701809653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37960433511778814269079537 28470325133834110701809653)
                    ·
                      refine ⟨2669092981296947878294655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28470325133834110701809653 2669092981296947878294655)
                      ·
                        rfl

theorem cell23_5198040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_5198040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198040 prefixEnd_5198040 := by exact prefixLift 5198040
  have htrace : WordTrace (prefixWord ++ tailWord_5198040) baseStart_5198040 baseEnd_5198040 := by
    simpa [prefixWord, tailWord_5198040, baseEnd_5198040] using wordTrace_append hprefix tailTrace_5198040
  have hstable : (prefixWord ++ tailWord_5198040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198040).length < 2 ^ (prefixWord ++ tailWord_5198040).sum := by decide
  have hdescent : baseEnd_5198040 < baseStart_5198040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198094 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_5198094 : Nat := 118140960795 + 5198094 * 2 ^ 59
def prefixEnd_5198094 : Nat := 4983230072969 + 3 ^ 40 * 5198094 * 2
def baseEnd_5198094 : Nat := 889706903084096889006469

theorem tailTrace_5198094 : CollatzResearch.WordTrace tailWord_5198094 prefixEnd_5198094 889706903084096889006469 := by
  unfold tailWord_5198094
  simp only [CollatzResearch.WordTrace]
  refine ⟨23698757953775084577728167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126393375753467117747883557 23698757953775084577728167)
  ·
    refine ⟨35548136930662626866592251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23698757953775084577728167 35548136930662626866592251)
    ·
      refine ⟨53322205395993940299888377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35548136930662626866592251 53322205395993940299888377)
      ·
        refine ⟨39991654046995455224916283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53322205395993940299888377 39991654046995455224916283)
        ·
          refine ⟨59987481070493182837374425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39991654046995455224916283 59987481070493182837374425)
          ·
            refine ⟨44990610802869887128030819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59987481070493182837374425 44990610802869887128030819)
            ·
              refine ⟨67485916204304830692046229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44990610802869887128030819 67485916204304830692046229)
              ·
                refine ⟨3163402322076788938689667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67485916204304830692046229 3163402322076788938689667)
                ·
                  refine ⟨4745103483115183408034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163402322076788938689667 4745103483115183408034501)
                  ·
                    refine ⟨889706903084096889006469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4745103483115183408034501 889706903084096889006469)
                    ·
                      rfl

theorem cell23_5198094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_5198094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198094 prefixEnd_5198094 := by exact prefixLift 5198094
  have htrace : WordTrace (prefixWord ++ tailWord_5198094) baseStart_5198094 baseEnd_5198094 := by
    simpa [prefixWord, tailWord_5198094, baseEnd_5198094] using wordTrace_append hprefix tailTrace_5198094
  have hstable : (prefixWord ++ tailWord_5198094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198094).length < 2 ^ (prefixWord ++ tailWord_5198094).sum := by decide
  have hdescent : baseEnd_5198094 < baseStart_5198094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198127 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 5, 2]
def baseStart_5198127 : Nat := 118140960795 + 5198127 * 2 ^ 59
def prefixEnd_5198127 : Nat := 4983230072969 + 3 ^ 40 * 5198127 * 2
def baseEnd_5198127 : Nat := 2669137654113889037906755

theorem tailTrace_5198127 : CollatzResearch.WordTrace tailWord_5198127 prefixEnd_5198127 2669137654113889037906755 := by
  unfold tailWord_5198127
  simp only [CollatzResearch.WordTrace]
  refine ⟨189591267239081123257776635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126394178159387415505184423 189591267239081123257776635)
  ·
    refine ⟨284386900858621684886664953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189591267239081123257776635 284386900858621684886664953)
    ·
      refine ⟨213290175643966263664998715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284386900858621684886664953 213290175643966263664998715)
      ·
        refine ⟨319935263465949395497498073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213290175643966263664998715 319935263465949395497498073)
        ·
          refine ⟨239951447599462046623123555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319935263465949395497498073 239951447599462046623123555)
          ·
            refine ⟨359927171399193069934685333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239951447599462046623123555 359927171399193069934685333)
            ·
              refine ⟨16871586159337175153188375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 359927171399193069934685333 16871586159337175153188375)
              ·
                refine ⟨25307379239005762729782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16871586159337175153188375 25307379239005762729782563)
                ·
                  refine ⟨37961068858508644094673845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25307379239005762729782563 37961068858508644094673845)
                  ·
                    refine ⟨3558850205485185383875673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37961068858508644094673845 3558850205485185383875673)
                    ·
                      refine ⟨2669137654113889037906755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558850205485185383875673 2669137654113889037906755)
                      ·
                        rfl

theorem cell23_5198127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5, 2].length) (baseStart_5198127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198127 prefixEnd_5198127 := by exact prefixLift 5198127
  have htrace : WordTrace (prefixWord ++ tailWord_5198127) baseStart_5198127 baseEnd_5198127 := by
    simpa [prefixWord, tailWord_5198127, baseEnd_5198127] using wordTrace_append hprefix tailTrace_5198127
  have hstable : (prefixWord ++ tailWord_5198127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198127).length < 2 ^ (prefixWord ++ tailWord_5198127).sum := by decide
  have hdescent : baseEnd_5198127 < baseStart_5198127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198180 : List Nat := [2, 3, 1, 1, 3, 1, 1, 11]
def baseStart_5198180 : Nat := 118140960795 + 5198180 * 2 ^ 59
def prefixEnd_5198180 : Nat := 4983230072969 + 3 ^ 40 * 5198180 * 2
def baseEnd_5198180 : Nat := 98857958095873234464593

theorem tailTrace_5198180 : CollatzResearch.WordTrace tailWord_5198180 prefixEnd_5198180 98857958095873234464593 := by
  unfold tailWord_5198180
  simp only [CollatzResearch.WordTrace]
  refine ⟨94796600153944556654727997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126395466871926075539637329 94796600153944556654727997)
  ·
    refine ⟨35548725057729208745522999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94796600153944556654727997 35548725057729208745522999)
    ·
      refine ⟨53323087586593813118284499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35548725057729208745522999 53323087586593813118284499)
      ·
        refine ⟨79984631379890719677426749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53323087586593813118284499 79984631379890719677426749)
        ·
          refine ⟨29994236767459019879035031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79984631379890719677426749 29994236767459019879035031)
          ·
            refine ⟨44991355151188529818552547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29994236767459019879035031 44991355151188529818552547)
            ·
              refine ⟨67487032726782794727828821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44991355151188529818552547 67487032726782794727828821)
              ·
                refine ⟨98857958095873234464593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67487032726782794727828821 98857958095873234464593)
                ·
                  rfl

theorem cell23_5198180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 11].length) (baseStart_5198180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198180 prefixEnd_5198180 := by exact prefixLift 5198180
  have htrace : WordTrace (prefixWord ++ tailWord_5198180) baseStart_5198180 baseEnd_5198180 := by
    simpa [prefixWord, tailWord_5198180, baseEnd_5198180] using wordTrace_append hprefix tailTrace_5198180
  have hstable : (prefixWord ++ tailWord_5198180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198180).length < 2 ^ (prefixWord ++ tailWord_5198180).sum := by decide
  have hdescent : baseEnd_5198180 < baseStart_5198180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198194 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5198194 : Nat := 118140960795 + 5198194 * 2 ^ 59
def prefixEnd_5198194 : Nat := 4983230072969 + 3 ^ 40 * 5198194 * 2
def baseEnd_5198194 : Nat := 2669172057317740275768947

theorem tailTrace_5198194 : CollatzResearch.WordTrace tailWord_5198194 prefixEnd_5198194 2669172057317740275768947 := by
  unfold tailWord_5198194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47398427732459598425116409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126395807286558929133643757 47398427732459598425116409)
  ·
    refine ⟨35548820799344698818837307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47398427732459598425116409 35548820799344698818837307)
    ·
      refine ⟨53323231199017048228255961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35548820799344698818837307 53323231199017048228255961)
      ·
        refine ⟨39992423399262786171191971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53323231199017048228255961 39992423399262786171191971)
        ·
          refine ⟨59988635098894179256787957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39992423399262786171191971 59988635098894179256787957)
          ·
            refine ⟨5623934540521329305323871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59988635098894179256787957 5623934540521329305323871)
            ·
              refine ⟨8435901810781993957985807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5623934540521329305323871 8435901810781993957985807)
              ·
                refine ⟨12653852716172990936978711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8435901810781993957985807 12653852716172990936978711)
                ·
                  refine ⟨18980779074259486405468067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12653852716172990936978711 18980779074259486405468067)
                  ·
                    refine ⟨28471168611389229608202101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18980779074259486405468067 28471168611389229608202101)
                    ·
                      refine ⟨2669172057317740275768947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28471168611389229608202101 2669172057317740275768947)
                      ·
                        rfl

theorem cell23_5198194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5198194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198194 prefixEnd_5198194 := by exact prefixLift 5198194
  have htrace : WordTrace (prefixWord ++ tailWord_5198194) baseStart_5198194 baseEnd_5198194 := by
    simpa [prefixWord, tailWord_5198194, baseEnd_5198194] using wordTrace_append hprefix tailTrace_5198194
  have hstable : (prefixWord ++ tailWord_5198194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198194).length < 2 ^ (prefixWord ++ tailWord_5198194).sum := by decide
  have hdescent : baseEnd_5198194 < baseStart_5198194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198257 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_5198257 : Nat := 118140960795 + 5198257 * 2 ^ 59
def prefixEnd_5198257 : Nat := 4983230072969 + 3 ^ 40 * 5198257 * 2
def baseEnd_5198257 : Nat := 889734802199657843093719

theorem tailTrace_5198257 : CollatzResearch.WordTrace tailWord_5198257 prefixEnd_5198257 889734802199657843093719 := by
  unfold tailWord_5198257
  simp only [CollatzResearch.WordTrace]
  refine ⟨189596008728610155460009025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126397339152406770306672683 189596008728610155460009025)
  ·
    refine ⟨142197006546457616595006769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189596008728610155460009025 142197006546457616595006769)
    ·
      refine ⟨106647754909843212446255077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142197006546457616595006769 106647754909843212446255077)
      ·
        refine ⟨19996454045595602333672827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106647754909843212446255077 19996454045595602333672827)
        ·
          refine ⟨29994681068393403500509241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996454045595602333672827 29994681068393403500509241)
          ·
            refine ⟨22496010801295052625381931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29994681068393403500509241 22496010801295052625381931)
            ·
              refine ⟨33744016201942578938072897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22496010801295052625381931 33744016201942578938072897)
              ·
                refine ⟨25308012151456934203554673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33744016201942578938072897 25308012151456934203554673)
                ·
                  refine ⟨18981009113592700652666005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25308012151456934203554673 18981009113592700652666005)
                  ·
                    refine ⟨889734802199657843093719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18981009113592700652666005 889734802199657843093719)
                    ·
                      rfl

theorem cell23_5198257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_5198257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198257 prefixEnd_5198257 := by exact prefixLift 5198257
  have htrace : WordTrace (prefixWord ++ tailWord_5198257) baseStart_5198257 baseEnd_5198257 := by
    simpa [prefixWord, tailWord_5198257, baseEnd_5198257] using wordTrace_append hprefix tailTrace_5198257
  have hstable : (prefixWord ++ tailWord_5198257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198257).length < 2 ^ (prefixWord ++ tailWord_5198257).sum := by decide
  have hdescent : baseEnd_5198257 < baseStart_5198257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198281 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 2, 2, 2]
def baseStart_5198281 : Nat := 118140960795 + 5198281 * 2 ^ 59
def prefixEnd_5198281 : Nat := 4983230072969 + 3 ^ 40 * 5198281 * 2
def baseEnd_5198281 : Nat := 2669216730134681435381047

theorem tailTrace_5198281 : CollatzResearch.WordTrace tailWord_5198281 prefixEnd_5198281 2669216730134681435381047 := by
  unfold tailWord_5198281
  simp only [CollatzResearch.WordTrace]
  refine ⟨189596884080523207558882697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126397922720348805039255131 189596884080523207558882697)
  ·
    refine ⟨142197663060392405669162023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189596884080523207558882697 142197663060392405669162023)
    ·
      refine ⟨213296494590588608503743035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142197663060392405669162023 213296494590588608503743035)
      ·
        refine ⟨319944741885882912755614553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213296494590588608503743035 319944741885882912755614553)
        ·
          refine ⟨239958556414412184566710915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319944741885882912755614553 239958556414412184566710915)
          ·
            refine ⟨359937834621618276850066373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239958556414412184566710915 359937834621618276850066373)
            ·
              refine ⟨67488343991553426909387445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 359937834621618276850066373 67488343991553426909387445)
              ·
                refine ⟨6327032249208133772755073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67488343991553426909387445 6327032249208133772755073)
                ·
                  refine ⟨4745274186906100329566305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327032249208133772755073 4745274186906100329566305)
                  ·
                    refine ⟨3558955640179575247174729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4745274186906100329566305 3558955640179575247174729)
                    ·
                      refine ⟨2669216730134681435381047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3558955640179575247174729 2669216730134681435381047)
                      ·
                        rfl

theorem cell23_5198281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2, 2].length) (baseStart_5198281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198281 prefixEnd_5198281 := by exact prefixLift 5198281
  have htrace : WordTrace (prefixWord ++ tailWord_5198281) baseStart_5198281 baseEnd_5198281 := by
    simpa [prefixWord, tailWord_5198281, baseEnd_5198281] using wordTrace_append hprefix tailTrace_5198281
  have hstable : (prefixWord ++ tailWord_5198281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198281).length < 2 ^ (prefixWord ++ tailWord_5198281).sum := by decide
  have hdescent : baseEnd_5198281 < baseStart_5198281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198321 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 5]
def baseStart_5198321 : Nat := 118140960795 + 5198321 * 2 ^ 59
def prefixEnd_5198321 : Nat := 4983230072969 + 3 ^ 40 * 5198321 * 2
def baseEnd_5198321 : Nat := 296581918817873475431207

theorem tailTrace_5198321 : CollatzResearch.WordTrace tailWord_5198321 prefixEnd_5198321 296581918817873475431207 := by
  unfold tailWord_5198321
  simp only [CollatzResearch.WordTrace]
  refine ⟨189598343000378294390338817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126398895333585529593559211 189598343000378294390338817)
  ·
    refine ⟨142198757250283720792754113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189598343000378294390338817 142198757250283720792754113)
    ·
      refine ⟨106649067937712790594565585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142198757250283720792754113 106649067937712790594565585)
      ·
        refine ⟨79986800953284592945924189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106649067937712790594565585 79986800953284592945924189)
        ·
          refine ⟨29995050357481722354721571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79986800953284592945924189 29995050357481722354721571)
          ·
            refine ⟨44992575536222583532082357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29995050357481722354721571 44992575536222583532082357)
            ·
              refine ⟨4218053956520867206132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44992575536222583532082357 4218053956520867206132721)
              ·
                refine ⟨3163540467390650404599541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4218053956520867206132721 3163540467390650404599541)
                ·
                  refine ⟨296581918817873475431207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163540467390650404599541 296581918817873475431207)
                  ·
                    rfl

theorem cell23_5198321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 5].length) (baseStart_5198321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198321 prefixEnd_5198321 := by exact prefixLift 5198321
  have htrace : WordTrace (prefixWord ++ tailWord_5198321) baseStart_5198321 baseEnd_5198321 := by
    simpa [prefixWord, tailWord_5198321, baseEnd_5198321] using wordTrace_append hprefix tailTrace_5198321
  have hstable : (prefixWord ++ tailWord_5198321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198321).length < 2 ^ (prefixWord ++ tailWord_5198321).sum := by decide
  have hdescent : baseEnd_5198321 < baseStart_5198321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198367 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5198367 : Nat := 118140960795 + 5198367 * 2 ^ 59
def prefixEnd_5198367 : Nat := 4983230072969 + 3 ^ 40 * 5198367 * 2
def baseEnd_5198367 : Nat := 2669260889470968098905651

theorem tailTrace_5198367 : CollatzResearch.WordTrace tailWord_5198367 prefixEnd_5198367 2669260889470968098905651 := by
  unfold tailWord_5198367
  simp only [CollatzResearch.WordTrace]
  refine ⟨189600020758211644246513355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126400013838807762831008903 189600020758211644246513355)
  ·
    refine ⟨284400031137317466369770033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189600020758211644246513355 284400031137317466369770033)
    ·
      refine ⟨213300023352988099777327525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284400031137317466369770033 213300023352988099777327525)
      ·
        refine ⟨39993754378685268708248911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213300023352988099777327525 39993754378685268708248911)
        ·
          refine ⟨59990631568027903062373367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39993754378685268708248911 59990631568027903062373367)
          ·
            refine ⟨89985947352041854593560051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59990631568027903062373367 89985947352041854593560051)
            ·
              refine ⟨134978921028062781890340077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89985947352041854593560051 134978921028062781890340077)
              ·
                refine ⟨50617095385523543208877529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134978921028062781890340077 50617095385523543208877529)
                ·
                  refine ⟨37962821539142657406658147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50617095385523543208877529 37962821539142657406658147)
                  ·
                    refine ⟨56944232308713986109987221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37962821539142657406658147 56944232308713986109987221)
                    ·
                      refine ⟨2669260889470968098905651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56944232308713986109987221 2669260889470968098905651)
                      ·
                        rfl

theorem cell23_5198367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5198367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198367 prefixEnd_5198367 := by exact prefixLift 5198367
  have htrace : WordTrace (prefixWord ++ tailWord_5198367) baseStart_5198367 baseEnd_5198367 := by
    simpa [prefixWord, tailWord_5198367, baseEnd_5198367] using wordTrace_append hprefix tailTrace_5198367
  have hstable : (prefixWord ++ tailWord_5198367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198367).length < 2 ^ (prefixWord ++ tailWord_5198367).sum := by decide
  have hdescent : baseEnd_5198367 < baseStart_5198367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198372 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 5]
def baseStart_5198372 : Nat := 118140960795 + 5198372 * 2 ^ 59
def prefixEnd_5198372 : Nat := 4983230072969 + 3 ^ 40 * 5198372 * 2
def baseEnd_5198372 : Nat := 296584828541582286593681

theorem tailTrace_5198372 : CollatzResearch.WordTrace tailWord_5198372 prefixEnd_5198372 296584828541582286593681 := by
  unfold tailWord_5198372
  simp only [CollatzResearch.WordTrace]
  refine ⟨94800101561596765050222685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126400135415462353400296913 94800101561596765050222685)
  ·
    refine ⟨35550038085598786893833507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94800101561596765050222685 35550038085598786893833507)
    ·
      refine ⟨53325057128398180340750261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35550038085598786893833507 53325057128398180340750261)
      ·
        refine ⟨4999224105787329406945337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53325057128398180340750261 4999224105787329406945337)
        ·
          refine ⟨3749418079340497055209003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4999224105787329406945337 3749418079340497055209003)
          ·
            refine ⟨5624127119010745582813505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749418079340497055209003 5624127119010745582813505)
            ·
              refine ⟨4218095339258059187110129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5624127119010745582813505 4218095339258059187110129)
              ·
                refine ⟨3163571504443544390332597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4218095339258059187110129 3163571504443544390332597)
                ·
                  refine ⟨296584828541582286593681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163571504443544390332597 296584828541582286593681)
                  ·
                    rfl

theorem cell23_5198372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_5198372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198372 prefixEnd_5198372 := by exact prefixLift 5198372
  have htrace : WordTrace (prefixWord ++ tailWord_5198372) baseStart_5198372 baseEnd_5198372 := by
    simpa [prefixWord, tailWord_5198372, baseEnd_5198372] using wordTrace_append hprefix tailTrace_5198372
  have hstable : (prefixWord ++ tailWord_5198372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198372).length < 2 ^ (prefixWord ++ tailWord_5198372).sum := by decide
  have hdescent : baseEnd_5198372 < baseStart_5198372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198394 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_5198394 : Nat := 118140960795 + 5198394 * 2 ^ 59
def prefixEnd_5198394 : Nat := 4983230072969 + 3 ^ 40 * 5198394 * 2
def baseEnd_5198394 : Nat := 296586083716515499252003

theorem tailTrace_5198394 : CollatzResearch.WordTrace tailWord_5198394 prefixEnd_5198394 296586083716515499252003 := by
  unfold tailWord_5198394
  simp only [CollatzResearch.WordTrace]
  refine ⟨47400251382278456964436559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126400670352742551905164157 47400251382278456964436559)
  ·
    refine ⟨71100377073417685446654839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47400251382278456964436559 71100377073417685446654839)
    ·
      refine ⟨106650565610126528169982259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71100377073417685446654839 106650565610126528169982259)
      ·
        refine ⟨159975848415189792254973389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106650565610126528169982259 159975848415189792254973389)
        ·
          refine ⟨59990943155696172095615021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159975848415189792254973389 59990943155696172095615021)
          ·
            refine ⟨22496603683386064535855633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59990943155696172095615021 22496603683386064535855633)
            ·
              refine ⟨16872452762539548401891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22496603683386064535855633 16872452762539548401891725)
              ·
                refine ⟨6327169785952330650709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16872452762539548401891725 6327169785952330650709397)
                ·
                  refine ⟨296586083716515499252003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6327169785952330650709397 296586083716515499252003)
                  ·
                    rfl

theorem cell23_5198394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_5198394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198394 prefixEnd_5198394 := by exact prefixLift 5198394
  have htrace : WordTrace (prefixWord ++ tailWord_5198394) baseStart_5198394 baseEnd_5198394 := by
    simpa [prefixWord, tailWord_5198394, baseEnd_5198394] using wordTrace_append hprefix tailTrace_5198394
  have hstable : (prefixWord ++ tailWord_5198394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198394).length < 2 ^ (prefixWord ++ tailWord_5198394).sum := by decide
  have hdescent : baseEnd_5198394 < baseStart_5198394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198428 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 6]
def baseStart_5198428 : Nat := 118140960795 + 5198428 * 2 ^ 59
def prefixEnd_5198428 : Nat := 4983230072969 + 3 ^ 40 * 5198428 * 2
def baseEnd_5198428 : Nat := 296588023532321373360319

theorem tailTrace_5198428 : CollatzResearch.WordTrace tailWord_5198428 prefixEnd_5198428 296588023532321373360319 := by
  unfold tailWord_5198428
  simp only [CollatzResearch.WordTrace]
  refine ⟨94801122805495325832241969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126401497073993767776322625 94801122805495325832241969)
  ·
    refine ⟨71100842104121494374181477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94801122805495325832241969 71100842104121494374181477)
    ·
      refine ⟨13331407894522780195159027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71100842104121494374181477 13331407894522780195159027)
      ·
        refine ⟨19997111841784170292738541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331407894522780195159027 19997111841784170292738541)
        ·
          refine ⟨7498916940669063859776953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19997111841784170292738541 7498916940669063859776953)
          ·
            refine ⟨5624187705501797894832715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7498916940669063859776953 5624187705501797894832715)
            ·
              refine ⟨8436281558252696842249073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624187705501797894832715 8436281558252696842249073)
              ·
                refine ⟨6327211168689522631686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8436281558252696842249073 6327211168689522631686805)
                ·
                  refine ⟨296588023532321373360319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6327211168689522631686805 296588023532321373360319)
                  ·
                    rfl

theorem cell23_5198428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_5198428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198428 prefixEnd_5198428 := by exact prefixLift 5198428
  have htrace : WordTrace (prefixWord ++ tailWord_5198428) baseStart_5198428 baseEnd_5198428 := by
    simpa [prefixWord, tailWord_5198428, baseEnd_5198428] using wordTrace_append hprefix tailTrace_5198428
  have hstable : (prefixWord ++ tailWord_5198428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198428).length < 2 ^ (prefixWord ++ tailWord_5198428).sum := by decide
  have hdescent : baseEnd_5198428 < baseStart_5198428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198431 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 2, 3, 2]
def baseStart_5198431 : Nat := 118140960795 + 5198431 * 2 ^ 59
def prefixEnd_5198431 : Nat := 4983230072969 + 3 ^ 40 * 5198431 * 2
def baseEnd_5198431 : Nat := 2669293752232855848505357

theorem tailTrace_5198431 : CollatzResearch.WordTrace tailWord_5198431 prefixEnd_5198431 2669293752232855848505357 := by
  unfold tailWord_5198431
  simp only [CollatzResearch.WordTrace]
  refine ⟨189602355029979783176843147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126401570019986522117895431 189602355029979783176843147)
  ·
    refine ⟨284403532544969674765264721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189602355029979783176843147 284403532544969674765264721)
    ·
      refine ⟨213302649408727256073948541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284403532544969674765264721 213302649408727256073948541)
      ·
        refine ⟨79988493528272721027730703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213302649408727256073948541 79988493528272721027730703)
        ·
          refine ⟨119982740292409081541596055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79988493528272721027730703 119982740292409081541596055)
          ·
            refine ⟨179974110438613622312394083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119982740292409081541596055 179974110438613622312394083)
            ·
              refine ⟨269961165657920433468591125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179974110438613622312394083 269961165657920433468591125)
              ·
                refine ⟨12654429640215020318840209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 269961165657920433468591125 12654429640215020318840209)
                ·
                  refine ⟨9490822230161265239130157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12654429640215020318840209 9490822230161265239130157)
                  ·
                    refine ⟨3559058336310474464673809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9490822230161265239130157 3559058336310474464673809)
                    ·
                      refine ⟨2669293752232855848505357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559058336310474464673809 2669293752232855848505357)
                      ·
                        rfl

theorem cell23_5198431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_5198431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198431 prefixEnd_5198431 := by exact prefixLift 5198431
  have htrace : WordTrace (prefixWord ++ tailWord_5198431) baseStart_5198431 baseEnd_5198431 := by
    simpa [prefixWord, tailWord_5198431, baseEnd_5198431] using wordTrace_append hprefix tailTrace_5198431
  have hstable : (prefixWord ++ tailWord_5198431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198431).length < 2 ^ (prefixWord ++ tailWord_5198431).sum := by decide
  have hdescent : baseEnd_5198431 < baseStart_5198431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198444 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_5198444 : Nat := 118140960795 + 5198444 * 2 ^ 59
def prefixEnd_5198444 : Nat := 4983230072969 + 3 ^ 40 * 5198444 * 2
def baseEnd_5198444 : Nat := 2669300427481364297642797

theorem tailTrace_5198444 : CollatzResearch.WordTrace tailWord_5198444 prefixEnd_5198444 2669300427481364297642797 := by
  unfold tailWord_5198444
  simp only [CollatzResearch.WordTrace]
  refine ⟨94801414589466343198533193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126401886119288457598044257 94801414589466343198533193)
  ·
    refine ⟨71101060942099757398899895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94801414589466343198533193 71101060942099757398899895)
    ·
      refine ⟨106651591413149636098349843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71101060942099757398899895 106651591413149636098349843)
      ·
        refine ⟨159977387119724454147524765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106651591413149636098349843 159977387119724454147524765)
        ·
          refine ⟨59991520169896670305321787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159977387119724454147524765 59991520169896670305321787)
          ·
            refine ⟨89987280254845005457982681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59991520169896670305321787 89987280254845005457982681)
            ·
              refine ⟨67490460191133754093487011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89987280254845005457982681 67490460191133754093487011)
              ·
                refine ⟨101235690286700631140230517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67490460191133754093487011 101235690286700631140230517)
                ·
                  refine ⟨9490845964378184169396611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101235690286700631140230517 9490845964378184169396611)
                  ·
                    refine ⟨14236268946567276254094917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9490845964378184169396611 14236268946567276254094917)
                    ·
                      refine ⟨2669300427481364297642797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14236268946567276254094917 2669300427481364297642797)
                      ·
                        rfl

theorem cell23_5198444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_5198444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198444 prefixEnd_5198444 := by exact prefixLift 5198444
  have htrace : WordTrace (prefixWord ++ tailWord_5198444) baseStart_5198444 baseEnd_5198444 := by
    simpa [prefixWord, tailWord_5198444, baseEnd_5198444] using wordTrace_append hprefix tailTrace_5198444
  have hstable : (prefixWord ++ tailWord_5198444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198444).length < 2 ^ (prefixWord ++ tailWord_5198444).sum := by decide
  have hdescent : baseEnd_5198444 < baseStart_5198444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198466 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5198466 : Nat := 118140960795 + 5198466 * 2 ^ 59
def prefixEnd_5198466 : Nat := 4983230072969 + 3 ^ 40 * 5198466 * 2
def baseEnd_5198466 : Nat := 889770574685254403855899

theorem tailTrace_5198466 : CollatzResearch.WordTrace tailWord_5198466 prefixEnd_5198466 889770574685254403855899 := by
  unfold tailWord_5198466
  simp only [CollatzResearch.WordTrace]
  refine ⟨47400907896213246038591813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126402421056568656102911501 47400907896213246038591813)
  ·
    refine ⟨8887670230539983632235965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47400907896213246038591813 8887670230539983632235965)
    ·
      refine ⟨3332876336452493862088487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8887670230539983632235965 3332876336452493862088487)
      ·
        refine ⟨4999314504678740793132731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3332876336452493862088487 4999314504678740793132731)
        ·
          refine ⟨7498971757018111189699097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999314504678740793132731 7498971757018111189699097)
          ·
            refine ⟨5624228817763583392274323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7498971757018111189699097 5624228817763583392274323)
            ·
              refine ⟨8436343226645375088411485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624228817763583392274323 8436343226645375088411485)
              ·
                refine ⟨3163628709992015658154307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8436343226645375088411485 3163628709992015658154307)
                ·
                  refine ⟨4745443064988023487231461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163628709992015658154307 4745443064988023487231461)
                  ·
                    refine ⟨889770574685254403855899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4745443064988023487231461 889770574685254403855899)
                    ·
                      rfl

theorem cell23_5198466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5198466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198466 prefixEnd_5198466 := by exact prefixLift 5198466
  have htrace : WordTrace (prefixWord ++ tailWord_5198466) baseStart_5198466 baseEnd_5198466 := by
    simpa [prefixWord, tailWord_5198466, baseEnd_5198466] using wordTrace_append hprefix tailTrace_5198466
  have hstable : (prefixWord ++ tailWord_5198466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198466).length < 2 ^ (prefixWord ++ tailWord_5198466).sum := by decide
  have hdescent : baseEnd_5198466 < baseStart_5198466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198546 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5198546 : Nat := 118140960795 + 5198546 * 2 ^ 59
def prefixEnd_5198546 : Nat := 4983230072969 + 3 ^ 40 * 5198546 * 2
def baseEnd_5198546 : Nat := 2669352802508122898567329

theorem tailTrace_5198546 : CollatzResearch.WordTrace tailWord_5198546 prefixEnd_5198546 2669352802508122898567329 := by
  unfold tailWord_5198546
  simp only [CollatzResearch.WordTrace]
  refine ⟨47401637356140789454319873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126404366283042105211519661 47401637356140789454319873)
  ·
    refine ⟨35551228017105592090739905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47401637356140789454319873 35551228017105592090739905)
    ·
      refine ⟨26663421012829194068054929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35551228017105592090739905 26663421012829194068054929)
      ·
        refine ⟨19997565759621895551041197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26663421012829194068054929 19997565759621895551041197)
        ·
          refine ⟨7499087159858210831640449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19997565759621895551041197 7499087159858210831640449)
          ·
            refine ⟨5624315369893658123730337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7499087159858210831640449 5624315369893658123730337)
            ·
              refine ⟨4218236527420243592797753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5624315369893658123730337 4218236527420243592797753)
              ·
                refine ⟨3163677395565182694598315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4218236527420243592797753 3163677395565182694598315)
                ·
                  refine ⟨4745516093347774041897473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163677395565182694598315 4745516093347774041897473)
                  ·
                    refine ⟨3559137070010830531423105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4745516093347774041897473 3559137070010830531423105)
                    ·
                      refine ⟨2669352802508122898567329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559137070010830531423105 2669352802508122898567329)
                      ·
                        rfl

theorem cell23_5198546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5198546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198546 prefixEnd_5198546 := by exact prefixLift 5198546
  have htrace : WordTrace (prefixWord ++ tailWord_5198546) baseStart_5198546 baseEnd_5198546 := by
    simpa [prefixWord, tailWord_5198546, baseEnd_5198546] using wordTrace_append hprefix tailTrace_5198546
  have hstable : (prefixWord ++ tailWord_5198546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198546).length < 2 ^ (prefixWord ++ tailWord_5198546).sum := by decide
  have hdescent : baseEnd_5198546 < baseStart_5198546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198561 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_5198561 : Nat := 118140960795 + 5198561 * 2 ^ 59
def prefixEnd_5198561 : Nat := 4983230072969 + 3 ^ 40 * 5198561 * 2
def baseEnd_5198561 : Nat := 889786834905980113293253

theorem tailTrace_5198561 : CollatzResearch.WordTrace tailWord_5198561 prefixEnd_5198561 889786834905980113293253 := by
  unfold tailWord_5198561
  simp only [CollatzResearch.WordTrace]
  refine ⟨189607096519508815379075537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126404731013005876919383691 189607096519508815379075537)
  ·
    refine ⟨142205322389631611534306653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189607096519508815379075537 142205322389631611534306653)
    ·
      refine ⟨53326995896111854325364995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142205322389631611534306653 53326995896111854325364995)
      ·
        refine ⟨79990493844167781488047493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53326995896111854325364995 79990493844167781488047493)
        ·
          refine ⟨14998217595781459029008905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79990493844167781488047493 14998217595781459029008905)
          ·
            refine ⟨11248663196836094271756679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14998217595781459029008905 11248663196836094271756679)
            ·
              refine ⟨16872994795254141407635019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11248663196836094271756679 16872994795254141407635019)
              ·
                refine ⟨25309492192881212111452529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16872994795254141407635019 25309492192881212111452529)
                ·
                  refine ⟨18982119144660909083589397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25309492192881212111452529 18982119144660909083589397)
                  ·
                    refine ⟨889786834905980113293253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18982119144660909083589397 889786834905980113293253)
                    ·
                      rfl

theorem cell23_5198561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_5198561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198561 prefixEnd_5198561 := by exact prefixLift 5198561
  have htrace : WordTrace (prefixWord ++ tailWord_5198561) baseStart_5198561 baseEnd_5198561 := by
    simpa [prefixWord, tailWord_5198561, baseEnd_5198561] using wordTrace_append hprefix tailTrace_5198561
  have hstable : (prefixWord ++ tailWord_5198561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198561).length < 2 ^ (prefixWord ++ tailWord_5198561).sum := by decide
  have hdescent : baseEnd_5198561 < baseStart_5198561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198601 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_5198601 : Nat := 118140960795 + 5198601 * 2 ^ 59
def prefixEnd_5198601 : Nat := 4983230072969 + 3 ^ 40 * 5198601 * 2
def baseEnd_5198601 : Nat := 2669381043944120183379575

theorem tailTrace_5198601 : CollatzResearch.WordTrace tailWord_5198601 prefixEnd_5198601 2669381043944120183379575 := by
  unfold tailWord_5198601
  simp only [CollatzResearch.WordTrace]
  refine ⟨189608555439363902210531657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126405703626242601473687771 189608555439363902210531657)
  ·
    refine ⟨142206416579522926657898743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189608555439363902210531657 142206416579522926657898743)
    ·
      refine ⟨213309624869284389986848115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142206416579522926657898743 213309624869284389986848115)
      ·
        refine ⟨319964437303926584980272173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213309624869284389986848115 319964437303926584980272173)
        ·
          refine ⟨119986663988972469367602065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319964437303926584980272173 119986663988972469367602065)
          ·
            refine ⟨89989997991729352025701549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119986663988972469367602065 89989997991729352025701549)
            ·
              refine ⟨33746249246898507009638081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89989997991729352025701549 33746249246898507009638081)
              ·
                refine ⟨25309686935173880257228561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33746249246898507009638081 25309686935173880257228561)
                ·
                  refine ⟨18982265201380410192921421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25309686935173880257228561 18982265201380410192921421)
                  ·
                    refine ⟨7118349450517653822345533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18982265201380410192921421 7118349450517653822345533)
                    ·
                      refine ⟨2669381043944120183379575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118349450517653822345533 2669381043944120183379575)
                      ·
                        rfl

theorem cell23_5198601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_5198601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198601 prefixEnd_5198601 := by exact prefixLift 5198601
  have htrace : WordTrace (prefixWord ++ tailWord_5198601) baseStart_5198601 baseEnd_5198601 := by
    simpa [prefixWord, tailWord_5198601, baseEnd_5198601] using wordTrace_append hprefix tailTrace_5198601
  have hstable : (prefixWord ++ tailWord_5198601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198601).length < 2 ^ (prefixWord ++ tailWord_5198601).sum := by decide
  have hdescent : baseEnd_5198601 < baseStart_5198601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198638 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5198638 : Nat := 118140960795 + 5198638 * 2 ^ 59
def prefixEnd_5198638 : Nat := 4983230072969 + 3 ^ 40 * 5198638 * 2
def baseEnd_5198638 : Nat := 889800014242778846205635

theorem tailTrace_5198638 : CollatzResearch.WordTrace tailWord_5198638 prefixEnd_5198638 889800014242778846205635 := by
  unfold tailWord_5198638
  simp only [CollatzResearch.WordTrace]
  refine ⟨23701238117528732191203571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126406603293486571686419045 23701238117528732191203571)
  ·
    refine ⟨35551857176293098286805357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23701238117528732191203571 35551857176293098286805357)
    ·
      refine ⟨13331946441109911857552009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35551857176293098286805357 13331946441109911857552009)
      ·
        refine ⟨9998959830832433893164007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13331946441109911857552009 9998959830832433893164007)
        ·
          refine ⟨14998439746248650839746011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9998959830832433893164007 14998439746248650839746011)
          ·
            refine ⟨22497659619372976259619017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14998439746248650839746011 22497659619372976259619017)
            ·
              refine ⟨16873244714529732194714263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22497659619372976259619017 16873244714529732194714263)
              ·
                refine ⟨25309867071794598292071395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16873244714529732194714263 25309867071794598292071395)
                ·
                  refine ⟨37964800607691897438107093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25309867071794598292071395 37964800607691897438107093)
                  ·
                    refine ⟨889800014242778846205635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37964800607691897438107093 889800014242778846205635)
                    ·
                      rfl

theorem cell23_5198638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5198638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198638 prefixEnd_5198638 := by exact prefixLift 5198638
  have htrace : WordTrace (prefixWord ++ tailWord_5198638) baseStart_5198638 baseEnd_5198638 := by
    simpa [prefixWord, tailWord_5198638, baseEnd_5198638] using wordTrace_append hprefix tailTrace_5198638
  have hstable : (prefixWord ++ tailWord_5198638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198638).length < 2 ^ (prefixWord ++ tailWord_5198638).sum := by decide
  have hdescent : baseEnd_5198638 < baseStart_5198638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198641 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_5198641 : Nat := 118140960795 + 5198641 * 2 ^ 59
def prefixEnd_5198641 : Nat := 4983230072969 + 3 ^ 40 * 5198641 * 2
def baseEnd_5198641 : Nat := 2669401583170300026879391

theorem tailTrace_5198641 : CollatzResearch.WordTrace tailWord_5198641 prefixEnd_5198641 2669401583170300026879391 := by
  unfold tailWord_5198641
  simp only [CollatzResearch.WordTrace]
  refine ⟨189610014359218989041987777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126406676239479326027991851 189610014359218989041987777)
  ·
    refine ⟨142207510769414241781490833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189610014359218989041987777 142207510769414241781490833)
    ·
      refine ⟨106655633077060681336118125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142207510769414241781490833 106655633077060681336118125)
      ·
        refine ⟨39995862403897755501044297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106655633077060681336118125 39995862403897755501044297)
        ·
          refine ⟨29996896802923316625783223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39995862403897755501044297 29996896802923316625783223)
          ·
            refine ⟨44995345204384974938674835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29996896802923316625783223 44995345204384974938674835)
            ·
              refine ⟨67493017806577462408012253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44995345204384974938674835 67493017806577462408012253)
              ·
                refine ⟨25309881677466548403004595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67493017806577462408012253 25309881677466548403004595)
                ·
                  refine ⟨37964822516199822604506893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25309881677466548403004595 37964822516199822604506893)
                  ·
                    refine ⟨14236808443574933476690085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37964822516199822604506893 14236808443574933476690085)
                    ·
                      refine ⟨2669401583170300026879391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14236808443574933476690085 2669401583170300026879391)
                      ·
                        rfl

theorem cell23_5198641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_5198641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198641 prefixEnd_5198641 := by exact prefixLift 5198641
  have htrace : WordTrace (prefixWord ++ tailWord_5198641) baseStart_5198641 baseEnd_5198641 := by
    simpa [prefixWord, tailWord_5198641, baseEnd_5198641] using wordTrace_append hprefix tailTrace_5198641
  have hstable : (prefixWord ++ tailWord_5198641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198641).length < 2 ^ (prefixWord ++ tailWord_5198641).sum := by decide
  have hdescent : baseEnd_5198641 < baseStart_5198641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198661 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_5198661 : Nat := 118140960795 + 5198661 * 2 ^ 59
def prefixEnd_5198661 : Nat := 4983230072969 + 3 ^ 40 * 5198661 * 2
def baseEnd_5198661 : Nat := 2669411852783389948629299

theorem tailTrace_5198661 : CollatzResearch.WordTrace tailWord_5198661 prefixEnd_5198661 2669411852783389948629299 := by
  unfold tailWord_5198661
  simp only [CollatzResearch.WordTrace]
  refine ⟨189610743819146532457715837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126407162546097688305143891 189610743819146532457715837)
  ·
    refine ⟨71104028932179949671643439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189610743819146532457715837 71104028932179949671643439)
    ·
      refine ⟨106656043398269924507465159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71104028932179949671643439 106656043398269924507465159)
      ·
        refine ⟨159984065097404886761197739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106656043398269924507465159 159984065097404886761197739)
        ·
          refine ⟨239976097646107330141796609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159984065097404886761197739 239976097646107330141796609)
          ·
            refine ⟨179982073234580497606347457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239976097646107330141796609 179982073234580497606347457)
            ·
              refine ⟨134986554925935373204760593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179982073234580497606347457 134986554925935373204760593)
              ·
                refine ⟨101239916194451529903570445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134986554925935373204760593 101239916194451529903570445)
                ·
                  refine ⟨37964968572919323713838917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101239916194451529903570445 37964968572919323713838917)
                  ·
                    refine ⟨7118431607422373196344797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37964968572919323713838917 7118431607422373196344797)
                    ·
                      refine ⟨2669411852783389948629299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118431607422373196344797 2669411852783389948629299)
                      ·
                        rfl

theorem cell23_5198661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_5198661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198661 prefixEnd_5198661 := by exact prefixLift 5198661
  have htrace : WordTrace (prefixWord ++ tailWord_5198661) baseStart_5198661 baseEnd_5198661 := by
    simpa [prefixWord, tailWord_5198661, baseEnd_5198661] using wordTrace_append hprefix tailTrace_5198661
  have hstable : (prefixWord ++ tailWord_5198661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198661).length < 2 ^ (prefixWord ++ tailWord_5198661).sum := by decide
  have hdescent : baseEnd_5198661 < baseStart_5198661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198695 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_5198695 : Nat := 118140960795 + 5198695 * 2 ^ 59
def prefixEnd_5198695 : Nat := 4983230072969 + 3 ^ 40 * 5198695 * 2
def baseEnd_5198695 : Nat := 2669429311125642815604143

theorem tailTrace_5198695 : CollatzResearch.WordTrace tailWord_5198695 prefixEnd_5198695 2669429311125642815604143 := by
  unfold tailWord_5198695
  simp only [CollatzResearch.WordTrace]
  refine ⟨189611983901023356264453539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126407989267348904176302359 189611983901023356264453539)
  ·
    refine ⟨284417975851535034396680309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189611983901023356264453539 284417975851535034396680309)
    ·
      refine ⟨26664185236081409474688779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284417975851535034396680309 26664185236081409474688779)
      ·
        refine ⟨39996277854122114212033169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26664185236081409474688779 39996277854122114212033169)
        ·
          refine ⟨29997208390591585659024877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39996277854122114212033169 29997208390591585659024877)
          ·
            refine ⟨11248953146471844622134329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29997208390591585659024877 11248953146471844622134329)
            ·
              refine ⟨8436714859853883466600747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11248953146471844622134329 8436714859853883466600747)
              ·
                refine ⟨12655072289780825199901121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8436714859853883466600747 12655072289780825199901121)
                ·
                  refine ⟨9491304217335618899925841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12655072289780825199901121 9491304217335618899925841)
                  ·
                    refine ⟨7118478163001714174944381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9491304217335618899925841 7118478163001714174944381)
                    ·
                      refine ⟨2669429311125642815604143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118478163001714174944381 2669429311125642815604143)
                      ·
                        rfl

theorem cell23_5198695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_5198695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198695 prefixEnd_5198695 := by exact prefixLift 5198695
  have htrace : WordTrace (prefixWord ++ tailWord_5198695) baseStart_5198695 baseEnd_5198695 := by
    simpa [prefixWord, tailWord_5198695, baseEnd_5198695] using wordTrace_append hprefix tailTrace_5198695
  have hstable : (prefixWord ++ tailWord_5198695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198695).length < 2 ^ (prefixWord ++ tailWord_5198695).sum := by decide
  have hdescent : baseEnd_5198695 < baseStart_5198695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198701 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5198701 : Nat := 118140960795 + 5198701 * 2 ^ 59
def prefixEnd_5198701 : Nat := 4983230072969 + 3 ^ 40 * 5198701 * 2
def baseEnd_5198701 : Nat := 2669432392009569792129115

theorem tailTrace_5198701 : CollatzResearch.WordTrace tailWord_5198701 prefixEnd_5198701 2669432392009569792129115 := by
  unfold tailWord_5198701
  simp only [CollatzResearch.WordTrace]
  refine ⟨189612202739001619289171957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126408135159334412859447971 189612202739001619289171957)
  ·
    refine ⟨17776144006781401808359871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189612202739001619289171957 17776144006781401808359871)
    ·
      refine ⟨26664216010172102712539807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17776144006781401808359871 26664216010172102712539807)
      ·
        refine ⟨39996324015258154068809711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26664216010172102712539807 39996324015258154068809711)
        ·
          refine ⟨59994486022887231103214567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39996324015258154068809711 59994486022887231103214567)
          ·
            refine ⟨89991729034330846654821851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59994486022887231103214567 89991729034330846654821851)
            ·
              refine ⟨134987593551496269982232777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89991729034330846654821851 134987593551496269982232777)
              ·
                refine ⟨101240695163622202486674583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134987593551496269982232777 101240695163622202486674583)
                ·
                  refine ⟨151861042745433303730011875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101240695163622202486674583 151861042745433303730011875)
                  ·
                    refine ⟨227791564118149955595017813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151861042745433303730011875 227791564118149955595017813)
                    ·
                      refine ⟨2669432392009569792129115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 227791564118149955595017813 2669432392009569792129115)
                      ·
                        rfl

theorem cell23_5198701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5198701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198701 prefixEnd_5198701 := by exact prefixLift 5198701
  have htrace : WordTrace (prefixWord ++ tailWord_5198701) baseStart_5198701 baseEnd_5198701 := by
    simpa [prefixWord, tailWord_5198701, baseEnd_5198701] using wordTrace_append hprefix tailTrace_5198701
  have hstable : (prefixWord ++ tailWord_5198701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198701).length < 2 ^ (prefixWord ++ tailWord_5198701).sum := by decide
  have hdescent : baseEnd_5198701 < baseStart_5198701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198728 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_5198728 : Nat := 118140960795 + 5198728 * 2 ^ 59
def prefixEnd_5198728 : Nat := 4983230072969 + 3 ^ 40 * 5198728 * 2
def baseEnd_5198728 : Nat := 889815418662413728830497

theorem tailTrace_5198728 : CollatzResearch.WordTrace tailWord_5198728 prefixEnd_5198728 889815418662413728830497 := by
  unfold tailWord_5198728
  simp only [CollatzResearch.WordTrace]
  refine ⟨94806593754951901450202419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126408791673269201933603225 94806593754951901450202419)
  ·
    refine ⟨142209890632427852175303629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94806593754951901450202419 142209890632427852175303629)
    ·
      refine ⟨53328708987160444565738861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142209890632427852175303629 53328708987160444565738861)
      ·
        refine ⟨19998265870185166712152073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53328708987160444565738861 19998265870185166712152073)
        ·
          refine ⟨14998699402638875034114055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19998265870185166712152073 14998699402638875034114055)
          ·
            refine ⟨22498049103958312551171083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14998699402638875034114055 22498049103958312551171083)
            ·
              refine ⟨33747073655937468826756625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22498049103958312551171083 33747073655937468826756625)
              ·
                refine ⟨25310305241953101620067469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33747073655937468826756625 25310305241953101620067469)
                ·
                  refine ⟨9491364465732413107525301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25310305241953101620067469 9491364465732413107525301)
                  ·
                    refine ⟨889815418662413728830497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9491364465732413107525301 889815418662413728830497)
                    ·
                      rfl

theorem cell23_5198728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_5198728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198728 prefixEnd_5198728 := by exact prefixLift 5198728
  have htrace : WordTrace (prefixWord ++ tailWord_5198728) baseStart_5198728 baseEnd_5198728 := by
    simpa [prefixWord, tailWord_5198728, baseEnd_5198728] using wordTrace_append hprefix tailTrace_5198728
  have hstable : (prefixWord ++ tailWord_5198728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198728).length < 2 ^ (prefixWord ++ tailWord_5198728).sum := by decide
  have hdescent : baseEnd_5198728 < baseStart_5198728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198775 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 2, 4]
def baseStart_5198775 : Nat := 118140960795 + 5198775 * 2 ^ 59
def prefixEnd_5198775 : Nat := 4983230072969 + 3 ^ 40 * 5198775 * 2
def baseEnd_5198775 : Nat := 889823463192667500867925

theorem tailTrace_5198775 : CollatzResearch.WordTrace tailWord_5198775 prefixEnd_5198775 889823463192667500867925 := by
  unfold tailWord_5198775
  simp only [CollatzResearch.WordTrace]
  refine ⟨189614901740733529927365779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126409934493822353284910519 189614901740733529927365779)
  ·
    refine ⟨284422352611100294891048669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189614901740733529927365779 284422352611100294891048669)
    ·
      refine ⟨106658382229162610584143251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284422352611100294891048669 106658382229162610584143251)
      ·
        refine ⟨159987573343743915876214877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106658382229162610584143251 159987573343743915876214877)
        ·
          refine ⟨59995340003903968453580579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159987573343743915876214877 59995340003903968453580579)
          ·
            refine ⟨89993010005855952680370869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59995340003903968453580579 89993010005855952680370869)
            ·
              refine ⟨8436844688048995563784769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89993010005855952680370869 8436844688048995563784769)
              ·
                refine ⟨6327633516036746672838577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8436844688048995563784769 6327633516036746672838577)
                ·
                  refine ⟨4745725137027560004628933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327633516036746672838577 4745725137027560004628933)
                  ·
                    refine ⟨889823463192667500867925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4745725137027560004628933 889823463192667500867925)
                    ·
                      rfl

theorem cell23_5198775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_5198775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198775 prefixEnd_5198775 := by exact prefixLift 5198775
  have htrace : WordTrace (prefixWord ++ tailWord_5198775) baseStart_5198775 baseEnd_5198775 := by
    simpa [prefixWord, tailWord_5198775, baseEnd_5198775] using wordTrace_append hprefix tailTrace_5198775
  have hstable : (prefixWord ++ tailWord_5198775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198775).length < 2 ^ (prefixWord ++ tailWord_5198775).sum := by decide
  have hdescent : baseEnd_5198775 < baseStart_5198775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198792 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 1, 6]
def baseStart_5198792 : Nat := 118140960795 + 5198792 * 2 ^ 59
def prefixEnd_5198792 : Nat := 4983230072969 + 3 ^ 40 * 5198792 * 2
def baseEnd_5198792 : Nat := 889826372916376312030399

theorem tailTrace_5198792 : CollatzResearch.WordTrace tailWord_5198792 prefixEnd_5198792 889826372916376312030399 := by
  unfold tailWord_5198792
  simp only [CollatzResearch.WordTrace]
  refine ⟨94807760890835970915367315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126410347854447961220489753 94807760890835970915367315)
  ·
    refine ⟨142211641336253956373050973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94807760890835970915367315 142211641336253956373050973)
    ·
      refine ⟨53329365501095233639894115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142211641336253956373050973 53329365501095233639894115)
      ·
        refine ⟨79994048251642850459841173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53329365501095233639894115 79994048251642850459841173)
        ·
          refine ⟨3749721011795758615305055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79994048251642850459841173 3749721011795758615305055)
          ·
            refine ⟨5624581517693637922957583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749721011795758615305055 5624581517693637922957583)
            ·
              refine ⟨8436872276540456884436375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624581517693637922957583 8436872276540456884436375)
              ·
                refine ⟨12655308414810685326654563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8436872276540456884436375 12655308414810685326654563)
                ·
                  refine ⟨18982962622216027989981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12655308414810685326654563 18982962622216027989981845)
                  ·
                    refine ⟨889826372916376312030399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18982962622216027989981845 889826372916376312030399)
                    ·
                      rfl

theorem cell23_5198792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_5198792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198792 prefixEnd_5198792 := by exact prefixLift 5198792
  have htrace : WordTrace (prefixWord ++ tailWord_5198792) baseStart_5198792 baseEnd_5198792 := by
    simpa [prefixWord, tailWord_5198792, baseEnd_5198792] using wordTrace_append hprefix tailTrace_5198792
  have hstable : (prefixWord ++ tailWord_5198792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198792).length < 2 ^ (prefixWord ++ tailWord_5198792).sum := by decide
  have hdescent : baseEnd_5198792 < baseStart_5198792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198795 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 4]
def baseStart_5198795 : Nat := 118140960795 + 5198795 * 2 ^ 59
def prefixEnd_5198795 : Nat := 4983230072969 + 3 ^ 40 * 5198795 * 2
def baseEnd_5198795 : Nat := 2669480659191092424353683

theorem tailTrace_5198795 : CollatzResearch.WordTrace tailWord_5198795 prefixEnd_5198795 2669480659191092424353683 := by
  unfold tailWord_5198795
  simp only [CollatzResearch.WordTrace]
  refine ⟨189615631200661073343093839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126410420800440715562062559 189615631200661073343093839)
  ·
    refine ⟨284423446800991610014640759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189615631200661073343093839 284423446800991610014640759)
    ·
      refine ⟨426635170201487415021961139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284423446800991610014640759 426635170201487415021961139)
      ·
        refine ⟨639952755302231122532941709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426635170201487415021961139 639952755302231122532941709)
        ·
          refine ⟨239982283238336670949853141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639952755302231122532941709 239982283238336670949853141)
          ·
            refine ⟨5624584763398515725387183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239982283238336670949853141 5624584763398515725387183)
            ·
              refine ⟨8436877145097773588080775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624584763398515725387183 8436877145097773588080775)
              ·
                refine ⟨12655315717646660382121163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8436877145097773588080775 12655315717646660382121163)
                ·
                  refine ⟨18982973576469990573181745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12655315717646660382121163 18982973576469990573181745)
                  ·
                    refine ⟨14237230182352492929886309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18982973576469990573181745 14237230182352492929886309)
                    ·
                      refine ⟨2669480659191092424353683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14237230182352492929886309 2669480659191092424353683)
                      ·
                        rfl

theorem cell23_5198795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 4].length) (baseStart_5198795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198795 prefixEnd_5198795 := by exact prefixLift 5198795
  have htrace : WordTrace (prefixWord ++ tailWord_5198795) baseStart_5198795 baseEnd_5198795 := by
    simpa [prefixWord, tailWord_5198795, baseEnd_5198795] using wordTrace_append hprefix tailTrace_5198795
  have hstable : (prefixWord ++ tailWord_5198795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198795).length < 2 ^ (prefixWord ++ tailWord_5198795).sum := by decide
  have hdescent : baseEnd_5198795 < baseStart_5198795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198802 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5198802 : Nat := 118140960795 + 5198802 * 2 ^ 59
def prefixEnd_5198802 : Nat := 4983230072969 + 3 ^ 40 * 5198802 * 2
def baseEnd_5198802 : Nat := 2669484253555673896966151

theorem tailTrace_5198802 : CollatzResearch.WordTrace tailWord_5198802 prefixEnd_5198802 2669484253555673896966151 := by
  unfold tailWord_5198802
  simp only [CollatzResearch.WordTrace]
  refine ⟨47403971627908928384649665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126410591007757142359065773 47403971627908928384649665)
  ·
    refine ⟨35552978720931696288487249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47403971627908928384649665 35552978720931696288487249)
    ·
      refine ⟨26664734040698772216365437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35552978720931696288487249 26664734040698772216365437)
      ·
        refine ⟨9999275265262039581137039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26664734040698772216365437 9999275265262039581137039)
        ·
          refine ⟨14998912897893059371705559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9999275265262039581137039 14998912897893059371705559)
          ·
            refine ⟨22498369346839589057558339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14998912897893059371705559 22498369346839589057558339)
            ·
              refine ⟨33747554020259383586337509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22498369346839589057558339 33747554020259383586337509)
              ·
                refine ⟨6327666378798634422438283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33747554020259383586337509 6327666378798634422438283)
                ·
                  refine ⟨9491499568197951633657425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6327666378798634422438283 9491499568197951633657425)
                  ·
                    refine ⟨7118624676148463725243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9491499568197951633657425 7118624676148463725243069)
                    ·
                      refine ⟨2669484253555673896966151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118624676148463725243069 2669484253555673896966151)
                      ·
                        rfl

theorem cell23_5198802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5198802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198802 prefixEnd_5198802 := by exact prefixLift 5198802
  have htrace : WordTrace (prefixWord ++ tailWord_5198802) baseStart_5198802 baseEnd_5198802 := by
    simpa [prefixWord, tailWord_5198802, baseEnd_5198802] using wordTrace_append hprefix tailTrace_5198802
  have hstable : (prefixWord ++ tailWord_5198802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198802).length < 2 ^ (prefixWord ++ tailWord_5198802).sum := by decide
  have hdescent : baseEnd_5198802 < baseStart_5198802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198849 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_5198849 : Nat := 118140960795 + 5198849 * 2 ^ 59
def prefixEnd_5198849 : Nat := 4983230072969 + 3 ^ 40 * 5198849 * 2
def baseEnd_5198849 : Nat := 2669508387146435213078435

theorem tailTrace_5198849 : CollatzResearch.WordTrace tailWord_5198849 prefixEnd_5198849 2669508387146435213078435 := by
  unfold tailWord_5198849
  simp only [CollatzResearch.WordTrace]
  refine ⟨189617600742465440565559601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126411733828310293710373067 189617600742465440565559601)
  ·
    refine ⟨142213200556849080424169701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189617600742465440565559601 142213200556849080424169701)
    ·
      refine ⟨26664975104409202579531819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142213200556849080424169701 26664975104409202579531819)
      ·
        refine ⟨39997462656613803869297729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26664975104409202579531819 39997462656613803869297729)
        ·
          refine ⟨29998096992460352901973297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39997462656613803869297729 29998096992460352901973297)
          ·
            refine ⟨22498572744345264676479973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29998096992460352901973297 22498572744345264676479973)
            ·
              refine ⟨4218482389564737126839995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22498572744345264676479973 4218482389564737126839995)
              ·
                refine ⟨6327723584347105690259993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218482389564737126839995 6327723584347105690259993)
                ·
                  refine ⟨4745792688260329267694995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327723584347105690259993 4745792688260329267694995)
                  ·
                    refine ⟨7118689032390493901542493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4745792688260329267694995 7118689032390493901542493)
                    ·
                      refine ⟨2669508387146435213078435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118689032390493901542493 2669508387146435213078435)
                      ·
                        rfl

theorem cell23_5198849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_5198849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198849 prefixEnd_5198849 := by exact prefixLift 5198849
  have htrace : WordTrace (prefixWord ++ tailWord_5198849) baseStart_5198849 baseEnd_5198849 := by
    simpa [prefixWord, tailWord_5198849, baseEnd_5198849] using wordTrace_append hprefix tailTrace_5198849
  have hstable : (prefixWord ++ tailWord_5198849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198849).length < 2 ^ (prefixWord ++ tailWord_5198849).sum := by decide
  have hdescent : baseEnd_5198849 < baseStart_5198849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198859 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 1, 3, 2]
def baseStart_5198859 : Nat := 118140960795 + 5198859 * 2 ^ 59
def prefixEnd_5198859 : Nat := 4983230072969 + 3 ^ 40 * 5198859 * 2
def baseEnd_5198859 : Nat := 2669513521952980173953389

theorem tailTrace_5198859 : CollatzResearch.WordTrace tailWord_5198859 prefixEnd_5198859 2669513521952980173953389 := by
  unfold tailWord_5198859
  simp only [CollatzResearch.WordTrace]
  refine ⟨189617965472429212273423631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126411976981619474848949087 189617965472429212273423631)
  ·
    refine ⟨284426948208643818410135447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189617965472429212273423631 284426948208643818410135447)
    ·
      refine ⟨426640422312965727615203171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284426948208643818410135447 426640422312965727615203171)
      ·
        refine ⟨639960633469448591422804757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426640422312965727615203171 639960633469448591422804757)
        ·
          refine ⟨29998154693880402722943973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 639960633469448591422804757 29998154693880402722943973)
          ·
            refine ⟨5624654005102575510551995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29998154693880402722943973 5624654005102575510551995)
            ·
              refine ⟨8436981007653863265827993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624654005102575510551995 8436981007653863265827993)
              ·
                refine ⟨6327735755740397449370995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8436981007653863265827993 6327735755740397449370995)
                ·
                  refine ⟨9491603633610596174056493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6327735755740397449370995 9491603633610596174056493)
                  ·
                    refine ⟨3559351362603973565271185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9491603633610596174056493 3559351362603973565271185)
                    ·
                      refine ⟨2669513521952980173953389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559351362603973565271185 2669513521952980173953389)
                      ·
                        rfl

theorem cell23_5198859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3, 2].length) (baseStart_5198859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198859 prefixEnd_5198859 := by exact prefixLift 5198859
  have htrace : WordTrace (prefixWord ++ tailWord_5198859) baseStart_5198859 baseEnd_5198859 := by
    simpa [prefixWord, tailWord_5198859, baseEnd_5198859] using wordTrace_append hprefix tailTrace_5198859
  have hstable : (prefixWord ++ tailWord_5198859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198859).length < 2 ^ (prefixWord ++ tailWord_5198859).sum := by decide
  have hdescent : baseEnd_5198859 < baseStart_5198859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198866 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5198866 : Nat := 118140960795 + 5198866 * 2 ^ 59
def prefixEnd_5198866 : Nat := 4983230072969 + 3 ^ 40 * 5198866 * 2
def baseEnd_5198866 : Nat := 2669517116317561646565857

theorem tailTrace_5198866 : CollatzResearch.WordTrace tailWord_5198866 prefixEnd_5198866 2669517116317561646565857 := by
  unfold tailWord_5198866
  simp only [CollatzResearch.WordTrace]
  refine ⟨47404555195850963117232113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126412147188935901645952301 47404555195850963117232113)
  ·
    refine ⟨35553416396888222337924085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47404555195850963117232113 35553416396888222337924085)
    ·
      refine ⟨3333132787208270844180383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35553416396888222337924085 3333132787208270844180383)
      ·
        refine ⟨4999699180812406266270575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333132787208270844180383 4999699180812406266270575)
        ·
          refine ⟨7499548771218609399405863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999699180812406266270575 7499548771218609399405863)
          ·
            refine ⟨11249323156827914099108795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499548771218609399405863 11249323156827914099108795)
            ·
              refine ⟨16873984735241871148663193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11249323156827914099108795 16873984735241871148663193)
              ·
                refine ⟨12655488551431403361497395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16873984735241871148663193 12655488551431403361497395)
                ·
                  refine ⟨18983232827147105042246093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12655488551431403361497395 18983232827147105042246093)
                  ·
                    refine ⟨7118712310180164390842285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18983232827147105042246093 7118712310180164390842285)
                    ·
                      refine ⟨2669517116317561646565857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118712310180164390842285 2669517116317561646565857)
                      ·
                        rfl

theorem cell23_5198866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5198866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198866 prefixEnd_5198866 := by exact prefixLift 5198866
  have htrace : WordTrace (prefixWord ++ tailWord_5198866) baseStart_5198866 baseEnd_5198866 := by
    simpa [prefixWord, tailWord_5198866, baseEnd_5198866] using wordTrace_append hprefix tailTrace_5198866
  have hstable : (prefixWord ++ tailWord_5198866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198866).length < 2 ^ (prefixWord ++ tailWord_5198866).sum := by decide
  have hdescent : baseEnd_5198866 < baseStart_5198866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198872 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5198872 : Nat := 118140960795 + 5198872 * 2 ^ 59
def prefixEnd_5198872 : Nat := 4983230072969 + 3 ^ 40 * 5198872 * 2
def baseEnd_5198872 : Nat := 2669520197201488623090829

theorem tailTrace_5198872 : CollatzResearch.WordTrace tailWord_5198872 prefixEnd_5198872 2669520197201488623090829 := by
  unfold tailWord_5198872
  simp only [CollatzResearch.WordTrace]
  refine ⟨94809219810691057746823435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126412293080921410329097913 94809219810691057746823435)
  ·
    refine ⟨142213829716036586620235153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94809219810691057746823435 142213829716036586620235153)
    ·
      refine ⟨106660372287027439965176365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142213829716036586620235153 106660372287027439965176365)
      ·
        refine ⟨39997639607635289986941137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106660372287027439965176365 39997639607635289986941137)
        ·
          refine ⟨29998229705726467490205853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39997639607635289986941137 29998229705726467490205853)
          ·
            refine ⟨11249336139647425308827195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29998229705726467490205853 11249336139647425308827195)
            ·
              refine ⟨16874004209471137963240793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11249336139647425308827195 16874004209471137963240793)
              ·
                refine ⟨12655503157103353472430595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16874004209471137963240793 12655503157103353472430595)
                ·
                  refine ⟨18983254735655030208645893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12655503157103353472430595 18983254735655030208645893)
                  ·
                    refine ⟨3559360262935318164121105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18983254735655030208645893 3559360262935318164121105)
                    ·
                      refine ⟨2669520197201488623090829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559360262935318164121105 2669520197201488623090829)
                      ·
                        rfl

theorem cell23_5198872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5198872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198872 prefixEnd_5198872 := by exact prefixLift 5198872
  have htrace : WordTrace (prefixWord ++ tailWord_5198872) baseStart_5198872 baseEnd_5198872 := by
    simpa [prefixWord, tailWord_5198872, baseEnd_5198872] using wordTrace_append hprefix tailTrace_5198872
  have hstable : (prefixWord ++ tailWord_5198872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198872).length < 2 ^ (prefixWord ++ tailWord_5198872).sum := by decide
  have hdescent : baseEnd_5198872 < baseStart_5198872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198876 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_5198876 : Nat := 118140960795 + 5198876 * 2 ^ 59
def prefixEnd_5198876 : Nat := 4983230072969 + 3 ^ 40 * 5198876 * 2
def baseEnd_5198876 : Nat := 2669522251124106607440811

theorem tailTrace_5198876 : CollatzResearch.WordTrace tailWord_5198876 prefixEnd_5198876 2669522251124106607440811 := by
  unfold tailWord_5198876
  simp only [CollatzResearch.WordTrace]
  refine ⟨94809292756683812088396241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126412390342245082784528321 94809292756683812088396241)
  ·
    refine ⟨71106969567512859066297181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94809292756683812088396241 71106969567512859066297181)
    ·
      refine ⟨26665113587817322149861443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71106969567512859066297181 26665113587817322149861443)
      ·
        refine ⟨39997670381725983224792165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26665113587817322149861443 39997670381725983224792165)
        ·
          refine ⟨7499563196573621854648531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39997670381725983224792165 7499563196573621854648531)
          ·
            refine ⟨11249344794860432781972797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499563196573621854648531 11249344794860432781972797)
            ·
              refine ⟨4218504298072662293239799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11249344794860432781972797 4218504298072662293239799)
              ·
                refine ⟨6327756447108993439859699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218504298072662293239799 6327756447108993439859699)
                ·
                  refine ⟨9491634670663490159789549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6327756447108993439859699 9491634670663490159789549)
                  ·
                    refine ⟨3559363001498808809921081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9491634670663490159789549 3559363001498808809921081)
                    ·
                      refine ⟨2669522251124106607440811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559363001498808809921081 2669522251124106607440811)
                      ·
                        rfl

theorem cell23_5198876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_5198876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198876 prefixEnd_5198876 := by exact prefixLift 5198876
  have htrace : WordTrace (prefixWord ++ tailWord_5198876) baseStart_5198876 baseEnd_5198876 := by
    simpa [prefixWord, tailWord_5198876, baseEnd_5198876] using wordTrace_append hprefix tailTrace_5198876
  have hstable : (prefixWord ++ tailWord_5198876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198876).length < 2 ^ (prefixWord ++ tailWord_5198876).sum := by decide
  have hdescent : baseEnd_5198876 < baseStart_5198876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198902 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5198902 : Nat := 118140960795 + 5198902 * 2 ^ 59
def prefixEnd_5198902 : Nat := 4983230072969 + 3 ^ 40 * 5198902 * 2
def baseEnd_5198902 : Nat := 2669535601621123505715691

theorem tailTrace_5198902 : CollatzResearch.WordTrace tailWord_5198902 prefixEnd_5198902 2669535601621123505715691 := by
  unfold tailWord_5198902
  simp only [CollatzResearch.WordTrace]
  refine ⟨11851220863204589413577435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126413022540848953744825973 11851220863204589413577435)
  ·
    refine ⟨17776831294806884120366153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11851220863204589413577435 17776831294806884120366153)
    ·
      refine ⟨13332623471105163090274615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17776831294806884120366153 13332623471105163090274615)
      ·
        refine ⟨19998935206657744635411923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13332623471105163090274615 19998935206657744635411923)
        ·
          refine ⟨29998402809986616953117885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19998935206657744635411923 29998402809986616953117885)
          ·
            refine ⟨11249401053744981357419207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29998402809986616953117885 11249401053744981357419207)
            ·
              refine ⟨16874101580617472036128811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11249401053744981357419207 16874101580617472036128811)
              ·
                refine ⟨25311152370926208054193217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16874101580617472036128811 25311152370926208054193217)
                ·
                  refine ⟨18983364278194656040644913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25311152370926208054193217 18983364278194656040644913)
                  ·
                    refine ⟨14237523208645992030483685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18983364278194656040644913 14237523208645992030483685)
                    ·
                      refine ⟨2669535601621123505715691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14237523208645992030483685 2669535601621123505715691)
                      ·
                        rfl

theorem cell23_5198902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5198902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198902 prefixEnd_5198902 := by exact prefixLift 5198902
  have htrace : WordTrace (prefixWord ++ tailWord_5198902) baseStart_5198902 baseEnd_5198902 := by
    simpa [prefixWord, tailWord_5198902, baseEnd_5198902] using wordTrace_append hprefix tailTrace_5198902
  have hstable : (prefixWord ++ tailWord_5198902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198902).length < 2 ^ (prefixWord ++ tailWord_5198902).sum := by decide
  have hdescent : baseEnd_5198902 < baseStart_5198902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198905 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5198905 : Nat := 118140960795 + 5198905 * 2 ^ 59
def prefixEnd_5198905 : Nat := 4983230072969 + 3 ^ 40 * 5198905 * 2
def baseEnd_5198905 : Nat := 2669537142063086993978177

theorem tailTrace_5198905 : CollatzResearch.WordTrace tailWord_5198905 prefixEnd_5198905 2669537142063086993978177 := by
  unfold tailWord_5198905
  simp only [CollatzResearch.WordTrace]
  refine ⟨189619643230262562129598169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126413095486841708086398779 189619643230262562129598169)
  ·
    refine ⟨142214732422696921597198627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189619643230262562129598169 142214732422696921597198627)
    ·
      refine ⟨213322098634045382395797941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142214732422696921597198627 213322098634045382395797941)
      ·
        refine ⟨19998946746941754599606057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213322098634045382395797941 19998946746941754599606057)
        ·
          refine ⟨14999210060206315949704543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19998946746941754599606057 14999210060206315949704543)
          ·
            refine ⟨22498815090309473924556815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14999210060206315949704543 22498815090309473924556815)
            ·
              refine ⟨33748222635464210886835223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22498815090309473924556815 33748222635464210886835223)
              ·
                refine ⟨50622333953196316330252835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33748222635464210886835223 50622333953196316330252835)
                ·
                  refine ⟨75933500929794474495379253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50622333953196316330252835 75933500929794474495379253)
                  ·
                    refine ⟨7118765712168231983941805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75933500929794474495379253 7118765712168231983941805)
                    ·
                      refine ⟨2669537142063086993978177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118765712168231983941805 2669537142063086993978177)
                      ·
                        rfl

theorem cell23_5198905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5198905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198905 prefixEnd_5198905 := by exact prefixLift 5198905
  have htrace : WordTrace (prefixWord ++ tailWord_5198905) baseStart_5198905 baseEnd_5198905 := by
    simpa [prefixWord, tailWord_5198905, baseEnd_5198905] using wordTrace_append hprefix tailTrace_5198905
  have hstable : (prefixWord ++ tailWord_5198905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198905).length < 2 ^ (prefixWord ++ tailWord_5198905).sum := by decide
  have hdescent : baseEnd_5198905 < baseStart_5198905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198915 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 5, 2]
def baseStart_5198915 : Nat := 118140960795 + 5198915 * 2 ^ 59
def prefixEnd_5198915 : Nat := 4983230072969 + 3 ^ 40 * 5198915 * 2
def baseEnd_5198915 : Nat := 2669542276869631954853131

theorem tailTrace_5198915 : CollatzResearch.WordTrace tailWord_5198915 prefixEnd_5198915 2669542276869631954853131 := by
  unfold tailWord_5198915
  simp only [CollatzResearch.WordTrace]
  refine ⟨189620007960226333837462199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126413338640150889224974799 189620007960226333837462199)
  ·
    refine ⟨284430011940339500756193299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189620007960226333837462199 284430011940339500756193299)
    ·
      refine ⟨426645017910509251134289949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284430011940339500756193299 426645017910509251134289949)
      ·
        refine ⟨159991881716440969175358731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426645017910509251134289949 159991881716440969175358731)
        ·
          refine ⟨239987822574661453763038097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159991881716440969175358731 239987822574661453763038097)
          ·
            refine ⟨179990866930996090322278573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239987822574661453763038097 179990866930996090322278573)
            ·
              refine ⟨67496575099123533870854465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179990866930996090322278573 67496575099123533870854465)
              ·
                refine ⟨50622431324342650403140849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67496575099123533870854465 50622431324342650403140849)
                ·
                  refine ⟨37966823493256987802355637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50622431324342650403140849 37966823493256987802355637)
                  ·
                    refine ⟨3559389702492842606470841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37966823493256987802355637 3559389702492842606470841)
                    ·
                      refine ⟨2669542276869631954853131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559389702492842606470841 2669542276869631954853131)
                      ·
                        rfl

theorem cell23_5198915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_5198915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198915 prefixEnd_5198915 := by exact prefixLift 5198915
  have htrace : WordTrace (prefixWord ++ tailWord_5198915) baseStart_5198915 baseEnd_5198915 := by
    simpa [prefixWord, tailWord_5198915, baseEnd_5198915] using wordTrace_append hprefix tailTrace_5198915
  have hstable : (prefixWord ++ tailWord_5198915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198915).length < 2 ^ (prefixWord ++ tailWord_5198915).sum := by decide
  have hdescent : baseEnd_5198915 < baseStart_5198915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198945 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_5198945 : Nat := 118140960795 + 5198945 * 2 ^ 59
def prefixEnd_5198945 : Nat := 4983230072969 + 3 ^ 40 * 5198945 * 2
def baseEnd_5198945 : Nat := 2669557681289266837477993

theorem tailTrace_5198945 : CollatzResearch.WordTrace tailWord_5198945 prefixEnd_5198945 2669557681289266837477993 := by
  unfold tailWord_5198945
  simp only [CollatzResearch.WordTrace]
  refine ⟨189621102150117648961054289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126414068100078432640702859 189621102150117648961054289)
  ·
    refine ⟨142215826612588236720790717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189621102150117648961054289 142215826612588236720790717)
    ·
      refine ⟨53330934979720588770296519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142215826612588236720790717 53330934979720588770296519)
      ·
        refine ⟨79996402469580883155444779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53330934979720588770296519 79996402469580883155444779)
        ·
          refine ⟨119994603704371324733167169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79996402469580883155444779 119994603704371324733167169)
          ·
            refine ⟨89995952778278493549875377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119994603704371324733167169 89995952778278493549875377)
            ·
              refine ⟨67496964583708870162406533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89995952778278493549875377 67496964583708870162406533)
              ·
                refine ⟨12655680859445413155451225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67496964583708870162406533 12655680859445413155451225)
                ·
                  refine ⟨9491760644584059866588419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12655680859445413155451225 9491760644584059866588419)
                  ·
                    refine ⟨14237640966876089799882629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9491760644584059866588419 14237640966876089799882629)
                    ·
                      refine ⟨2669557681289266837477993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14237640966876089799882629 2669557681289266837477993)
                      ·
                        rfl

theorem cell23_5198945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_5198945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198945 prefixEnd_5198945 := by exact prefixLift 5198945
  have htrace : WordTrace (prefixWord ++ tailWord_5198945) baseStart_5198945 baseEnd_5198945 := by
    simpa [prefixWord, tailWord_5198945, baseEnd_5198945] using wordTrace_append hprefix tailTrace_5198945
  have hstable : (prefixWord ++ tailWord_5198945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198945).length < 2 ^ (prefixWord ++ tailWord_5198945).sum := by decide
  have hdescent : baseEnd_5198945 < baseStart_5198945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5198962 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5198962 : Nat := 118140960795 + 5198962 * 2 ^ 59
def prefixEnd_5198962 : Nat := 4983230072969 + 3 ^ 40 * 5198962 * 2
def baseEnd_5198962 : Nat := 2669566410460393270965415

theorem tailTrace_5198962 : CollatzResearch.WordTrace tailWord_5198962 prefixEnd_5198962 2669566410460393270965415 := by
  unfold tailWord_5198962
  simp only [CollatzResearch.WordTrace]
  refine ⟨47405430547764015216105785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126414481460704040576282093 47405430547764015216105785)
  ·
    refine ⟨35554072910823011412079339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47405430547764015216105785 35554072910823011412079339)
    ·
      refine ⟨53331109366234517118119009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35554072910823011412079339 53331109366234517118119009)
      ·
        refine ⟨39998332024675887838589257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53331109366234517118119009 39998332024675887838589257)
        ·
          refine ⟨29998749018506915878941943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39998332024675887838589257 29998749018506915878941943)
          ·
            refine ⟨44998123527760373818412915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29998749018506915878941943 44998123527760373818412915)
            ·
              refine ⟨67497185291640560727619373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44998123527760373818412915 67497185291640560727619373)
              ·
                refine ⟨25311444484365210272857265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67497185291640560727619373 25311444484365210272857265)
                ·
                  refine ⟨18983583363273907704642949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25311444484365210272857265 18983583363273907704642949)
                  ·
                    refine ⟨3559421880613857694620553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18983583363273907704642949 3559421880613857694620553)
                    ·
                      refine ⟨2669566410460393270965415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559421880613857694620553 2669566410460393270965415)
                      ·
                        rfl

theorem cell23_5198962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5198962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5198962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5198962 prefixEnd_5198962 := by exact prefixLift 5198962
  have htrace : WordTrace (prefixWord ++ tailWord_5198962) baseStart_5198962 baseEnd_5198962 := by
    simpa [prefixWord, tailWord_5198962, baseEnd_5198962] using wordTrace_append hprefix tailTrace_5198962
  have hstable : (prefixWord ++ tailWord_5198962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5198962).length < 2 ^ (prefixWord ++ tailWord_5198962).sum := by decide
  have hdescent : baseEnd_5198962 < baseStart_5198962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5198962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199006 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5199006 : Nat := 118140960795 + 5199006 * 2 ^ 59
def prefixEnd_5199006 : Nat := 4983230072969 + 3 ^ 40 * 5199006 * 2
def baseEnd_5199006 : Nat := 889863001203063699605071

theorem tailTrace_5199006 : CollatzResearch.WordTrace tailWord_5199006 prefixEnd_5199006 889863001203063699605071 := by
  unfold tailWord_5199006
  simp only [CollatzResearch.WordTrace]
  refine ⟨23702915875362082047378109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126415551335264437586016581 23702915875362082047378109)
  ·
    refine ⟨8888593453260780767766791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23702915875362082047378109 8888593453260780767766791)
    ·
      refine ⟨13332890179891171151650187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8888593453260780767766791 13332890179891171151650187)
      ·
        refine ⟨19999335269836756727475281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13332890179891171151650187 19999335269836756727475281)
        ·
          refine ⟨14999501452377567545606461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19999335269836756727475281 14999501452377567545606461)
          ·
            refine ⟨5624813044641587829602423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14999501452377567545606461 5624813044641587829602423)
            ·
              refine ⟨8437219566962381744403635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624813044641587829602423 8437219566962381744403635)
              ·
                refine ⟨12655829350443572616605453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437219566962381744403635 12655829350443572616605453)
                ·
                  refine ⟨4745936006416339731227045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12655829350443572616605453 4745936006416339731227045)
                  ·
                    refine ⟨889863001203063699605071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4745936006416339731227045 889863001203063699605071)
                    ·
                      rfl

theorem cell23_5199006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5199006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199006 prefixEnd_5199006 := by exact prefixLift 5199006
  have htrace : WordTrace (prefixWord ++ tailWord_5199006) baseStart_5199006 baseEnd_5199006 := by
    simpa [prefixWord, tailWord_5199006, baseEnd_5199006] using wordTrace_append hprefix tailTrace_5199006
  have hstable : (prefixWord ++ tailWord_5199006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199006).length < 2 ^ (prefixWord ++ tailWord_5199006).sum := by decide
  have hdescent : baseEnd_5199006 < baseStart_5199006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199055 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_5199055 : Nat := 118140960795 + 5199055 * 2 ^ 59
def prefixEnd_5199055 : Nat := 4983230072969 + 3 ^ 40 * 5199055 * 2
def baseEnd_5199055 : Nat := 2669614164161261407102487

theorem tailTrace_5199055 : CollatzResearch.WordTrace tailWord_5199055 prefixEnd_5199055 2669614164161261407102487 := by
  unfold tailWord_5199055
  simp only [CollatzResearch.WordTrace]
  refine ⟨189625114179719137747558619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126416742786479425165039079 189625114179719137747558619)
  ·
    refine ⟨284437671269578706621337929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189625114179719137747558619 284437671269578706621337929)
    ·
      refine ⟨213328253452184029966003447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284437671269578706621337929 213328253452184029966003447)
      ·
        refine ⟨319992380178276044949005171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213328253452184029966003447 319992380178276044949005171)
        ·
          refine ⟨479988570267414067423507757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319992380178276044949005171 479988570267414067423507757)
          ·
            refine ⟨179995713850280275283815409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 479988570267414067423507757 179995713850280275283815409)
            ·
              refine ⟨134996785387710206462861557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179995713850280275283815409 134996785387710206462861557)
              ·
                refine ⟨12655948630097831855893271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134996785387710206462861557 12655948630097831855893271)
                ·
                  refine ⟨18983922945146747783839907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12655948630097831855893271 18983922945146747783839907)
                  ·
                    refine ⟨28475884417720121675759861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18983922945146747783839907 28475884417720121675759861)
                    ·
                      refine ⟨2669614164161261407102487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28475884417720121675759861 2669614164161261407102487)
                      ·
                        rfl

theorem cell23_5199055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_5199055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199055 prefixEnd_5199055 := by exact prefixLift 5199055
  have htrace : WordTrace (prefixWord ++ tailWord_5199055) baseStart_5199055 baseEnd_5199055 := by
    simpa [prefixWord, tailWord_5199055, baseEnd_5199055] using wordTrace_append hprefix tailTrace_5199055
  have hstable : (prefixWord ++ tailWord_5199055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199055).length < 2 ^ (prefixWord ++ tailWord_5199055).sum := by decide
  have hdescent : baseEnd_5199055 < baseStart_5199055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199065 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_5199065 : Nat := 118140960795 + 5199065 * 2 ^ 59
def prefixEnd_5199065 : Nat := 4983230072969 + 3 ^ 40 * 5199065 * 2
def baseEnd_5199065 : Nat := 2669619298967806367977441

theorem tailTrace_5199065 : CollatzResearch.WordTrace tailWord_5199065 prefixEnd_5199065 2669619298967806367977441 := by
  unfold tailWord_5199065
  simp only [CollatzResearch.WordTrace]
  refine ⟨189625478909682909455422649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126416985939788606303615099 189625478909682909455422649)
  ·
    refine ⟨142219109182262182091566987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189625478909682909455422649 142219109182262182091566987)
    ·
      refine ⟨213328663773393273137350481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142219109182262182091566987 213328663773393273137350481)
      ·
        refine ⟨159996497830044954853012861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213328663773393273137350481 159996497830044954853012861)
        ·
          refine ⟨59998686686266858069879823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159996497830044954853012861 59998686686266858069879823)
          ·
            refine ⟨89998030029400287104819735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59998686686266858069879823 89998030029400287104819735)
            ·
              refine ⟨134997045044100430657229603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89998030029400287104819735 134997045044100430657229603)
              ·
                refine ⟨202495567566150645985844405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134997045044100430657229603 202495567566150645985844405)
                ·
                  refine ⟨18983959459326623061172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202495567566150645985844405 18983959459326623061172913)
                  ·
                    refine ⟨14237969594494967295879685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18983959459326623061172913 14237969594494967295879685)
                    ·
                      refine ⟨2669619298967806367977441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14237969594494967295879685 2669619298967806367977441)
                      ·
                        rfl

theorem cell23_5199065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_5199065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199065 prefixEnd_5199065 := by exact prefixLift 5199065
  have htrace : WordTrace (prefixWord ++ tailWord_5199065) baseStart_5199065 baseEnd_5199065 := by
    simpa [prefixWord, tailWord_5199065, baseEnd_5199065] using wordTrace_append hprefix tailTrace_5199065
  have hstable : (prefixWord ++ tailWord_5199065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199065).length < 2 ^ (prefixWord ++ tailWord_5199065).sum := by decide
  have hdescent : baseEnd_5199065 < baseStart_5199065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199072 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_5199072 : Nat := 118140960795 + 5199072 * 2 ^ 59
def prefixEnd_5199072 : Nat := 4983230072969 + 3 ^ 40 * 5199072 * 2
def baseEnd_5199072 : Nat := 2669622893332387840589909

theorem tailTrace_5199072 : CollatzResearch.WordTrace tailWord_5199072 prefixEnd_5199072 2669622893332387840589909 := by
  unfold tailWord_5199072
  simp only [CollatzResearch.WordTrace]
  refine ⟨94812867110328774825463735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126417156147105033100618313 94812867110328774825463735)
  ·
    refine ⟨142219300665493162238195603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94812867110328774825463735 142219300665493162238195603)
    ·
      refine ⟨213328950998239743357293405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142219300665493162238195603 213328950998239743357293405)
      ·
        refine ⟨79998356624339903758985027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213328950998239743357293405 79998356624339903758985027)
        ·
          refine ⟨119997534936509855638477541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79998356624339903758985027 119997534936509855638477541)
          ·
            refine ⟨22499537800595597932214539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119997534936509855638477541 22499537800595597932214539)
            ·
              refine ⟨33749306700893396898321809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22499537800595597932214539 33749306700893396898321809)
              ·
                refine ⟨25311980025670047673741357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33749306700893396898321809 25311980025670047673741357)
                ·
                  refine ⟨9491992509626267877653009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25311980025670047673741357 9491992509626267877653009)
                  ·
                    refine ⟨7118994382219700908239757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9491992509626267877653009 7118994382219700908239757)
                    ·
                      refine ⟨2669622893332387840589909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7118994382219700908239757 2669622893332387840589909)
                      ·
                        rfl

theorem cell23_5199072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_5199072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199072 prefixEnd_5199072 := by exact prefixLift 5199072
  have htrace : WordTrace (prefixWord ++ tailWord_5199072) baseStart_5199072 baseEnd_5199072 := by
    simpa [prefixWord, tailWord_5199072, baseEnd_5199072] using wordTrace_append hprefix tailTrace_5199072
  have hstable : (prefixWord ++ tailWord_5199072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199072).length < 2 ^ (prefixWord ++ tailWord_5199072).sum := by decide
  have hdescent : baseEnd_5199072 < baseStart_5199072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199079 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 1, 6]
def baseStart_5199079 : Nat := 118140960795 + 5199079 * 2 ^ 59
def prefixEnd_5199079 : Nat := 4983230072969 + 3 ^ 40 * 5199079 * 2
def baseEnd_5199079 : Nat := 889875495898989771067459

theorem tailTrace_5199079 : CollatzResearch.WordTrace tailWord_5199079 prefixEnd_5199079 889875495898989771067459 := by
  unfold tailWord_5199079
  simp only [CollatzResearch.WordTrace]
  refine ⟨189625989531632189846432291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126417326354421459897621527 189625989531632189846432291)
  ·
    refine ⟨284438984297448284769648437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189625989531632189846432291 284438984297448284769648437)
    ·
      refine ⟨26666154777885776697154541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284438984297448284769648437 26666154777885776697154541)
      ·
        refine ⟨9999808041707166261432953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26666154777885776697154541 9999808041707166261432953)
        ·
          refine ⟨7499856031280374696074715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9999808041707166261432953 7499856031280374696074715)
          ·
            refine ⟨11249784046920562044112073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499856031280374696074715 11249784046920562044112073)
            ·
              refine ⟨8437338035190421533084055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11249784046920562044112073 8437338035190421533084055)
              ·
                refine ⟨12656007052785632299626083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437338035190421533084055 12656007052785632299626083)
                ·
                  refine ⟨18984010579178448449439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12656007052785632299626083 18984010579178448449439125)
                  ·
                    refine ⟨889875495898989771067459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18984010579178448449439125 889875495898989771067459)
                    ·
                      rfl

theorem cell23_5199079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_5199079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199079 prefixEnd_5199079 := by exact prefixLift 5199079
  have htrace : WordTrace (prefixWord ++ tailWord_5199079) baseStart_5199079 baseEnd_5199079 := by
    simpa [prefixWord, tailWord_5199079, baseEnd_5199079] using wordTrace_append hprefix tailTrace_5199079
  have hstable : (prefixWord ++ tailWord_5199079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199079).length < 2 ^ (prefixWord ++ tailWord_5199079).sum := by decide
  have hdescent : baseEnd_5199079 < baseStart_5199079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199082 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5199082 : Nat := 118140960795 + 5199082 * 2 ^ 59
def prefixEnd_5199082 : Nat := 4983230072969 + 3 ^ 40 * 5199082 * 2
def baseEnd_5199082 : Nat := 2669628028138932801464863

theorem tailTrace_5199082 : CollatzResearch.WordTrace tailWord_5199082 prefixEnd_5199082 2669628028138932801464863 := by
  unfold tailWord_5199082
  simp only [CollatzResearch.WordTrace]
  refine ⟨47406524737655330339697875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126417399300414214239194333 47406524737655330339697875)
  ·
    refine ⟨71109787106482995509546813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47406524737655330339697875 71109787106482995509546813)
    ·
      refine ⟨26666170164931123316080055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71109787106482995509546813 26666170164931123316080055)
      ·
        refine ⟨39999255247396684974120083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26666170164931123316080055 39999255247396684974120083)
        ·
          refine ⟨59998882871095027461180125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39999255247396684974120083 59998882871095027461180125)
          ·
            refine ⟨22499581076660635297942547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59998882871095027461180125 22499581076660635297942547)
            ·
              refine ⟨33749371614990952946913821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22499581076660635297942547 33749371614990952946913821)
              ·
                refine ⟨12656014355621607355092683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33749371614990952946913821 12656014355621607355092683)
                ·
                  refine ⟨18984021533432411032639025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12656014355621607355092683 18984021533432411032639025)
                  ·
                    refine ⟨14238016150074308274479269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18984021533432411032639025 14238016150074308274479269)
                    ·
                      refine ⟨2669628028138932801464863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14238016150074308274479269 2669628028138932801464863)
                      ·
                        rfl

theorem cell23_5199082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5199082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199082 prefixEnd_5199082 := by exact prefixLift 5199082
  have htrace : WordTrace (prefixWord ++ tailWord_5199082) baseStart_5199082 baseEnd_5199082 := by
    simpa [prefixWord, tailWord_5199082, baseEnd_5199082] using wordTrace_append hprefix tailTrace_5199082
  have hstable : (prefixWord ++ tailWord_5199082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199082).length < 2 ^ (prefixWord ++ tailWord_5199082).sum := by decide
  have hdescent : baseEnd_5199082 < baseStart_5199082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199103 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 1, 2, 2]
def baseStart_5199103 : Nat := 118140960795 + 5199103 * 2 ^ 59
def prefixEnd_5199103 : Nat := 4983230072969 + 3 ^ 40 * 5199103 * 2
def baseEnd_5199103 : Nat := 2669638811232677219302267

theorem tailTrace_5199103 : CollatzResearch.WordTrace tailWord_5199103 prefixEnd_5199103 2669638811232677219302267 := by
  unfold tailWord_5199103
  simp only [CollatzResearch.WordTrace]
  refine ⟨189626864883545241945305963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126417909922363494630203975 189626864883545241945305963)
  ·
    refine ⟨284440297325317862917958945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189626864883545241945305963 284440297325317862917958945)
    ·
      refine ⟨213330222993988397188469209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284440297325317862917958945 213330222993988397188469209)
      ·
        refine ⟨159997667245491297891351907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213330222993988397188469209 159997667245491297891351907)
        ·
          refine ⟨239996500868236946837027861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159997667245491297891351907 239996500868236946837027861)
          ·
            refine ⟨11249835978198606882985681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 239996500868236946837027861 11249835978198606882985681)
            ·
              refine ⟨8437376983648955162239261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11249835978198606882985681 8437376983648955162239261)
              ·
                refine ⟨3164016368868358185839723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8437376983648955162239261 3164016368868358185839723)
                ·
                  refine ⟨4746024553302537278759585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164016368868358185839723 4746024553302537278759585)
                  ·
                    refine ⟨3559518414976902959069689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746024553302537278759585 3559518414976902959069689)
                    ·
                      refine ⟨2669638811232677219302267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559518414976902959069689 2669638811232677219302267)
                      ·
                        rfl

theorem cell23_5199103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_5199103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199103 prefixEnd_5199103 := by exact prefixLift 5199103
  have htrace : WordTrace (prefixWord ++ tailWord_5199103) baseStart_5199103 baseEnd_5199103 := by
    simpa [prefixWord, tailWord_5199103, baseEnd_5199103] using wordTrace_append hprefix tailTrace_5199103
  have hstable : (prefixWord ++ tailWord_5199103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199103).length < 2 ^ (prefixWord ++ tailWord_5199103).sum := by decide
  have hdescent : baseEnd_5199103 < baseStart_5199103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199136 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5199136 : Nat := 118140960795 + 5199136 * 2 ^ 59
def prefixEnd_5199136 : Nat := 4983230072969 + 3 ^ 40 * 5199136 * 2
def baseEnd_5199136 : Nat := 2669655756094275590189615

theorem tailTrace_5199136 : CollatzResearch.WordTrace tailWord_5199136 prefixEnd_5199136 2669655756094275590189615 := by
  unfold tailWord_5199136
  simp only [CollatzResearch.WordTrace]
  refine ⟨94814034246212844290628631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126418712328283792387504841 94814034246212844290628631)
  ·
    refine ⟨142221051369319266435942947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94814034246212844290628631 142221051369319266435942947)
    ·
      refine ⟨213331577053978899653914421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142221051369319266435942947 213331577053978899653914421)
      ·
        refine ⟨19999835348810521842554477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213331577053978899653914421 19999835348810521842554477)
        ·
          refine ⟨7499938255803945690957929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19999835348810521842554477 7499938255803945690957929)
          ·
            refine ⟨5624953691852959268218447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7499938255803945690957929 5624953691852959268218447)
            ·
              refine ⟨8437430537779438902327671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624953691852959268218447 8437430537779438902327671)
              ·
                refine ⟨12656145806669158353491507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437430537779438902327671 12656145806669158353491507)
                ·
                  refine ⟨18984218710003737530237261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12656145806669158353491507 18984218710003737530237261)
                  ·
                    refine ⟨7119082016251401573838973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18984218710003737530237261 7119082016251401573838973)
                    ·
                      refine ⟨2669655756094275590189615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119082016251401573838973 2669655756094275590189615)
                      ·
                        rfl

theorem cell23_5199136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5199136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199136 prefixEnd_5199136 := by exact prefixLift 5199136
  have htrace : WordTrace (prefixWord ++ tailWord_5199136) baseStart_5199136 baseEnd_5199136 := by
    simpa [prefixWord, tailWord_5199136, baseEnd_5199136] using wordTrace_append hprefix tailTrace_5199136
  have hstable : (prefixWord ++ tailWord_5199136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199136).length < 2 ^ (prefixWord ++ tailWord_5199136).sum := by decide
  have hdescent : baseEnd_5199136 < baseStart_5199136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199149 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5199149 : Nat := 118140960795 + 5199149 * 2 ^ 59
def prefixEnd_5199149 : Nat := 4983230072969 + 3 ^ 40 * 5199149 * 2
def baseEnd_5199149 : Nat := 2669662431342784039327055

theorem tailTrace_5199149 : CollatzResearch.WordTrace tailWord_5199149 prefixEnd_5199149 2669662431342784039327055 := by
  unfold tailWord_5199149
  simp only [CollatzResearch.WordTrace]
  refine ⟨189628542641378591801480501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126419028427585727867653667 189628542641378591801480501)
  ·
    refine ⟨17777675872629242981388797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189628542641378591801480501 17777675872629242981388797)
    ·
      refine ⟨6666628452235966118020799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17777675872629242981388797 6666628452235966118020799)
      ·
        refine ⟨9999942678353949177031199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666628452235966118020799 9999942678353949177031199)
        ·
          refine ⟨14999914017530923765546799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9999942678353949177031199 14999914017530923765546799)
          ·
            refine ⟨22499871026296385648320199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14999914017530923765546799 22499871026296385648320199)
            ·
              refine ⟨33749806539444578472480299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22499871026296385648320199 33749806539444578472480299)
              ·
                refine ⟨50624709809166867708720449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33749806539444578472480299 50624709809166867708720449)
                ·
                  refine ⟨37968532356875150781540337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50624709809166867708720449 37968532356875150781540337)
                  ·
                    refine ⟨28476399267656363086155253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37968532356875150781540337 28476399267656363086155253)
                    ·
                      refine ⟨2669662431342784039327055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28476399267656363086155253 2669662431342784039327055)
                      ·
                        rfl

theorem cell23_5199149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5199149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199149 prefixEnd_5199149 := by exact prefixLift 5199149
  have htrace : WordTrace (prefixWord ++ tailWord_5199149) baseStart_5199149 baseEnd_5199149 := by
    simpa [prefixWord, tailWord_5199149, baseEnd_5199149] using wordTrace_append hprefix tailTrace_5199149
  have hstable : (prefixWord ++ tailWord_5199149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199149).length < 2 ^ (prefixWord ++ tailWord_5199149).sum := by decide
  have hdescent : baseEnd_5199149 < baseStart_5199149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199162 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_5199162 : Nat := 118140960795 + 5199162 * 2 ^ 59
def prefixEnd_5199162 : Nat := 4983230072969 + 3 ^ 40 * 5199162 * 2
def baseEnd_5199162 : Nat := 2669669106591292488464495

theorem tailTrace_5199162 : CollatzResearch.WordTrace tailWord_5199162 prefixEnd_5199162 2669669106591292488464495 := by
  unfold tailWord_5199162
  simp only [CollatzResearch.WordTrace]
  refine ⟨47407254197582873755425935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126419344526887663347802493 47407254197582873755425935)
  ·
    refine ⟨71110881296374310633138903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47407254197582873755425935 71110881296374310633138903)
    ·
      refine ⟨106666321944561465949708355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71110881296374310633138903 106666321944561465949708355)
      ·
        refine ⟨159999482916842198924562533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106666321944561465949708355 159999482916842198924562533)
        ·
          refine ⟨29999903046907912298355475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159999482916842198924562533 29999903046907912298355475)
          ·
            refine ⟨44999854570361868447533213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29999903046907912298355475 44999854570361868447533213)
            ·
              refine ⟨16874945463885700667824955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44999854570361868447533213 16874945463885700667824955)
              ·
                refine ⟨25312418195828551001737433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16874945463885700667824955 25312418195828551001737433)
                ·
                  refine ⟨18984313646871413251303075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25312418195828551001737433 18984313646871413251303075)
                  ·
                    refine ⟨28476470470307119876954613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18984313646871413251303075 28476470470307119876954613)
                    ·
                      refine ⟨2669669106591292488464495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28476470470307119876954613 2669669106591292488464495)
                      ·
                        rfl

theorem cell23_5199162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_5199162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199162 prefixEnd_5199162 := by exact prefixLift 5199162
  have htrace : WordTrace (prefixWord ++ tailWord_5199162) baseStart_5199162 baseEnd_5199162 := by
    simpa [prefixWord, tailWord_5199162, baseEnd_5199162] using wordTrace_append hprefix tailTrace_5199162
  have hstable : (prefixWord ++ tailWord_5199162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199162).length < 2 ^ (prefixWord ++ tailWord_5199162).sum := by decide
  have hdescent : baseEnd_5199162 < baseStart_5199162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199176 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_5199176 : Nat := 118140960795 + 5199176 * 2 ^ 59
def prefixEnd_5199176 : Nat := 4983230072969 + 3 ^ 40 * 5199176 * 2
def baseEnd_5199176 : Nat := 2669676295320455433689431

theorem tailTrace_5199176 : CollatzResearch.WordTrace tailWord_5199176 prefixEnd_5199176 2669676295320455433689431 := by
  unfold tailWord_5199176
  simp only [CollatzResearch.WordTrace]
  refine ⟨94814763706140387706356691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126419684941520516941808921 94814763706140387706356691)
  ·
    refine ⟨142222145559210581559535037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94814763706140387706356691 142222145559210581559535037)
    ·
      refine ⟨53333304584703968084825639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142222145559210581559535037 53333304584703968084825639)
      ·
        refine ⟨79999956877055952127238459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53333304584703968084825639 79999956877055952127238459)
        ·
          refine ⟨119999935315583928190857689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79999956877055952127238459 119999935315583928190857689)
          ·
            refine ⟨89999951486687946143143267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119999935315583928190857689 89999951486687946143143267)
            ·
              refine ⟨134999927230031919214714901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89999951486687946143143267 134999927230031919214714901)
              ·
                refine ⟨6328121588907746213189761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134999927230031919214714901 6328121588907746213189761)
                ·
                  refine ⟨4746091191680809659892321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6328121588907746213189761 4746091191680809659892321)
                  ·
                    refine ⟨3559568393760607244919241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746091191680809659892321 3559568393760607244919241)
                    ·
                      refine ⟨2669676295320455433689431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559568393760607244919241 2669676295320455433689431)
                      ·
                        rfl

theorem cell23_5199176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_5199176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199176 prefixEnd_5199176 := by exact prefixLift 5199176
  have htrace : WordTrace (prefixWord ++ tailWord_5199176) baseStart_5199176 baseEnd_5199176 := by
    simpa [prefixWord, tailWord_5199176, baseEnd_5199176] using wordTrace_append hprefix tailTrace_5199176
  have hstable : (prefixWord ++ tailWord_5199176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199176).length < 2 ^ (prefixWord ++ tailWord_5199176).sum := by decide
  have hdescent : baseEnd_5199176 < baseStart_5199176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199192 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_5199192 : Nat := 118140960795 + 5199192 * 2 ^ 59
def prefixEnd_5199192 : Nat := 4983230072969 + 3 ^ 40 * 5199192 * 2
def baseEnd_5199192 : Nat := 2669684511010927371089357

theorem tailTrace_5199192 : CollatzResearch.WordTrace tailWord_5199192 prefixEnd_5199192 2669684511010927371089357 := by
  unfold tailWord_5199192
  simp only [CollatzResearch.WordTrace]
  refine ⟨94815055490111405072647915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126420073986815206763530553 94815055490111405072647915)
  ·
    refine ⟨142222583235167107608971873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94815055490111405072647915 142222583235167107608971873)
    ·
      refine ⟨106666937426375330706728905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142222583235167107608971873 106666937426375330706728905)
      ·
        refine ⟨80000203069781498030046679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106666937426375330706728905 80000203069781498030046679)
        ·
          refine ⟨120000304604672247045070019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80000203069781498030046679 120000304604672247045070019)
          ·
            refine ⟨180000456907008370567605029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120000304604672247045070019 180000456907008370567605029)
            ·
              refine ⟨33750085670064069481425943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180000456907008370567605029 33750085670064069481425943)
              ·
                refine ⟨50625128505096104222138915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33750085670064069481425943 50625128505096104222138915)
                ·
                  refine ⟨75937692757644156333208373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50625128505096104222138915 75937692757644156333208373)
                  ·
                    refine ⟨7119158696029139656238285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75937692757644156333208373 7119158696029139656238285)
                    ·
                      refine ⟨2669684511010927371089357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119158696029139656238285 2669684511010927371089357)
                      ·
                        rfl

theorem cell23_5199192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_5199192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199192 prefixEnd_5199192 := by exact prefixLift 5199192
  have htrace : WordTrace (prefixWord ++ tailWord_5199192) baseStart_5199192 baseEnd_5199192 := by
    simpa [prefixWord, tailWord_5199192, baseEnd_5199192] using wordTrace_append hprefix tailTrace_5199192
  have hstable : (prefixWord ++ tailWord_5199192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199192).length < 2 ^ (prefixWord ++ tailWord_5199192).sum := by decide
  have hdescent : baseEnd_5199192 < baseStart_5199192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199193 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 2, 2, 2]
def baseStart_5199193 : Nat := 118140960795 + 5199193 * 2 ^ 59
def prefixEnd_5199193 : Nat := 4983230072969 + 3 ^ 40 * 5199193 * 2
def baseEnd_5199193 : Nat := 2669685024491581867176853

theorem tailTrace_5199193 : CollatzResearch.WordTrace tailWord_5199193 prefixEnd_5199193 2669685024491581867176853 := by
  unfold tailWord_5199193
  simp only [CollatzResearch.WordTrace]
  refine ⟨189630147453219187316082233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126420098302146124877388155 189630147453219187316082233)
  ·
    refine ⟨142222610589914390487061675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189630147453219187316082233 142222610589914390487061675)
    ·
      refine ⟨213333915884871585730592513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142222610589914390487061675 213333915884871585730592513)
      ·
        refine ⟨160000436913653689297944385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213333915884871585730592513 160000436913653689297944385)
        ·
          refine ⟨120000327685240266973458289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160000436913653689297944385 120000327685240266973458289)
          ·
            refine ⟨90000245763930200230093717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120000327685240266973458289 90000245763930200230093717)
            ·
              refine ⟨4218761520184228135785643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90000245763930200230093717 4218761520184228135785643)
              ·
                refine ⟨6328142280276342203678465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218761520184228135785643 6328142280276342203678465)
                ·
                  refine ⟨4746106710207256652758849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6328142280276342203678465 4746106710207256652758849)
                  ·
                    refine ⟨3559580032655442489569137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746106710207256652758849 3559580032655442489569137)
                    ·
                      refine ⟨2669685024491581867176853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559580032655442489569137 2669685024491581867176853)
                      ·
                        rfl

theorem cell23_5199193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_5199193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199193 prefixEnd_5199193 := by exact prefixLift 5199193
  have htrace : WordTrace (prefixWord ++ tailWord_5199193) baseStart_5199193 baseEnd_5199193 := by
    simpa [prefixWord, tailWord_5199193, baseEnd_5199193] using wordTrace_append hprefix tailTrace_5199193
  have hstable : (prefixWord ++ tailWord_5199193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199193).length < 2 ^ (prefixWord ++ tailWord_5199193).sum := by decide
  have hdescent : baseEnd_5199193 < baseStart_5199193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199249 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_5199249 : Nat := 118140960795 + 5199249 * 2 ^ 59
def prefixEnd_5199249 : Nat := 4983230072969 + 3 ^ 40 * 5199249 * 2
def baseEnd_5199249 : Nat := 2669713779408233648076595

theorem tailTrace_5199249 : CollatzResearch.WordTrace tailWord_5199249 prefixEnd_5199249 2669713779408233648076595 := by
  unfold tailWord_5199249
  simp only [CollatzResearch.WordTrace]
  refine ⟨189632189941016308880120801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126421459960677539253413867 189632189941016308880120801)
  ·
    refine ⟨142224142455762231660090601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189632189941016308880120801 142224142455762231660090601)
    ·
      refine ⟨106668106841821673745067951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142224142455762231660090601 106668106841821673745067951)
      ·
        refine ⟨160002160262732510617601927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106668106841821673745067951 160002160262732510617601927)
        ·
          refine ⟨240003240394098765926402891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160002160262732510617601927 240003240394098765926402891)
          ·
            refine ⟨360004860591148148889604337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240003240394098765926402891 360004860591148148889604337)
            ·
              refine ⟨270003645443361111667203253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360004860591148148889604337 270003645443361111667203253)
              ·
                refine ⟨25312841760315104218800305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270003645443361111667203253 25312841760315104218800305)
                ·
                  refine ⟨18984631320236328164100229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25312841760315104218800305 18984631320236328164100229)
                  ·
                    refine ⟨3559618372544311530768793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18984631320236328164100229 3559618372544311530768793)
                    ·
                      refine ⟨2669713779408233648076595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559618372544311530768793 2669713779408233648076595)
                      ·
                        rfl

theorem cell23_5199249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_5199249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199249 prefixEnd_5199249 := by exact prefixLift 5199249
  have htrace : WordTrace (prefixWord ++ tailWord_5199249) baseStart_5199249 baseEnd_5199249 := by
    simpa [prefixWord, tailWord_5199249, baseEnd_5199249] using wordTrace_append hprefix tailTrace_5199249
  have hstable : (prefixWord ++ tailWord_5199249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199249).length < 2 ^ (prefixWord ++ tailWord_5199249).sum := by decide
  have hdescent : baseEnd_5199249 < baseStart_5199249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199266 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_5199266 : Nat := 118140960795 + 5199266 * 2 ^ 59
def prefixEnd_5199266 : Nat := 4983230072969 + 3 ^ 40 * 5199266 * 2
def baseEnd_5199266 : Nat := 2669722508579360081564017

theorem tailTrace_5199266 : CollatzResearch.WordTrace tailWord_5199266 prefixEnd_5199266 2669722508579360081564017 := by
  unfold tailWord_5199266
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408202495488680195872413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126421873321303147188993101 47408202495488680195872413)
  ·
    refine ⟨17778075935808255073452155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47408202495488680195872413 17778075935808255073452155)
    ·
      refine ⟨26667113903712382610178233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17778075935808255073452155 26667113903712382610178233)
      ·
        refine ⟨20000335427784286957633675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26667113903712382610178233 20000335427784286957633675)
        ·
          refine ⟨30000503141676430436450513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20000335427784286957633675 30000503141676430436450513)
          ·
            refine ⟨22500377356257322827337885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30000503141676430436450513 22500377356257322827337885)
            ·
              refine ⟨8437641508596496060251707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22500377356257322827337885 8437641508596496060251707)
              ·
                refine ⟨12656462262894744090377561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437641508596496060251707 12656462262894744090377561)
                ·
                  refine ⟨9492346697171058067783171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12656462262894744090377561 9492346697171058067783171)
                  ·
                    refine ⟨14238520045756587101674757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9492346697171058067783171 14238520045756587101674757)
                    ·
                      refine ⟨2669722508579360081564017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14238520045756587101674757 2669722508579360081564017)
                      ·
                        rfl

theorem cell23_5199266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_5199266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199266 prefixEnd_5199266 := by exact prefixLift 5199266
  have htrace : WordTrace (prefixWord ++ tailWord_5199266) baseStart_5199266 baseEnd_5199266 := by
    simpa [prefixWord, tailWord_5199266, baseEnd_5199266] using wordTrace_append hprefix tailTrace_5199266
  have hstable : (prefixWord ++ tailWord_5199266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199266).length < 2 ^ (prefixWord ++ tailWord_5199266).sum := by decide
  have hdescent : baseEnd_5199266 < baseStart_5199266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199269 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_5199269 : Nat := 118140960795 + 5199269 * 2 ^ 59
def prefixEnd_5199269 : Nat := 4983230072969 + 3 ^ 40 * 5199269 * 2
def baseEnd_5199269 : Nat := 2669724049021323569826503

theorem tailTrace_5199269 : CollatzResearch.WordTrace tailWord_5199269 prefixEnd_5199269 2669724049021323569826503 := by
  unfold tailWord_5199269
  simp only [CollatzResearch.WordTrace]
  refine ⟨189632919400943852295848861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126421946267295901530565907 189632919400943852295848861)
  ·
    refine ⟨71112344775353944610943323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189632919400943852295848861 71112344775353944610943323)
    ·
      refine ⟨106668517163030916916414985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71112344775353944610943323 106668517163030916916414985)
      ·
        refine ⟨80001387872273187687311239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106668517163030916916414985 80001387872273187687311239)
        ·
          refine ⟨120002081808409781530966859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80001387872273187687311239 120002081808409781530966859)
          ·
            refine ⟨180003122712614672296450289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120002081808409781530966859 180003122712614672296450289)
            ·
              refine ⟨135002342034461004222337717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180003122712614672296450289 135002342034461004222337717)
              ·
                refine ⟨12656469565730719145844161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135002342034461004222337717 12656469565730719145844161)
                ·
                  refine ⟨9492352174298039359383121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12656469565730719145844161 9492352174298039359383121)
                  ·
                    refine ⟨7119264130723529519537341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9492352174298039359383121 7119264130723529519537341)
                    ·
                      refine ⟨2669724049021323569826503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119264130723529519537341 2669724049021323569826503)
                      ·
                        rfl

theorem cell23_5199269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_5199269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199269 prefixEnd_5199269 := by exact prefixLift 5199269
  have htrace : WordTrace (prefixWord ++ tailWord_5199269) baseStart_5199269 baseEnd_5199269 := by
    simpa [prefixWord, tailWord_5199269, baseEnd_5199269] using wordTrace_append hprefix tailTrace_5199269
  have hstable : (prefixWord ++ tailWord_5199269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199269).length < 2 ^ (prefixWord ++ tailWord_5199269).sum := by decide
  have hdescent : baseEnd_5199269 < baseStart_5199269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199276 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_5199276 : Nat := 118140960795 + 5199276 * 2 ^ 59
def prefixEnd_5199276 : Nat := 4983230072969 + 3 ^ 40 * 5199276 * 2
def baseEnd_5199276 : Nat := 889909214461968347479657

theorem tailTrace_5199276 : CollatzResearch.WordTrace tailWord_5199276 prefixEnd_5199276 889909214461968347479657 := by
  unfold tailWord_5199276
  simp only [CollatzResearch.WordTrace]
  refine ⟨94816587355959246245676841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126422116474612328327569121 94816587355959246245676841)
  ·
    refine ⟨71112440516969434684257631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94816587355959246245676841 71112440516969434684257631)
    ·
      refine ⟨106668660775454152026386447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71112440516969434684257631 106668660775454152026386447)
      ·
        refine ⟨160002991163181228039579671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106668660775454152026386447 160002991163181228039579671)
        ·
          refine ⟨240004486744771842059369507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160002991163181228039579671 240004486744771842059369507)
          ·
            refine ⟨360006730117157763089054261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240004486744771842059369507 360006730117157763089054261)
            ·
              refine ⟨33750630948483540289598837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360006730117157763089054261 33750630948483540289598837)
              ·
                refine ⟨3164121651420331902149891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33750630948483540289598837 3164121651420331902149891)
                ·
                  refine ⟨4746182477130497853224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164121651420331902149891 4746182477130497853224837)
                  ·
                    refine ⟨889909214461968347479657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746182477130497853224837 889909214461968347479657)
                    ·
                      rfl

theorem cell23_5199276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_5199276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199276 prefixEnd_5199276 := by exact prefixLift 5199276
  have htrace : WordTrace (prefixWord ++ tailWord_5199276) baseStart_5199276 baseEnd_5199276 := by
    simpa [prefixWord, tailWord_5199276, baseEnd_5199276] using wordTrace_append hprefix tailTrace_5199276
  have hstable : (prefixWord ++ tailWord_5199276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199276).length < 2 ^ (prefixWord ++ tailWord_5199276).sum := by decide
  have hdescent : baseEnd_5199276 < baseStart_5199276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199289 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 8]
def baseStart_5199289 : Nat := 118140960795 + 5199289 * 2 ^ 59
def prefixEnd_5199289 : Nat := 4983230072969 + 3 ^ 40 * 5199289 * 2
def baseEnd_5199289 : Nat := 296637146514934832397379

theorem tailTrace_5199289 : CollatzResearch.WordTrace tailWord_5199289 prefixEnd_5199289 296637146514934832397379 := by
  unfold tailWord_5199289
  simp only [CollatzResearch.WordTrace]
  refine ⟨189633648860871395711576921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126422432573914263807717947 189633648860871395711576921)
  ·
    refine ⟨142225236645653546783682691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189633648860871395711576921 142225236645653546783682691)
    ·
      refine ⟨213337854968480320175524037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142225236645653546783682691 213337854968480320175524037)
      ·
        refine ⟨40000847806590060032910757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213337854968480320175524037 40000847806590060032910757)
        ·
          refine ⟨7500158963735636256170767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40000847806590060032910757 7500158963735636256170767)
          ·
            refine ⟨11250238445603454384256151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500158963735636256170767 11250238445603454384256151)
            ·
              refine ⟨16875357668405181576384227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11250238445603454384256151 16875357668405181576384227)
              ·
                refine ⟨25313036502607772364576341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16875357668405181576384227 25313036502607772364576341)
                ·
                  refine ⟨296637146514934832397379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25313036502607772364576341 296637146514934832397379)
                  ·
                    rfl

theorem cell23_5199289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_5199289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199289 prefixEnd_5199289 := by exact prefixLift 5199289
  have htrace : WordTrace (prefixWord ++ tailWord_5199289) baseStart_5199289 baseEnd_5199289 := by
    simpa [prefixWord, tailWord_5199289, baseEnd_5199289] using wordTrace_append hprefix tailTrace_5199289
  have hstable : (prefixWord ++ tailWord_5199289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199289).length < 2 ^ (prefixWord ++ tailWord_5199289).sum := by decide
  have hdescent : baseEnd_5199289 < baseStart_5199289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199306 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_5199306 : Nat := 118140960795 + 5199306 * 2 ^ 59
def prefixEnd_5199306 : Nat := 4983230072969 + 3 ^ 40 * 5199306 * 2
def baseEnd_5199306 : Nat := 296638116422837769451537

theorem tailTrace_5199306 : CollatzResearch.WordTrace tailWord_5199306 prefixEnd_5199306 296638116422837769451537 := by
  unfold tailWord_5199306
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408567225452451903736443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126422845934539871743297181 47408567225452451903736443)
  ·
    refine ⟨71112850838178677855604665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47408567225452451903736443 71112850838178677855604665)
    ·
      refine ⟨53334638128634008391703499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71112850838178677855604665 53334638128634008391703499)
      ·
        refine ⟨80001957192951012587555249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53334638128634008391703499 80001957192951012587555249)
        ·
          refine ⟨60001467894713259440666437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80001957192951012587555249 60001467894713259440666437)
          ·
            refine ⟨11250275230258736145124957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60001467894713259440666437 11250275230258736145124957)
            ·
              refine ⟨4218853211347026054421859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11250275230258736145124957 4218853211347026054421859)
              ·
                refine ⟨6328279817020539081632789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218853211347026054421859 6328279817020539081632789)
                ·
                  refine ⟨296638116422837769451537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6328279817020539081632789 296638116422837769451537)
                  ·
                    rfl

theorem cell23_5199306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_5199306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199306 prefixEnd_5199306 := by exact prefixLift 5199306
  have htrace : WordTrace (prefixWord ++ tailWord_5199306) baseStart_5199306 baseEnd_5199306 := by
    simpa [prefixWord, tailWord_5199306, baseEnd_5199306] using wordTrace_append hprefix tailTrace_5199306
  have hstable : (prefixWord ++ tailWord_5199306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199306).length < 2 ^ (prefixWord ++ tailWord_5199306).sum := by decide
  have hdescent : baseEnd_5199306 < baseStart_5199306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199350 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5199350 : Nat := 118140960795 + 5199350 * 2 ^ 59
def prefixEnd_5199350 : Nat := 4983230072969 + 3 ^ 40 * 5199350 * 2
def baseEnd_5199350 : Nat := 2669765640954337752913631

theorem tailTrace_5199350 : CollatzResearch.WordTrace tailWord_5199350 prefixEnd_5199350 2669765640954337752913631 := by
  unfold tailWord_5199350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852242107103150195596719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126423915809100268753031669 11852242107103150195596719)
  ·
    refine ⟨17778363160654725293395079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11852242107103150195596719 17778363160654725293395079)
    ·
      refine ⟨26667544740982087940092619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17778363160654725293395079 26667544740982087940092619)
      ·
        refine ⟨40001317111473131910138929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26667544740982087940092619 40001317111473131910138929)
        ·
          refine ⟨30000987833604848932604197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40001317111473131910138929 30000987833604848932604197)
          ·
            refine ⟨5625185218800909174863287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30000987833604848932604197 5625185218800909174863287)
            ·
              refine ⟨8437777828201363762294931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625185218800909174863287 8437777828201363762294931)
              ·
                refine ⟨12656666742302045643442397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437777828201363762294931 12656666742302045643442397)
                ·
                  refine ⟨4746250028363267116290899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12656666742302045643442397 4746250028363267116290899)
                  ·
                    refine ⟨7119375042544900674436349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746250028363267116290899 7119375042544900674436349)
                    ·
                      refine ⟨2669765640954337752913631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119375042544900674436349 2669765640954337752913631)
                      ·
                        rfl

theorem cell23_5199350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5199350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199350 prefixEnd_5199350 := by exact prefixLift 5199350
  have htrace : WordTrace (prefixWord ++ tailWord_5199350) baseStart_5199350 baseEnd_5199350 := by
    simpa [prefixWord, tailWord_5199350, baseEnd_5199350] using wordTrace_append hprefix tailTrace_5199350
  have hstable : (prefixWord ++ tailWord_5199350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199350).length < 2 ^ (prefixWord ++ tailWord_5199350).sum := by decide
  have hdescent : baseEnd_5199350 < baseStart_5199350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199369 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_5199369 : Nat := 118140960795 + 5199369 * 2 ^ 59
def prefixEnd_5199369 : Nat := 4983230072969 + 3 ^ 40 * 5199369 * 2
def baseEnd_5199369 : Nat := 2669775397086773178576043

theorem tailTrace_5199369 : CollatzResearch.WordTrace tailWord_5199369 prefixEnd_5199369 2669775397086773178576043 := by
  unfold tailWord_5199369
  simp only [CollatzResearch.WordTrace]
  refine ⟨189636566700581569374489161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126424377800387712916326107 189636566700581569374489161)
  ·
    refine ⟨142227425025436177030866871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189636566700581569374489161 142227425025436177030866871)
    ·
      refine ⟨213341137538154265546300307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142227425025436177030866871 213341137538154265546300307)
      ·
        refine ⟨320011706307231398319450461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213341137538154265546300307 320011706307231398319450461)
        ·
          refine ⟨120004389865211774369793923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320011706307231398319450461 120004389865211774369793923)
          ·
            refine ⟨180006584797817661554690885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120004389865211774369793923 180006584797817661554690885)
            ·
              refine ⟨33751234649590811541504541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180006584797817661554690885 33751234649590811541504541)
              ·
                refine ⟨12656712993596554328064203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33751234649590811541504541 12656712993596554328064203)
                ·
                  refine ⟨18985069490394831492096305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12656712993596554328064203 18985069490394831492096305)
                  ·
                    refine ⟨14238802117796123619072229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18985069490394831492096305 14238802117796123619072229)
                    ·
                      refine ⟨2669775397086773178576043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14238802117796123619072229 2669775397086773178576043)
                      ·
                        rfl

theorem cell23_5199369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_5199369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199369 prefixEnd_5199369 := by exact prefixLift 5199369
  have htrace : WordTrace (prefixWord ++ tailWord_5199369) baseStart_5199369 baseEnd_5199369 := by
    simpa [prefixWord, tailWord_5199369, baseEnd_5199369] using wordTrace_append hprefix tailTrace_5199369
  have hstable : (prefixWord ++ tailWord_5199369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199369).length < 2 ^ (prefixWord ++ tailWord_5199369).sum := by decide
  have hdescent : baseEnd_5199369 < baseStart_5199369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199400 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5199400 : Nat := 118140960795 + 5199400 * 2 ^ 59
def prefixEnd_5199400 : Nat := 4983230072969 + 3 ^ 40 * 5199400 * 2
def baseEnd_5199400 : Nat := 889930438329020852429467

theorem tailTrace_5199400 : CollatzResearch.WordTrace tailWord_5199400 prefixEnd_5199400 889930438329020852429467 := by
  unfold tailWord_5199400
  simp only [CollatzResearch.WordTrace]
  refine ⟨94818848681734630834433827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126425131575646174445911769 94818848681734630834433827)
  ·
    refine ⟨142228273022601946251650741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94818848681734630834433827 142228273022601946251650741)
    ·
      refine ⟨13333900595868932461092257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142228273022601946251650741 13333900595868932461092257)
      ·
        refine ⟨10000425446901699345819193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13333900595868932461092257 10000425446901699345819193)
        ·
          refine ⟨7500319085176274509364395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10000425446901699345819193 7500319085176274509364395)
          ·
            refine ⟨11250478627764411764046593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500319085176274509364395 11250478627764411764046593)
            ·
              refine ⟨8437858970823308823034945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11250478627764411764046593 8437858970823308823034945)
              ·
                refine ⟨6328394228117481617276209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8437858970823308823034945 6328394228117481617276209)
                ·
                  refine ⟨4746295671088111212957157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6328394228117481617276209 4746295671088111212957157)
                  ·
                    refine ⟨889930438329020852429467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746295671088111212957157 889930438329020852429467)
                    ·
                      rfl

theorem cell23_5199400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5199400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199400 prefixEnd_5199400 := by exact prefixLift 5199400
  have htrace : WordTrace (prefixWord ++ tailWord_5199400) baseStart_5199400 baseEnd_5199400 := by
    simpa [prefixWord, tailWord_5199400, baseEnd_5199400] using wordTrace_append hprefix tailTrace_5199400
  have hstable : (prefixWord ++ tailWord_5199400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199400).length < 2 ^ (prefixWord ++ tailWord_5199400).sum := by decide
  have hdescent : baseEnd_5199400 < baseStart_5199400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199423 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 3]
def baseStart_5199423 : Nat := 118140960795 + 5199423 * 2 ^ 59
def prefixEnd_5199423 : Nat := 4983230072969 + 3 ^ 40 * 5199423 * 2
def baseEnd_5199423 : Nat := 2669803125042115967300795

theorem tailTrace_5199423 : CollatzResearch.WordTrace tailWord_5199423 prefixEnd_5199423 2669803125042115967300795 := by
  unfold tailWord_5199423
  simp only [CollatzResearch.WordTrace]
  refine ⟨189638536242385936596954923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126425690828257291064636615 189638536242385936596954923)
  ·
    refine ⟨284457804363578904895432385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189638536242385936596954923 284457804363578904895432385)
    ·
      refine ⟨213343353272684178671574289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284457804363578904895432385 213343353272684178671574289)
      ·
        refine ⟨160007514954513134003680717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213343353272684178671574289 160007514954513134003680717)
        ·
          refine ⟨60002818107942425251380269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160007514954513134003680717 60002818107942425251380269)
          ·
            refine ⟨22501056790478409469267601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60002818107942425251380269 22501056790478409469267601)
            ·
              refine ⟨16875792592858807101950701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22501056790478409469267601 16875792592858807101950701)
              ·
                refine ⟨6328422222322052663231513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16875792592858807101950701 6328422222322052663231513)
                ·
                  refine ⟨4746316666741539497423635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6328422222322052663231513 4746316666741539497423635)
                  ·
                    refine ⟨7119475000112309246135453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746316666741539497423635 7119475000112309246135453)
                    ·
                      refine ⟨2669803125042115967300795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119475000112309246135453 2669803125042115967300795)
                      ·
                        rfl

theorem cell23_5199423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_5199423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199423 prefixEnd_5199423 := by exact prefixLift 5199423
  have htrace : WordTrace (prefixWord ++ tailWord_5199423) baseStart_5199423 baseEnd_5199423 := by
    simpa [prefixWord, tailWord_5199423, baseEnd_5199423] using wordTrace_append hprefix tailTrace_5199423
  have hstable : (prefixWord ++ tailWord_5199423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199423).length < 2 ^ (prefixWord ++ tailWord_5199423).sum := by decide
  have hdescent : baseEnd_5199423 < baseStart_5199423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199429 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_5199429 : Nat := 118140960795 + 5199429 * 2 ^ 59
def prefixEnd_5199429 : Nat := 4983230072969 + 3 ^ 40 * 5199429 * 2
def baseEnd_5199429 : Nat := 2669806205926042943825767

theorem tailTrace_5199429 : CollatzResearch.WordTrace tailWord_5199429 prefixEnd_5199429 2669806205926042943825767 := by
  unfold tailWord_5199429
  simp only [CollatzResearch.WordTrace]
  refine ⟨189638755080364199621673341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126425836720242799747782227 189638755080364199621673341)
  ·
    refine ⟨71114533155136574858127503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189638755080364199621673341 71114533155136574858127503)
    ·
      refine ⟨106671799732704862287191255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71114533155136574858127503 106671799732704862287191255)
      ·
        refine ⟨160007699599057293430786883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106671799732704862287191255 160007699599057293430786883)
        ·
          refine ⟨240011549398585940146180325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160007699599057293430786883 240011549398585940146180325)
          ·
            refine ⟨45002165512234863777408811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240011549398585940146180325 45002165512234863777408811)
            ·
              refine ⟨67503248268352295666113217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45002165512234863777408811 67503248268352295666113217)
              ·
                refine ⟨50627436201264221749584913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67503248268352295666113217 50627436201264221749584913)
                ·
                  refine ⟨37970577150948166312188685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50627436201264221749584913 37970577150948166312188685)
                  ·
                    refine ⟨14238966431605562367070757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37970577150948166312188685 14238966431605562367070757)
                    ·
                      refine ⟨2669806205926042943825767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14238966431605562367070757 2669806205926042943825767)
                      ·
                        rfl

theorem cell23_5199429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_5199429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199429 prefixEnd_5199429 := by exact prefixLift 5199429
  have htrace : WordTrace (prefixWord ++ tailWord_5199429) baseStart_5199429 baseEnd_5199429 := by
    simpa [prefixWord, tailWord_5199429, baseEnd_5199429] using wordTrace_append hprefix tailTrace_5199429
  have hstable : (prefixWord ++ tailWord_5199429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199429).length < 2 ^ (prefixWord ++ tailWord_5199429).sum := by decide
  have hdescent : baseEnd_5199429 < baseStart_5199429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199430 : List Nat := [6, 1, 1, 1, 3, 1, 3, 7]
def baseStart_5199430 : Nat := 118140960795 + 5199430 * 2 ^ 59
def prefixEnd_5199430 : Nat := 4983230072969 + 3 ^ 40 * 5199430 * 2
def baseEnd_5199430 : Nat := 98881730348396201478269

theorem tailTrace_5199430 : CollatzResearch.WordTrace tailWord_5199430 prefixEnd_5199430 98881730348396201478269 := by
  unfold tailWord_5199430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926212236042518024764367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126425861035573717861639829 5926212236042518024764367)
  ·
    refine ⟨8889318354063777037146551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5926212236042518024764367 8889318354063777037146551)
    ·
      refine ⟨13333977531095665555719827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8889318354063777037146551 13333977531095665555719827)
      ·
        refine ⟨20000966296643498333579741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13333977531095665555719827 20000966296643498333579741)
        ·
          refine ⟨7500362361241311875092403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20000966296643498333579741 7500362361241311875092403)
          ·
            refine ⟨11250543541861967812638605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500362361241311875092403 11250543541861967812638605)
            ·
              refine ⟨4218953828198237929739477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11250543541861967812638605 4218953828198237929739477)
              ·
                refine ⟨98881730348396201478269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4218953828198237929739477 98881730348396201478269)
                ·
                  rfl

theorem cell23_5199430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_5199430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199430 prefixEnd_5199430 := by exact prefixLift 5199430
  have htrace : WordTrace (prefixWord ++ tailWord_5199430) baseStart_5199430 baseEnd_5199430 := by
    simpa [prefixWord, tailWord_5199430, baseEnd_5199430] using wordTrace_append hprefix tailTrace_5199430
  have hstable : (prefixWord ++ tailWord_5199430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199430).length < 2 ^ (prefixWord ++ tailWord_5199430).sum := by decide
  have hdescent : baseEnd_5199430 < baseStart_5199430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199449 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_5199449 : Nat := 118140960795 + 5199449 * 2 ^ 59
def prefixEnd_5199449 : Nat := 4983230072969 + 3 ^ 40 * 5199449 * 2
def baseEnd_5199449 : Nat := 2669816475539132865575675

theorem tailTrace_5199449 : CollatzResearch.WordTrace tailWord_5199449 prefixEnd_5199449 2669816475539132865575675 := by
  unfold tailWord_5199449
  simp only [CollatzResearch.WordTrace]
  refine ⟨189639484540291743037401401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126426323026861162024934267 189639484540291743037401401)
  ·
    refine ⟨142229613405218807278051051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189639484540291743037401401 142229613405218807278051051)
    ·
      refine ⟨213344420107828210917076577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142229613405218807278051051 213344420107828210917076577)
      ·
        refine ⟨160008315080871158187807433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213344420107828210917076577 160008315080871158187807433)
        ·
          refine ⟨120006236310653368640855575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160008315080871158187807433 120006236310653368640855575)
          ·
            refine ⟨180009354465980052961283363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120006236310653368640855575 180009354465980052961283363)
            ·
              refine ⟨270014031698970079441925045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180009354465980052961283363 270014031698970079441925045)
              ·
                refine ⟨25313815471778444947680473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270014031698970079441925045 25313815471778444947680473)
                ·
                  refine ⟨18985361603833833710760355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25313815471778444947680473 18985361603833833710760355)
                  ·
                    refine ⟨28478042405750750566140533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18985361603833833710760355 28478042405750750566140533)
                    ·
                      refine ⟨2669816475539132865575675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28478042405750750566140533 2669816475539132865575675)
                      ·
                        rfl

theorem cell23_5199449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_5199449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199449 prefixEnd_5199449 := by exact prefixLift 5199449
  have htrace : WordTrace (prefixWord ++ tailWord_5199449) baseStart_5199449 baseEnd_5199449 := by
    simpa [prefixWord, tailWord_5199449, baseEnd_5199449] using wordTrace_append hprefix tailTrace_5199449
  have hstable : (prefixWord ++ tailWord_5199449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199449).length < 2 ^ (prefixWord ++ tailWord_5199449).sum := by decide
  have hdescent : baseEnd_5199449 < baseStart_5199449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199499 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 7]
def baseStart_5199499 : Nat := 118140960795 + 5199499 * 2 ^ 59
def prefixEnd_5199499 : Nat := 4983230072969 + 3 ^ 40 * 5199499 * 2
def baseEnd_5199499 : Nat := 889947383190619223316815

theorem tailTrace_5199499 : CollatzResearch.WordTrace tailWord_5199499 prefixEnd_5199499 889947383190619223316815 := by
  unfold tailWord_5199499
  simp only [CollatzResearch.WordTrace]
  refine ⟨189641308190110601576721551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126427538793407067717814367 189641308190110601576721551)
  ·
    refine ⟨284461962285165902365082327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189641308190110601576721551 284461962285165902365082327)
    ·
      refine ⟨426692943427748853547623491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284461962285165902365082327 426692943427748853547623491)
      ·
        refine ⟨640039415141623280321435237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426692943427748853547623491 640039415141623280321435237)
        ·
          refine ⟨120007390339054365060269107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 640039415141623280321435237 120007390339054365060269107)
          ·
            refine ⟨180011085508581547590403661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120007390339054365060269107 180011085508581547590403661)
            ·
              refine ⟨67504157065718080346401373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180011085508581547590403661 67504157065718080346401373)
              ·
                refine ⟨25314058899644280129900515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67504157065718080346401373 25314058899644280129900515)
                ·
                  refine ⟨37971088349466420194850773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25314058899644280129900515 37971088349466420194850773)
                  ·
                    refine ⟨889947383190619223316815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37971088349466420194850773 889947383190619223316815)
                    ·
                      rfl

theorem cell23_5199499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_5199499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199499 prefixEnd_5199499 := by exact prefixLift 5199499
  have htrace : WordTrace (prefixWord ++ tailWord_5199499) baseStart_5199499 baseEnd_5199499 := by
    simpa [prefixWord, tailWord_5199499, baseEnd_5199499] using wordTrace_append hprefix tailTrace_5199499
  have hstable : (prefixWord ++ tailWord_5199499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199499).length < 2 ^ (prefixWord ++ tailWord_5199499).sum := by decide
  have hdescent : baseEnd_5199499 < baseStart_5199499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199509 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_5199509 : Nat := 118140960795 + 5199509 * 2 ^ 59
def prefixEnd_5199509 : Nat := 4983230072969 + 3 ^ 40 * 5199509 * 2
def baseEnd_5199509 : Nat := 2669847284378402630825399

theorem tailTrace_5199509 : CollatzResearch.WordTrace tailWord_5199509 prefixEnd_5199509 2669847284378402630825399 := by
  unfold tailWord_5199509
  simp only [CollatzResearch.WordTrace]
  refine ⟨189641672920074373284585581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126427781946716248856390387 189641672920074373284585581)
  ·
    refine ⟨71115627345027889981719593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189641672920074373284585581 71115627345027889981719593)
    ·
      refine ⟨53336720508770917486289695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71115627345027889981719593 53336720508770917486289695)
      ·
        refine ⟨80005080763156376229434543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53336720508770917486289695 80005080763156376229434543)
        ·
          refine ⟨120007621144734564344151815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80005080763156376229434543 120007621144734564344151815)
          ·
            refine ⟨180011431717101846516227723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120007621144734564344151815 180011431717101846516227723)
            ·
              refine ⟨270017147575652769774341585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180011431717101846516227723 270017147575652769774341585)
              ·
                refine ⟨202512860681739577330756189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270017147575652769774341585 202512860681739577330756189)
                ·
                  refine ⟨75942322755652341499033571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202512860681739577330756189 75942322755652341499033571)
                  ·
                    refine ⟨113913484133478512248550357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75942322755652341499033571 113913484133478512248550357)
                    ·
                      refine ⟨2669847284378402630825399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113913484133478512248550357 2669847284378402630825399)
                      ·
                        rfl

theorem cell23_5199509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_5199509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199509 prefixEnd_5199509 := by exact prefixLift 5199509
  have htrace : WordTrace (prefixWord ++ tailWord_5199509) baseStart_5199509 baseEnd_5199509 := by
    simpa [prefixWord, tailWord_5199509, baseEnd_5199509] using wordTrace_append hprefix tailTrace_5199509
  have hstable : (prefixWord ++ tailWord_5199509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199509).length < 2 ^ (prefixWord ++ tailWord_5199509).sum := by decide
  have hdescent : baseEnd_5199509 < baseStart_5199509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199520 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 5]
def baseStart_5199520 : Nat := 118140960795 + 5199520 * 2 ^ 59
def prefixEnd_5199520 : Nat := 4983230072969 + 3 ^ 40 * 5199520 * 2
def baseEnd_5199520 : Nat := 296650325851733565309761

theorem tailTrace_5199520 : CollatzResearch.WordTrace tailWord_5199520 prefixEnd_5199520 296650325851733565309761 := by
  unfold tailWord_5199520
  simp only [CollatzResearch.WordTrace]
  refine ⟨94821037061517261081618007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126428049415356348108824009 94821037061517261081618007)
  ·
    refine ⟨142231555592275891622427011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94821037061517261081618007 142231555592275891622427011)
    ·
      refine ⟨213347333388413837433640517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142231555592275891622427011 213347333388413837433640517)
      ·
        refine ⟨40002625010327594518807597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213347333388413837433640517 40002625010327594518807597)
        ·
          refine ⟨15000984378872847944552849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40002625010327594518807597 15000984378872847944552849)
          ·
            refine ⟨11250738284154635958414637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15000984378872847944552849 11250738284154635958414637)
            ·
              refine ⟨4219026856557988484405489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11250738284154635958414637 4219026856557988484405489)
              ·
                refine ⟨3164270142418491363304117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219026856557988484405489 3164270142418491363304117)
                ·
                  refine ⟨296650325851733565309761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3164270142418491363304117 296650325851733565309761)
                  ·
                    rfl

theorem cell23_5199520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 5].length) (baseStart_5199520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199520 prefixEnd_5199520 := by exact prefixLift 5199520
  have htrace : WordTrace (prefixWord ++ tailWord_5199520) baseStart_5199520 baseEnd_5199520 := by
    simpa [prefixWord, tailWord_5199520, baseEnd_5199520] using wordTrace_append hprefix tailTrace_5199520
  have hstable : (prefixWord ++ tailWord_5199520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199520).length < 2 ^ (prefixWord ++ tailWord_5199520).sum := by decide
  have hdescent : baseEnd_5199520 < baseStart_5199520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199566 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_5199566 : Nat := 118140960795 + 5199566 * 2 ^ 59
def prefixEnd_5199566 : Nat := 4983230072969 + 3 ^ 40 * 5199566 * 2
def baseEnd_5199566 : Nat := 2669876552775708907812637

theorem tailTrace_5199566 : CollatzResearch.WordTrace tailWord_5199566 prefixEnd_5199566 2669876552775708907812637 := by
  unfold tailWord_5199566
  simp only [CollatzResearch.WordTrace]
  refine ⟨23705468985108484002426319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126429167920578581346273701 23705468985108484002426319)
  ·
    refine ⟨35558203477662726003639479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23705468985108484002426319 35558203477662726003639479)
    ·
      refine ⟨53337305216494089005459219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35558203477662726003639479 53337305216494089005459219)
      ·
        refine ⟨80005957824741133508188829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53337305216494089005459219 80005957824741133508188829)
        ·
          refine ⟨30002234184277925065570811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80005957824741133508188829 30002234184277925065570811)
          ·
            refine ⟨45003351276416887598356217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30002234184277925065570811 45003351276416887598356217)
            ·
              refine ⟨33752513457312665698767163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45003351276416887598356217 33752513457312665698767163)
              ·
                refine ⟨50628770185968998548150745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33752513457312665698767163 50628770185968998548150745)
                ·
                  refine ⟨37971577639476748911113059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50628770185968998548150745 37971577639476748911113059)
                  ·
                    refine ⟨56957366459215123366669589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37971577639476748911113059 56957366459215123366669589)
                    ·
                      refine ⟨2669876552775708907812637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56957366459215123366669589 2669876552775708907812637)
                      ·
                        rfl

theorem cell23_5199566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_5199566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199566 prefixEnd_5199566 := by exact prefixLift 5199566
  have htrace : WordTrace (prefixWord ++ tailWord_5199566) baseStart_5199566 baseEnd_5199566 := by
    simpa [prefixWord, tailWord_5199566, baseEnd_5199566] using wordTrace_append hprefix tailTrace_5199566
  have hstable : (prefixWord ++ tailWord_5199566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199566).length < 2 ^ (prefixWord ++ tailWord_5199566).sum := by decide
  have hdescent : baseEnd_5199566 < baseStart_5199566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199603 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 3]
def baseStart_5199603 : Nat := 118140960795 + 5199603 * 2 ^ 59
def prefixEnd_5199603 : Nat := 4983230072969 + 3 ^ 40 * 5199603 * 2
def baseEnd_5199603 : Nat := 2669895551559925263049967

theorem tailTrace_5199603 : CollatzResearch.WordTrace tailWord_5199603 prefixEnd_5199603 2669895551559925263049967 := by
  unfold tailWord_5199603
  simp only [CollatzResearch.WordTrace]
  refine ⟨189645101381733827338507463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126430067587822551559004975 189645101381733827338507463)
  ·
    refine ⟨284467652072600741007761195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189645101381733827338507463 284467652072600741007761195)
    ·
      refine ⟨426701478108901111511641793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284467652072600741007761195 426701478108901111511641793)
      ·
        refine ⟨320026108581675833633731345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426701478108901111511641793 320026108581675833633731345)
        ·
          refine ⟨240019581436256875225298509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320026108581675833633731345 240019581436256875225298509)
          ·
            refine ⟨90007343038596328209486941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240019581436256875225298509 90007343038596328209486941)
            ·
              refine ⟨33752753639473623078557603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90007343038596328209486941 33752753639473623078557603)
              ·
                refine ⟨50629130459210434617836405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33752753639473623078557603 50629130459210434617836405)
                ·
                  refine ⟨4746480980550978245422163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50629130459210434617836405 4746480980550978245422163)
                  ·
                    refine ⟨7119721470826467368133245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746480980550978245422163 7119721470826467368133245)
                    ·
                      refine ⟨2669895551559925263049967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119721470826467368133245 2669895551559925263049967)
                      ·
                        rfl

theorem cell23_5199603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_5199603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199603 prefixEnd_5199603 := by exact prefixLift 5199603
  have htrace : WordTrace (prefixWord ++ tailWord_5199603) baseStart_5199603 baseEnd_5199603 := by
    simpa [prefixWord, tailWord_5199603, baseEnd_5199603] using wordTrace_append hprefix tailTrace_5199603
  have hstable : (prefixWord ++ tailWord_5199603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199603).length < 2 ^ (prefixWord ++ tailWord_5199603).sum := by decide
  have hdescent : baseEnd_5199603 < baseStart_5199603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199604 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5199604 : Nat := 118140960795 + 5199604 * 2 ^ 59
def prefixEnd_5199604 : Nat := 4983230072969 + 3 ^ 40 * 5199604 * 2
def baseEnd_5199604 : Nat := 2669896065040579759137463

theorem tailTrace_5199604 : CollatzResearch.WordTrace tailWord_5199604 prefixEnd_5199604 2669896065040579759137463 := by
  unfold tailWord_5199604
  simp only [CollatzResearch.WordTrace]
  refine ⟨94822568927365102254646933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126430091903153469672862577 94822568927365102254646933)
  ·
    refine ⟨4444807918470239168186575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94822568927365102254646933 4444807918470239168186575)
    ·
      refine ⟨6667211877705358752279863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444807918470239168186575 6667211877705358752279863)
      ·
        refine ⟨10000817816558038128419795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667211877705358752279863 10000817816558038128419795)
        ·
          refine ⟨15001226724837057192629693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000817816558038128419795 15001226724837057192629693)
          ·
            refine ⟨5625460021813896447236135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15001226724837057192629693 5625460021813896447236135)
            ·
              refine ⟨8438190032720844670854203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625460021813896447236135 8438190032720844670854203)
              ·
                refine ⟨12657285049081267006281305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8438190032720844670854203 12657285049081267006281305)
                ·
                  refine ⟨9492963786810950254710979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12657285049081267006281305 9492963786810950254710979)
                  ·
                    refine ⟨14239445680216425382066469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9492963786810950254710979 14239445680216425382066469)
                    ·
                      refine ⟨2669896065040579759137463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14239445680216425382066469 2669896065040579759137463)
                      ·
                        rfl

theorem cell23_5199604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5199604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199604 prefixEnd_5199604 := by exact prefixLift 5199604
  have htrace : WordTrace (prefixWord ++ tailWord_5199604) baseStart_5199604 baseEnd_5199604 := by
    simpa [prefixWord, tailWord_5199604, baseEnd_5199604] using wordTrace_append hprefix tailTrace_5199604
  have hstable : (prefixWord ++ tailWord_5199604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199604).length < 2 ^ (prefixWord ++ tailWord_5199604).sum := by decide
  have hdescent : baseEnd_5199604 < baseStart_5199604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199614 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5199614 : Nat := 118140960795 + 5199614 * 2 ^ 59
def prefixEnd_5199614 : Nat := 4983230072969 + 3 ^ 40 * 5199614 * 2
def baseEnd_5199614 : Nat := 889967066615708240004139

theorem tailTrace_5199614 : CollatzResearch.WordTrace tailWord_5199614 prefixEnd_5199614 889967066615708240004139 := by
  unfold tailWord_5199614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23705687823086747027144737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126430335056462650811438597 23705687823086747027144737)
  ·
    refine ⟨17779265867315060270358553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23705687823086747027144737 17779265867315060270358553)
    ·
      refine ⟨13334449400486295202768915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17779265867315060270358553 13334449400486295202768915)
      ·
        refine ⟨20001674100729442804153373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13334449400486295202768915 20001674100729442804153373)
        ·
          refine ⟨7500627787773541051557515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20001674100729442804153373 7500627787773541051557515)
          ·
            refine ⟨11250941681660311577336273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500627787773541051557515 11250941681660311577336273)
            ·
              refine ⟨8438206261245233683002205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11250941681660311577336273 8438206261245233683002205)
              ·
                refine ⟨3164327347966962631125827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8438206261245233683002205 3164327347966962631125827)
                ·
                  refine ⟨4746491021950443946688741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164327347966962631125827 4746491021950443946688741)
                  ·
                    refine ⟨889967066615708240004139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746491021950443946688741 889967066615708240004139)
                    ·
                      rfl

theorem cell23_5199614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5199614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199614 prefixEnd_5199614 := by exact prefixLift 5199614
  have htrace : WordTrace (prefixWord ++ tailWord_5199614) baseStart_5199614 baseEnd_5199614 := by
    simpa [prefixWord, tailWord_5199614, baseEnd_5199614] using wordTrace_append hprefix tailTrace_5199614
  have hstable : (prefixWord ++ tailWord_5199614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199614).length < 2 ^ (prefixWord ++ tailWord_5199614).sum := by decide
  have hdescent : baseEnd_5199614 < baseStart_5199614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199630 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5199630 : Nat := 118140960795 + 5199630 * 2 ^ 59
def prefixEnd_5199630 : Nat := 4983230072969 + 3 ^ 40 * 5199630 * 2
def baseEnd_5199630 : Nat := 2669909415537596657412343

theorem tailTrace_5199630 : CollatzResearch.WordTrace tailWord_5199630 prefixEnd_5199630 2669909415537596657412343 := by
  unfold tailWord_5199630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23705760769079501368717543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126430724101757340633160229 23705760769079501368717543)
  ·
    refine ⟨35558641153619252053076315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23705760769079501368717543 35558641153619252053076315)
    ·
      refine ⟨53337961730428878079614473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35558641153619252053076315 53337961730428878079614473)
      ·
        refine ⟨40003471297821658559710855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53337961730428878079614473 40003471297821658559710855)
        ·
          refine ⟨60005206946732487839566283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40003471297821658559710855 60005206946732487839566283)
          ·
            refine ⟨90007810420098731759349425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60005206946732487839566283 90007810420098731759349425)
            ·
              refine ⟨67505857815074048819512069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90007810420098731759349425 67505857815074048819512069)
              ·
                refine ⟨12657348340326384153658513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67505857815074048819512069 12657348340326384153658513)
                ·
                  refine ⟨9493011255244788115243885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12657348340326384153658513 9493011255244788115243885)
                  ·
                    refine ⟨3559879220716795543216457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9493011255244788115243885 3559879220716795543216457)
                    ·
                      refine ⟨2669909415537596657412343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559879220716795543216457 2669909415537596657412343)
                      ·
                        rfl

theorem cell23_5199630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5199630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199630 prefixEnd_5199630 := by exact prefixLift 5199630
  have htrace : WordTrace (prefixWord ++ tailWord_5199630) baseStart_5199630 baseEnd_5199630 := by
    simpa [prefixWord, tailWord_5199630, baseEnd_5199630] using wordTrace_append hprefix tailTrace_5199630
  have hstable : (prefixWord ++ tailWord_5199630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199630).length < 2 ^ (prefixWord ++ tailWord_5199630).sum := by decide
  have hdescent : baseEnd_5199630 < baseStart_5199630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199637 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_5199637 : Nat := 118140960795 + 5199637 * 2 ^ 59
def prefixEnd_5199637 : Nat := 4983230072969 + 3 ^ 40 * 5199637 * 2
def baseEnd_5199637 : Nat := 2669913009902178130024811

theorem tailTrace_5199637 : CollatzResearch.WordTrace tailWord_5199637 prefixEnd_5199637 2669913009902178130024811 := by
  unfold tailWord_5199637
  simp only [CollatzResearch.WordTrace]
  refine ⟨189646341463610651145245165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126430894309073767430163443 189646341463610651145245165)
  ·
    refine ⟨71117378048853994179466937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189646341463610651145245165 71117378048853994179466937)
    ·
      refine ⟨53338033536640495634600203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71117378048853994179466937 53338033536640495634600203)
      ·
        refine ⟨80007050304960743451900305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53338033536640495634600203 80007050304960743451900305)
        ·
          refine ⟨60005287728720557588925229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80007050304960743451900305 60005287728720557588925229)
          ·
            refine ⟨22501982898270209095846961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60005287728720557588925229 22501982898270209095846961)
            ·
              refine ⟨16876487173702656821885221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22501982898270209095846961 16876487173702656821885221)
              ·
                refine ⟨3164341345069248154103479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16876487173702656821885221 3164341345069248154103479)
                ·
                  refine ⟨4746512017603872231155219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164341345069248154103479 4746512017603872231155219)
                  ·
                    refine ⟨7119768026405808346732829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4746512017603872231155219 7119768026405808346732829)
                    ·
                      refine ⟨2669913009902178130024811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119768026405808346732829 2669913009902178130024811)
                      ·
                        rfl

theorem cell23_5199637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_5199637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199637 prefixEnd_5199637 := by exact prefixLift 5199637
  have htrace : WordTrace (prefixWord ++ tailWord_5199637) baseStart_5199637 baseEnd_5199637 := by
    simpa [prefixWord, tailWord_5199637, baseEnd_5199637] using wordTrace_append hprefix tailTrace_5199637
  have hstable : (prefixWord ++ tailWord_5199637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199637).length < 2 ^ (prefixWord ++ tailWord_5199637).sum := by decide
  have hdescent : baseEnd_5199637 < baseStart_5199637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199653 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_5199653 : Nat := 118140960795 + 5199653 * 2 ^ 59
def prefixEnd_5199653 : Nat := 4983230072969 + 3 ^ 40 * 5199653 * 2
def baseEnd_5199653 : Nat := 889973741864216689141579

theorem tailTrace_5199653 : CollatzResearch.WordTrace tailWord_5199653 prefixEnd_5199653 889973741864216689141579 := by
  unfold tailWord_5199653
  simp only [CollatzResearch.WordTrace]
  refine ⟨189646925031552685877827613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126431283354368457251885075 189646925031552685877827613)
  ·
    refine ⟨71117596886832257204185355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189646925031552685877827613 71117596886832257204185355)
    ·
      refine ⟨106676395330248385806278033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71117596886832257204185355 106676395330248385806278033)
      ·
        refine ⟨80007296497686289354708525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106676395330248385806278033 80007296497686289354708525)
        ·
          refine ⟨30002736186632358508015697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80007296497686289354708525 30002736186632358508015697)
          ·
            refine ⟨22502052139974268881011773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30002736186632358508015697 22502052139974268881011773)
            ·
              refine ⟨8438269552490350830379415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22502052139974268881011773 8438269552490350830379415)
              ·
                refine ⟨12657404328735526245569123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8438269552490350830379415 12657404328735526245569123)
                ·
                  refine ⟨18986106493103289368353685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12657404328735526245569123 18986106493103289368353685)
                  ·
                    refine ⟨889973741864216689141579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18986106493103289368353685 889973741864216689141579)
                    ·
                      rfl

theorem cell23_5199653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_5199653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199653 prefixEnd_5199653 := by exact prefixLift 5199653
  have htrace : WordTrace (prefixWord ++ tailWord_5199653) baseStart_5199653 baseEnd_5199653 := by
    simpa [prefixWord, tailWord_5199653, baseEnd_5199653] using wordTrace_append hprefix tailTrace_5199653
  have hstable : (prefixWord ++ tailWord_5199653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199653).length < 2 ^ (prefixWord ++ tailWord_5199653).sum := by decide
  have hdescent : baseEnd_5199653 < baseStart_5199653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199660 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_5199660 : Nat := 118140960795 + 5199660 * 2 ^ 59
def prefixEnd_5199660 : Nat := 4983230072969 + 3 ^ 40 * 5199660 * 2
def baseEnd_5199660 : Nat := 2669924819957231540037205

theorem tailTrace_5199660 : CollatzResearch.WordTrace tailWord_5199660 prefixEnd_5199660 2669924819957231540037205 := by
  unfold tailWord_5199660
  simp only [CollatzResearch.WordTrace]
  refine ⟨94823590171263663036666217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126431453561684884048888289 94823590171263663036666217)
  ·
    refine ⟨71117692628447747277499663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94823590171263663036666217 71117692628447747277499663)
    ·
      refine ⟨106676538942671620916249495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71117692628447747277499663 106676538942671620916249495)
      ·
        refine ⟨160014808414007431374374243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106676538942671620916249495 160014808414007431374374243)
        ·
          refine ⟨240022212621011147061561365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160014808414007431374374243 240022212621011147061561365)
          ·
            refine ⟨11251041216609897518510689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 240022212621011147061561365 11251041216609897518510689)
            ·
              refine ⟨8438280912457423138883017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251041216609897518510689 8438280912457423138883017)
              ·
                refine ⟨6328710684343067354162263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438280912457423138883017 6328710684343067354162263)
                ·
                  refine ⟨9493066026514601031243395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328710684343067354162263 9493066026514601031243395)
                  ·
                    refine ⟨14239599039771901546865093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9493066026514601031243395 14239599039771901546865093)
                    ·
                      refine ⟨2669924819957231540037205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14239599039771901546865093 2669924819957231540037205)
                      ·
                        rfl

theorem cell23_5199660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_5199660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199660 prefixEnd_5199660 := by exact prefixLift 5199660
  have htrace : WordTrace (prefixWord ++ tailWord_5199660) baseStart_5199660 baseEnd_5199660 := by
    simpa [prefixWord, tailWord_5199660, baseEnd_5199660] using wordTrace_append hprefix tailTrace_5199660
  have hstable : (prefixWord ++ tailWord_5199660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199660).length < 2 ^ (prefixWord ++ tailWord_5199660).sum := by decide
  have hdescent : baseEnd_5199660 < baseStart_5199660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199696 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_5199696 : Nat := 118140960795 + 5199696 * 2 ^ 59
def prefixEnd_5199696 : Nat := 4983230072969 + 3 ^ 40 * 5199696 * 2
def baseEnd_5199696 : Nat := 889981101753597799729013

theorem tailTrace_5199696 : CollatzResearch.WordTrace tailWord_5199696 prefixEnd_5199696 889981101753597799729013 := by
  unfold tailWord_5199696
  simp only [CollatzResearch.WordTrace]
  refine ⟨94824246685198452110821471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126432328913597936147761961 94824246685198452110821471)
  ·
    refine ⟨142236370027797678166232207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94824246685198452110821471 142236370027797678166232207)
    ·
      refine ⟨213354555041696517249348311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142236370027797678166232207 213354555041696517249348311)
      ·
        refine ⟨320031832562544775874022467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213354555041696517249348311 320031832562544775874022467)
        ·
          refine ⟨480047748843817163811033701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320031832562544775874022467 480047748843817163811033701)
          ·
            refine ⟨90008952908215718214568819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 480047748843817163811033701 90008952908215718214568819)
            ·
              refine ⟨135013429362323577321853229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90008952908215718214568819 135013429362323577321853229)
              ·
                refine ⟨50630036010871341495694961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135013429362323577321853229 50630036010871341495694961)
                ·
                  refine ⟨37972527008153506121771221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50630036010871341495694961 37972527008153506121771221)
                  ·
                    refine ⟨889981101753597799729013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37972527008153506121771221 889981101753597799729013)
                    ·
                      rfl

theorem cell23_5199696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_5199696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199696 prefixEnd_5199696 := by exact prefixLift 5199696
  have htrace : WordTrace (prefixWord ++ tailWord_5199696) baseStart_5199696 baseEnd_5199696 := by
    simpa [prefixWord, tailWord_5199696, baseEnd_5199696] using wordTrace_append hprefix tailTrace_5199696
  have hstable : (prefixWord ++ tailWord_5199696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199696).length < 2 ^ (prefixWord ++ tailWord_5199696).sum := by decide
  have hdescent : baseEnd_5199696 < baseStart_5199696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199714 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5199714 : Nat := 118140960795 + 5199714 * 2 ^ 59
def prefixEnd_5199714 : Nat := 4983230072969 + 3 ^ 40 * 5199714 * 2
def baseEnd_5199714 : Nat := 2669952547912574328761957

theorem tailTrace_5199714 : CollatzResearch.WordTrace tailWord_5199714 prefixEnd_5199714 2669952547912574328761957 := by
  unfold tailWord_5199714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47412287471082923323949549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126432766589554462197198797 47412287471082923323949549)
  ·
    refine ⟨17779607801656096246481081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47412287471082923323949549 17779607801656096246481081)
    ·
      refine ⟨13334705851242072184860811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17779607801656096246481081 13334705851242072184860811)
      ·
        refine ⟨20002058776863108277291217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13334705851242072184860811 20002058776863108277291217)
        ·
          refine ⟨15001544082647331207968413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20002058776863108277291217 15001544082647331207968413)
          ·
            refine ⟨5625579030992749202988155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15001544082647331207968413 5625579030992749202988155)
            ·
              refine ⟨8438368546489123804482233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625579030992749202988155 8438368546489123804482233)
              ·
                refine ⟨6328776409866842853361675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438368546489123804482233 6328776409866842853361675)
                ·
                  refine ⟨9493164614800264280042513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328776409866842853361675 9493164614800264280042513)
                  ·
                    refine ⟨7119873461100198210031885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9493164614800264280042513 7119873461100198210031885)
                    ·
                      refine ⟨2669952547912574328761957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119873461100198210031885 2669952547912574328761957)
                      ·
                        rfl

theorem cell23_5199714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5199714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199714 prefixEnd_5199714 := by exact prefixLift 5199714
  have htrace : WordTrace (prefixWord ++ tailWord_5199714) baseStart_5199714 baseEnd_5199714 := by
    simpa [prefixWord, tailWord_5199714, baseEnd_5199714] using wordTrace_append hprefix tailTrace_5199714
  have hstable : (prefixWord ++ tailWord_5199714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199714).length < 2 ^ (prefixWord ++ tailWord_5199714).sum := by decide
  have hdescent : baseEnd_5199714 < baseStart_5199714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199745 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5199745 : Nat := 118140960795 + 5199745 * 2 ^ 59
def prefixEnd_5199745 : Nat := 4983230072969 + 3 ^ 40 * 5199745 * 2
def baseEnd_5199745 : Nat := 2669968465812863707474315

theorem tailTrace_5199745 : CollatzResearch.WordTrace tailWord_5199745 prefixEnd_5199745 2669968465812863707474315 := by
  unfold tailWord_5199745
  simp only [CollatzResearch.WordTrace]
  refine ⟨189650280547219385590176689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126433520364812923726784459 189650280547219385590176689)
  ·
    refine ⟨142237710410414539192632517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189650280547219385590176689 142237710410414539192632517)
    ·
      refine ⟨26669570701952726098618597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142237710410414539192632517 26669570701952726098618597)
      ·
        refine ⟨5000544506616136143490987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26669570701952726098618597 5000544506616136143490987)
        ·
          refine ⟨7500816759924204215236481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000544506616136143490987 7500816759924204215236481)
          ·
            refine ⟨5625612569943153161427361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7500816759924204215236481 5625612569943153161427361)
            ·
              refine ⟨4219209427457364871070521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5625612569943153161427361 4219209427457364871070521)
              ·
                refine ⟨3164407070593023653302891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219209427457364871070521 3164407070593023653302891)
                ·
                  refine ⟨4746610605889535479954337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164407070593023653302891 4746610605889535479954337)
                  ·
                    refine ⟨3559957954417151609965753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746610605889535479954337 3559957954417151609965753)
                    ·
                      refine ⟨2669968465812863707474315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559957954417151609965753 2669968465812863707474315)
                      ·
                        rfl

theorem cell23_5199745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5199745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199745 prefixEnd_5199745 := by exact prefixLift 5199745
  have htrace : WordTrace (prefixWord ++ tailWord_5199745) baseStart_5199745 baseEnd_5199745 := by
    simpa [prefixWord, tailWord_5199745, baseEnd_5199745] using wordTrace_append hprefix tailTrace_5199745
  have hstable : (prefixWord ++ tailWord_5199745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199745).length < 2 ^ (prefixWord ++ tailWord_5199745).sum := by decide
  have hdescent : baseEnd_5199745 < baseStart_5199745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199753 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_5199753 : Nat := 118140960795 + 5199753 * 2 ^ 59
def prefixEnd_5199753 : Nat := 4983230072969 + 3 ^ 40 * 5199753 * 2
def baseEnd_5199753 : Nat := 2669972573658099676174277

theorem tailTrace_5199753 : CollatzResearch.WordTrace tailWord_5199753 prefixEnd_5199753 2669972573658099676174277 := by
  unfold tailWord_5199753
  simp only [CollatzResearch.WordTrace]
  refine ⟨189650572331190402956467913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126433714887460268637645275 189650572331190402956467913)
  ·
    refine ⟨142237929248392802217350935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189650572331190402956467913 142237929248392802217350935)
    ·
      refine ⟨213356893872589203326026403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142237929248392802217350935 213356893872589203326026403)
      ·
        refine ⟨320035340808883804989039605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213356893872589203326026403 320035340808883804989039605)
        ·
          refine ⟨30003313200832856717722463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 320035340808883804989039605 30003313200832856717722463)
          ·
            refine ⟨45004969801249285076583695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30003313200832856717722463 45004969801249285076583695)
            ·
              refine ⟨67507454701873927614875543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45004969801249285076583695 67507454701873927614875543)
              ·
                refine ⟨101261182052810891422313315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67507454701873927614875543 101261182052810891422313315)
                ·
                  refine ⟨151891773079216337133469973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101261182052810891422313315 151891773079216337133469973)
                  ·
                    refine ⟨7119926863088265803131405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 151891773079216337133469973 7119926863088265803131405)
                    ·
                      refine ⟨2669972573658099676174277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7119926863088265803131405 2669972573658099676174277)
                      ·
                        rfl

theorem cell23_5199753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_5199753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199753 prefixEnd_5199753 := by exact prefixLift 5199753
  have htrace : WordTrace (prefixWord ++ tailWord_5199753) baseStart_5199753 baseEnd_5199753 := by
    simpa [prefixWord, tailWord_5199753, baseEnd_5199753] using wordTrace_append hprefix tailTrace_5199753
  have hstable : (prefixWord ++ tailWord_5199753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199753).length < 2 ^ (prefixWord ++ tailWord_5199753).sum := by decide
  have hdescent : baseEnd_5199753 < baseStart_5199753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199767 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_5199767 : Nat := 118140960795 + 5199767 * 2 ^ 59
def prefixEnd_5199767 : Nat := 4983230072969 + 3 ^ 40 * 5199767 * 2
def baseEnd_5199767 : Nat := 2669979762387262621399213

theorem tailTrace_5199767 : CollatzResearch.WordTrace tailWord_5199767 prefixEnd_5199767 2669979762387262621399213 := by
  unfold tailWord_5199767
  simp only [CollatzResearch.WordTrace]
  refine ⟨189651082953139683347477555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126434055302093122231651703 189651082953139683347477555)
  ·
    refine ⟨284476624429709525021216333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189651082953139683347477555 284476624429709525021216333)
    ·
      refine ⟨106678734161141071882956125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284476624429709525021216333 106678734161141071882956125)
      ·
        refine ⟨40004525310427901956108547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106678734161141071882956125 40004525310427901956108547)
        ·
          refine ⟨60006787965641852934162821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40004525310427901956108547 60006787965641852934162821)
          ·
            refine ⟨11251272743557847425155529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60006787965641852934162821 11251272743557847425155529)
            ·
              refine ⟨8438454557668385568866647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251272743557847425155529 8438454557668385568866647)
              ·
                refine ⟨12657681836502578353299971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8438454557668385568866647 12657681836502578353299971)
                ·
                  refine ⟨18986522754753867529949957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12657681836502578353299971 18986522754753867529949957)
                  ·
                    refine ⟨3559973016516350161865617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18986522754753867529949957 3559973016516350161865617)
                    ·
                      refine ⟨2669979762387262621399213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3559973016516350161865617 2669979762387262621399213)
                      ·
                        rfl

theorem cell23_5199767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_5199767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199767 prefixEnd_5199767 := by exact prefixLift 5199767
  have htrace : WordTrace (prefixWord ++ tailWord_5199767) baseStart_5199767 baseEnd_5199767 := by
    simpa [prefixWord, tailWord_5199767, baseEnd_5199767] using wordTrace_append hprefix tailTrace_5199767
  have hstable : (prefixWord ++ tailWord_5199767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199767).length < 2 ^ (prefixWord ++ tailWord_5199767).sum := by decide
  have hdescent : baseEnd_5199767 < baseStart_5199767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199773 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 9]
def baseStart_5199773 : Nat := 118140960795 + 5199773 * 2 ^ 59
def prefixEnd_5199773 : Nat := 4983230072969 + 3 ^ 40 * 5199773 * 2
def baseEnd_5199773 : Nat := 296664760363465510880465

theorem tailTrace_5199773 : CollatzResearch.WordTrace tailWord_5199773 prefixEnd_5199773 296664760363465510880465 := by
  unfold tailWord_5199773
  simp only [CollatzResearch.WordTrace]
  refine ⟨189651301791117946372195973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126434201194078630914797315 189651301791117946372195973)
  ·
    refine ⟨35559619085834614944786745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189651301791117946372195973 35559619085834614944786745)
    ·
      refine ⟨26669714314375961208590059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35559619085834614944786745 26669714314375961208590059)
      ·
        refine ⟨40004571471563941812885089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26669714314375961208590059 40004571471563941812885089)
        ·
          refine ⟨30003428603672956359663817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40004571471563941812885089 30003428603672956359663817)
          ·
            refine ⟨22502571452754717269747863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30003428603672956359663817 22502571452754717269747863)
            ·
              refine ⟨33753857179132075904621795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22502571452754717269747863 33753857179132075904621795)
              ·
                refine ⟨50630785768698113856932693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33753857179132075904621795 50630785768698113856932693)
                ·
                  refine ⟨296664760363465510880465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50630785768698113856932693 296664760363465510880465)
                  ·
                    rfl

theorem cell23_5199773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_5199773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199773 prefixEnd_5199773 := by exact prefixLift 5199773
  have htrace : WordTrace (prefixWord ++ tailWord_5199773) baseStart_5199773 baseEnd_5199773 := by
    simpa [prefixWord, tailWord_5199773, baseEnd_5199773] using wordTrace_append hprefix tailTrace_5199773
  have hstable : (prefixWord ++ tailWord_5199773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199773).length < 2 ^ (prefixWord ++ tailWord_5199773).sum := by decide
  have hdescent : baseEnd_5199773 < baseStart_5199773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199823 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_5199823 : Nat := 118140960795 + 5199823 * 2 ^ 59
def prefixEnd_5199823 : Nat := 4983230072969 + 3 ^ 40 * 5199823 * 2
def baseEnd_5199823 : Nat := 2670008517303914402298955

theorem tailTrace_5199823 : CollatzResearch.WordTrace tailWord_5199823 prefixEnd_5199823 2670008517303914402298955 := by
  unfold tailWord_5199823
  simp only [CollatzResearch.WordTrace]
  refine ⟨189653125440936804911516123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126435416960624536607677415 189653125440936804911516123)
  ·
    refine ⟨284479688161405207367274185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189653125440936804911516123 284479688161405207367274185)
    ·
      refine ⟨213359766121053905525455639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284479688161405207367274185 213359766121053905525455639)
      ·
        refine ⟨320039649181580858288183459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213359766121053905525455639 320039649181580858288183459)
        ·
          refine ⟨480059473772371287432275189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320039649181580858288183459 480059473772371287432275189)
          ·
            refine ⟨45005575666159808196775799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 480059473772371287432275189 45005575666159808196775799)
            ·
              refine ⟨67508363499239712295163699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45005575666159808196775799 67508363499239712295163699)
              ·
                refine ⟨101262545248859568442745549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67508363499239712295163699 101262545248859568442745549)
                ·
                  refine ⟨37973454468322338166029581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101262545248859568442745549 37973454468322338166029581)
                  ·
                    refine ⟨14240045425620876812261093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37973454468322338166029581 14240045425620876812261093)
                    ·
                      refine ⟨2670008517303914402298955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14240045425620876812261093 2670008517303914402298955)
                      ·
                        rfl

theorem cell23_5199823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_5199823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199823 prefixEnd_5199823 := by exact prefixLift 5199823
  have htrace : WordTrace (prefixWord ++ tailWord_5199823) baseStart_5199823 baseEnd_5199823 := by
    simpa [prefixWord, tailWord_5199823, baseEnd_5199823] using wordTrace_append hprefix tailTrace_5199823
  have hstable : (prefixWord ++ tailWord_5199823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199823).length < 2 ^ (prefixWord ++ tailWord_5199823).sum := by decide
  have hdescent : baseEnd_5199823 < baseStart_5199823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199840 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2]
def baseStart_5199840 : Nat := 118140960795 + 5199840 * 2 ^ 59
def prefixEnd_5199840 : Nat := 4983230072969 + 3 ^ 40 * 5199840 * 2
def baseEnd_5199840 : Nat := 2670017246475040835786377

theorem tailTrace_5199840 : CollatzResearch.WordTrace tailWord_5199840 prefixEnd_5199840 2670017246475040835786377 := by
  unfold tailWord_5199840
  simp only [CollatzResearch.WordTrace]
  refine ⟨94826872740937608407442487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126435830321250144543256649 94826872740937608407442487)
  ·
    refine ⟨142240309111406412611163731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94826872740937608407442487 142240309111406412611163731)
    ·
      refine ⟨213360463667109618916745597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142240309111406412611163731 213360463667109618916745597)
      ·
        refine ⟨80010173875166107093779599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213360463667109618916745597 80010173875166107093779599)
        ·
          refine ⟨120015260812749160640669399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80010173875166107093779599 120015260812749160640669399)
          ·
            refine ⟨180022891219123740961004099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120015260812749160640669399 180022891219123740961004099)
            ·
              refine ⟨270034336828685611441506149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180022891219123740961004099 270034336828685611441506149)
              ·
                refine ⟨50631438155378552145282403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270034336828685611441506149 50631438155378552145282403)
                ·
                  refine ⟨75947157233067828217923605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50631438155378552145282403 75947157233067828217923605)
                  ·
                    refine ⟨3560022995300054447715169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75947157233067828217923605 3560022995300054447715169)
                    ·
                      refine ⟨2670017246475040835786377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560022995300054447715169 2670017246475040835786377)
                      ·
                        rfl

theorem cell23_5199840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_5199840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199840 prefixEnd_5199840 := by exact prefixLift 5199840
  have htrace : WordTrace (prefixWord ++ tailWord_5199840) baseStart_5199840 baseEnd_5199840 := by
    simpa [prefixWord, tailWord_5199840, baseEnd_5199840] using wordTrace_append hprefix tailTrace_5199840
  have hstable : (prefixWord ++ tailWord_5199840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199840).length < 2 ^ (prefixWord ++ tailWord_5199840).sum := by decide
  have hdescent : baseEnd_5199840 < baseStart_5199840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199857 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_5199857 : Nat := 118140960795 + 5199857 * 2 ^ 59
def prefixEnd_5199857 : Nat := 4983230072969 + 3 ^ 40 * 5199857 * 2
def baseEnd_5199857 : Nat := 2670025975646167269273799

theorem tailTrace_5199857 : CollatzResearch.WordTrace tailWord_5199857 prefixEnd_5199857 2670025975646167269273799 := by
  unfold tailWord_5199857
  simp only [CollatzResearch.WordTrace]
  refine ⟨189654365522813628718253825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126436243681875752478835883 189654365522813628718253825)
  ·
    refine ⟨142240774142110221538690369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189654365522813628718253825 142240774142110221538690369)
    ·
      refine ⟨106680580606582666154017777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142240774142110221538690369 106680580606582666154017777)
      ·
        refine ⟨80010435454936999615513333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106680580606582666154017777 80010435454936999615513333)
        ·
          refine ⟨7500978323900343713954375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80010435454936999615513333 7500978323900343713954375)
          ·
            refine ⟨11251467485850515570931563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500978323900343713954375 11251467485850515570931563)
            ·
              refine ⟨16877201228775773356397345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11251467485850515570931563 16877201228775773356397345)
              ·
                refine ⟨12657900921581830017298009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16877201228775773356397345 12657900921581830017298009)
                ·
                  refine ⟨9493425691186372512973507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12657900921581830017298009 9493425691186372512973507)
                  ·
                    refine ⟨14240138536779558769460261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9493425691186372512973507 14240138536779558769460261)
                    ·
                      refine ⟨2670025975646167269273799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14240138536779558769460261 2670025975646167269273799)
                      ·
                        rfl

theorem cell23_5199857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_5199857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199857 prefixEnd_5199857 := by exact prefixLift 5199857
  have htrace : WordTrace (prefixWord ++ tailWord_5199857) baseStart_5199857 baseEnd_5199857 := by
    simpa [prefixWord, tailWord_5199857, baseEnd_5199857] using wordTrace_append hprefix tailTrace_5199857
  have hstable : (prefixWord ++ tailWord_5199857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199857).length < 2 ^ (prefixWord ++ tailWord_5199857).sum := by decide
  have hdescent : baseEnd_5199857 < baseStart_5199857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199867 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 1, 4]
def baseStart_5199867 : Nat := 118140960795 + 5199867 * 2 ^ 59
def prefixEnd_5199867 : Nat := 4983230072969 + 3 ^ 40 * 5199867 * 2
def baseEnd_5199867 : Nat := 890010370150904076716251

theorem tailTrace_5199867 : CollatzResearch.WordTrace tailWord_5199867 prefixEnd_5199867 890010370150904076716251 := by
  unfold tailWord_5199867
  simp only [CollatzResearch.WordTrace]
  refine ⟨189654730252777400426117855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126436486835184933617411903 189654730252777400426117855)
  ·
    refine ⟨284482095379166100639176783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189654730252777400426117855 284482095379166100639176783)
    ·
      refine ⟨426723143068749150958765175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284482095379166100639176783 426723143068749150958765175)
      ·
        refine ⟨640084714603123726438147763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426723143068749150958765175 640084714603123726438147763)
        ·
          refine ⟨960127071904685589657221645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640084714603123726438147763 960127071904685589657221645)
          ·
            refine ⟨360047651964257096121458117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960127071904685589657221645 360047651964257096121458117)
            ·
              refine ⟨67508934743298205522773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360047651964257096121458117 67508934743298205522773397)
              ·
                refine ⟨3164481316092103383880003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67508934743298205522773397 3164481316092103383880003)
                ·
                  refine ⟨4746721974138155075820005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164481316092103383880003 4746721974138155075820005)
                  ·
                    refine ⟨890010370150904076716251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746721974138155075820005 890010370150904076716251)
                    ·
                      rfl

theorem cell23_5199867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 4].length) (baseStart_5199867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199867 prefixEnd_5199867 := by exact prefixLift 5199867
  have htrace : WordTrace (prefixWord ++ tailWord_5199867) baseStart_5199867 baseEnd_5199867 := by
    simpa [prefixWord, tailWord_5199867, baseEnd_5199867] using wordTrace_append hprefix tailTrace_5199867
  have hstable : (prefixWord ++ tailWord_5199867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199867).length < 2 ^ (prefixWord ++ tailWord_5199867).sum := by decide
  have hdescent : baseEnd_5199867 < baseStart_5199867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199880 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 6]
def baseStart_5199880 : Nat := 118140960795 + 5199880 * 2 ^ 59
def prefixEnd_5199880 : Nat := 4983230072969 + 3 ^ 40 * 5199880 * 2
def baseEnd_5199880 : Nat := 296670865077913408809577

theorem tailTrace_5199880 : CollatzResearch.WordTrace tailWord_5199880 prefixEnd_5199880 296670865077913408809577 := by
  unfold tailWord_5199880
  simp only [CollatzResearch.WordTrace]
  refine ⟨94827602200865151823170547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126436802934486869097560729 94827602200865151823170547)
  ·
    refine ⟨142241403301297727734755821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94827602200865151823170547 142241403301297727734755821)
    ·
      refine ⟨53340526237986647900533433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142241403301297727734755821 53340526237986647900533433)
      ·
        refine ⟨40005394678489985925400075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53340526237986647900533433 40005394678489985925400075)
        ·
          refine ⟨60008092017734978888100113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40005394678489985925400075 60008092017734978888100113)
          ·
            refine ⟨45006069013301234166075085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60008092017734978888100113 45006069013301234166075085)
            ·
              refine ⟨16877275879987962812278157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45006069013301234166075085 16877275879987962812278157)
              ·
                refine ⟨6328978454995486054604309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16877275879987962812278157 6328978454995486054604309)
                ·
                  refine ⟨296670865077913408809577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6328978454995486054604309 296670865077913408809577)
                  ·
                    rfl

theorem cell23_5199880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_5199880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199880 prefixEnd_5199880 := by exact prefixLift 5199880
  have htrace : WordTrace (prefixWord ++ tailWord_5199880) baseStart_5199880 baseEnd_5199880 := by
    simpa [prefixWord, tailWord_5199880, baseEnd_5199880] using wordTrace_append hprefix tailTrace_5199880
  have hstable : (prefixWord ++ tailWord_5199880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199880).length < 2 ^ (prefixWord ++ tailWord_5199880).sum := by decide
  have hdescent : baseEnd_5199880 < baseStart_5199880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199918 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5199918 : Nat := 118140960795 + 5199918 * 2 ^ 59
def prefixEnd_5199918 : Nat := 4983230072969 + 3 ^ 40 * 5199918 * 2
def baseEnd_5199918 : Nat := 890019099322030510203673

theorem tailTrace_5199918 : CollatzResearch.WordTrace tailWord_5199918 prefixEnd_5199918 890019099322030510203673 := by
  unfold tailWord_5199918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707073796949079517028051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126437726917061757424149605 23707073796949079517028051)
  ·
    refine ⟨35560610695423619275542077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23707073796949079517028051 35560610695423619275542077)
    ·
      refine ⟨13335229010783857228328279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35560610695423619275542077 13335229010783857228328279)
      ·
        refine ⟨20002843516175785842492419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13335229010783857228328279 20002843516175785842492419)
        ·
          refine ⟨30004265274263678763738629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20002843516175785842492419 30004265274263678763738629)
          ·
            refine ⟨5625799738924439768200993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30004265274263678763738629 5625799738924439768200993)
            ·
              refine ⟨4219349804193329826150745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5625799738924439768200993 4219349804193329826150745)
              ·
                refine ⟨3164512353144997369613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219349804193329826150745 3164512353144997369613059)
                ·
                  refine ⟨4746768529717496054419589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164512353144997369613059 4746768529717496054419589)
                  ·
                    refine ⟨890019099322030510203673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4746768529717496054419589 890019099322030510203673)
                    ·
                      rfl

theorem cell23_5199918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5199918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199918 prefixEnd_5199918 := by exact prefixLift 5199918
  have htrace : WordTrace (prefixWord ++ tailWord_5199918) baseStart_5199918 baseEnd_5199918 := by
    simpa [prefixWord, tailWord_5199918, baseEnd_5199918] using wordTrace_append hprefix tailTrace_5199918
  have hstable : (prefixWord ++ tailWord_5199918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199918).length < 2 ^ (prefixWord ++ tailWord_5199918).sum := by decide
  have hdescent : baseEnd_5199918 < baseStart_5199918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199964 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_5199964 : Nat := 118140960795 + 5199964 * 2 ^ 59
def prefixEnd_5199964 : Nat := 4983230072969 + 3 ^ 40 * 5199964 * 2
def baseEnd_5199964 : Nat := 2670080918076198350635807

theorem tailTrace_5199964 : CollatzResearch.WordTrace tailWord_5199964 prefixEnd_5199964 2670080918076198350635807 := by
  unfold tailWord_5199964
  simp only [CollatzResearch.WordTrace]
  refine ⟨94829134066712992996199473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126438845422283990661599297 94829134066712992996199473)
  ·
    refine ⟨71121850550034744747149605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94829134066712992996199473 71121850550034744747149605)
    ·
      refine ⟨13335346978131514640090551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71121850550034744747149605 13335346978131514640090551)
      ·
        refine ⟨20003020467197271960135827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13335346978131514640090551 20003020467197271960135827)
        ·
          refine ⟨30004530700795907940203741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20003020467197271960135827 30004530700795907940203741)
          ·
            refine ⟨11251699012798465477576403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30004530700795907940203741 11251699012798465477576403)
            ·
              refine ⟨16877548519197698216364605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11251699012798465477576403 16877548519197698216364605)
              ·
                refine ⟨6329080694699136831136727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16877548519197698216364605 6329080694699136831136727)
                ·
                  refine ⟨9493621042048705246705091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329080694699136831136727 9493621042048705246705091)
                  ·
                    refine ⟨14240431563073057870057637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9493621042048705246705091 14240431563073057870057637)
                    ·
                      refine ⟨2670080918076198350635807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14240431563073057870057637 2670080918076198350635807)
                      ·
                        rfl

theorem cell23_5199964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_5199964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199964 prefixEnd_5199964 := by exact prefixLift 5199964
  have htrace : WordTrace (prefixWord ++ tailWord_5199964) baseStart_5199964 baseEnd_5199964 := by
    simpa [prefixWord, tailWord_5199964, baseEnd_5199964] using wordTrace_append hprefix tailTrace_5199964
  have hstable : (prefixWord ++ tailWord_5199964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199964).length < 2 ^ (prefixWord ++ tailWord_5199964).sum := by decide
  have hdescent : baseEnd_5199964 < baseStart_5199964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5199981 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5199981 : Nat := 118140960795 + 5199981 * 2 ^ 59
def prefixEnd_5199981 : Nat := 4983230072969 + 3 ^ 40 * 5199981 * 2
def baseEnd_5199981 : Nat := 2670089647247324784123229

theorem tailTrace_5199981 : CollatzResearch.WordTrace tailWord_5199981 prefixEnd_5199981 2670089647247324784123229 := by
  unfold tailWord_5199981
  simp only [CollatzResearch.WordTrace]
  refine ⟨189658888174364397895767797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126439258782909598597178531 189658888174364397895767797)
  ·
    refine ⟨17780520766346662302728231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189658888174364397895767797 17780520766346662302728231)
    ·
      refine ⟨26670781149519993454092347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17780520766346662302728231 26670781149519993454092347)
      ·
        refine ⟨40006171724279990181138521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26670781149519993454092347 40006171724279990181138521)
        ·
          refine ⟨30004628793209992635853891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40006171724279990181138521 30004628793209992635853891)
          ·
            refine ⟨45006943189814988953780837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30004628793209992635853891 45006943189814988953780837)
            ·
              refine ⟨8438801848090310428833907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45006943189814988953780837 8438801848090310428833907)
              ·
                refine ⟨12658202772135465643250861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8438801848090310428833907 12658202772135465643250861)
                ·
                  refine ⟨4746826039550799616219073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12658202772135465643250861 4746826039550799616219073)
                  ·
                    refine ⟨3560119529663099712164305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746826039550799616219073 3560119529663099712164305)
                    ·
                      refine ⟨2670089647247324784123229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560119529663099712164305 2670089647247324784123229)
                      ·
                        rfl

theorem cell23_5199981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5199981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5199981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5199981 prefixEnd_5199981 := by exact prefixLift 5199981
  have htrace : WordTrace (prefixWord ++ tailWord_5199981) baseStart_5199981 baseEnd_5199981 := by
    simpa [prefixWord, tailWord_5199981, baseEnd_5199981] using wordTrace_append hprefix tailTrace_5199981
  have hstable : (prefixWord ++ tailWord_5199981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5199981).length < 2 ^ (prefixWord ++ tailWord_5199981).sum := by decide
  have hdescent : baseEnd_5199981 < baseStart_5199981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5199981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200001 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_5200001 : Nat := 118140960795 + 5200001 * 2 ^ 59
def prefixEnd_5200001 : Nat := 4983230072969 + 3 ^ 40 * 5200001 * 2
def baseEnd_5200001 : Nat := 2670099916860414705873137

theorem tailTrace_5200001 : CollatzResearch.WordTrace tailWord_5200001 prefixEnd_5200001 2670099916860414705873137 := by
  unfold tailWord_5200001
  simp only [CollatzResearch.WordTrace]
  refine ⟨189659617634291941311495857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126439745089527960874330571 189659617634291941311495857)
  ·
    refine ⟨142244713225718955983621893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189659617634291941311495857 142244713225718955983621893)
    ·
      refine ⟨26670883729822304246929105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142244713225718955983621893 26670883729822304246929105)
      ·
        refine ⟨20003162797366728185196829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26670883729822304246929105 20003162797366728185196829)
        ·
          refine ⟨7501186049012523069448811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20003162797366728185196829 7501186049012523069448811)
          ·
            refine ⟨11251779073518784604173217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501186049012523069448811 11251779073518784604173217)
            ·
              refine ⟨8438834305139088453129913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251779073518784604173217 8438834305139088453129913)
              ·
                refine ⟨6329125728854316339847435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438834305139088453129913 6329125728854316339847435)
                ·
                  refine ⟨9493688593281474509771153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329125728854316339847435 9493688593281474509771153)
                  ·
                    refine ⟨7120266444961105882328365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9493688593281474509771153 7120266444961105882328365)
                    ·
                      refine ⟨2670099916860414705873137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120266444961105882328365 2670099916860414705873137)
                      ·
                        rfl

theorem cell23_5200001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_5200001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200001 prefixEnd_5200001 := by exact prefixLift 5200001
  have htrace : WordTrace (prefixWord ++ tailWord_5200001) baseStart_5200001 baseEnd_5200001 := by
    simpa [prefixWord, tailWord_5200001, baseEnd_5200001] using wordTrace_append hprefix tailTrace_5200001
  have hstable : (prefixWord ++ tailWord_5200001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200001).length < 2 ^ (prefixWord ++ tailWord_5200001).sum := by decide
  have hdescent : baseEnd_5200001 < baseStart_5200001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200052 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5200052 : Nat := 118140960795 + 5200052 * 2 ^ 59
def prefixEnd_5200052 : Nat := 4983230072969 + 3 ^ 40 * 5200052 * 2
def baseEnd_5200052 : Nat := 2670126104373794006335403

theorem tailTrace_5200052 : CollatzResearch.WordTrace tailWord_5200052 prefixEnd_5200052 2670126104373794006335403 := by
  unfold tailWord_5200052
  simp only [CollatzResearch.WordTrace]
  refine ⟨94830738878553588510801205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126440985171404784681068273 94830738878553588510801205)
  ·
    refine ⟨8890381769864398922887613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94830738878553588510801205 8890381769864398922887613)
    ·
      refine ⟨3333893163699149596082855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8890381769864398922887613 3333893163699149596082855)
      ·
        refine ⟨5000839745548724394124283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333893163699149596082855 5000839745548724394124283)
        ·
          refine ⟨7501259618323086591186425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000839745548724394124283 7501259618323086591186425)
          ·
            refine ⟨5625944713742314943389819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7501259618323086591186425 5625944713742314943389819)
            ·
              refine ⟨8438917070613472415084729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625944713742314943389819 8438917070613472415084729)
              ·
                refine ⟨6329187802960104311313547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438917070613472415084729 6329187802960104311313547)
                ·
                  refine ⟨9493781704440156466970321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329187802960104311313547 9493781704440156466970321)
                  ·
                    refine ⟨7120336278330117350227741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9493781704440156466970321 7120336278330117350227741)
                    ·
                      refine ⟨2670126104373794006335403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120336278330117350227741 2670126104373794006335403)
                      ·
                        rfl

theorem cell23_5200052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5200052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200052 prefixEnd_5200052 := by exact prefixLift 5200052
  have htrace : WordTrace (prefixWord ++ tailWord_5200052) baseStart_5200052 baseEnd_5200052 := by
    simpa [prefixWord, tailWord_5200052, baseEnd_5200052] using wordTrace_append hprefix tailTrace_5200052
  have hstable : (prefixWord ++ tailWord_5200052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200052).length < 2 ^ (prefixWord ++ tailWord_5200052).sum := by decide
  have hdescent : baseEnd_5200052 < baseStart_5200052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200087 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_5200087 : Nat := 118140960795 + 5200087 * 2 ^ 59
def prefixEnd_5200087 : Nat := 4983230072969 + 3 ^ 40 * 5200087 * 2
def baseEnd_5200087 : Nat := 2670144076196701369397741

theorem tailTrace_5200087 : CollatzResearch.WordTrace tailWord_5200087 prefixEnd_5200087 2670144076196701369397741 := by
  unfold tailWord_5200087
  simp only [CollatzResearch.WordTrace]
  refine ⟨189662754311980377999126515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126441836207986918666084343 189662754311980377999126515)
  ·
    refine ⟨284494131467970566998689773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189662754311980377999126515 284494131467970566998689773)
    ·
      refine ⟨106685299300488962624508665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284494131467970566998689773 106685299300488962624508665)
      ·
        refine ⟨80013974475366721968381499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106685299300488962624508665 80013974475366721968381499)
        ·
          refine ⟨120020961713050082952572249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80013974475366721968381499 120020961713050082952572249)
          ·
            refine ⟨90015721284787562214429187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120020961713050082952572249 90015721284787562214429187)
            ·
              refine ⟨135023581927181343321643781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90015721284787562214429187 135023581927181343321643781)
              ·
                refine ⟨25316921611346501872808209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135023581927181343321643781 25316921611346501872808209)
                ·
                  refine ⟨18987691208509876404606157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25316921611346501872808209 18987691208509876404606157)
                  ·
                    refine ⟨7120384203191203651727309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18987691208509876404606157 7120384203191203651727309)
                    ·
                      refine ⟨2670144076196701369397741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120384203191203651727309 2670144076196701369397741)
                      ·
                        rfl

theorem cell23_5200087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_5200087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200087 prefixEnd_5200087 := by exact prefixLift 5200087
  have htrace : WordTrace (prefixWord ++ tailWord_5200087) baseStart_5200087 baseEnd_5200087 := by
    simpa [prefixWord, tailWord_5200087, baseEnd_5200087] using wordTrace_append hprefix tailTrace_5200087
  have hstable : (prefixWord ++ tailWord_5200087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200087).length < 2 ^ (prefixWord ++ tailWord_5200087).sum := by decide
  have hdescent : baseEnd_5200087 < baseStart_5200087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200088 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_5200088 : Nat := 118140960795 + 5200088 * 2 ^ 59
def prefixEnd_5200088 : Nat := 4983230072969 + 3 ^ 40 * 5200088 * 2
def baseEnd_5200088 : Nat := 2670144589677355865485237

theorem tailTrace_5200088 : CollatzResearch.WordTrace tailWord_5200088 prefixEnd_5200088 2670144589677355865485237 := by
  unfold tailWord_5200088
  simp only [CollatzResearch.WordTrace]
  refine ⟨94831395392488377584956459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126441860523317836779941945 94831395392488377584956459)
  ·
    refine ⟨142247093088732566377434689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94831395392488377584956459 142247093088732566377434689)
    ·
      refine ⟨106685319816549424783076017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142247093088732566377434689 106685319816549424783076017)
      ·
        refine ⟨80013989862412068587307013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106685319816549424783076017 80013989862412068587307013)
        ·
          refine ⟨15002623099202262860120065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80013989862412068587307013 15002623099202262860120065)
          ·
            refine ⟨11251967324401697145090049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15002623099202262860120065 11251967324401697145090049)
            ·
              refine ⟨8438975493301272858817537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11251967324401697145090049 8438975493301272858817537)
              ·
                refine ⟨6329231619975954644113153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438975493301272858817537 6329231619975954644113153)
                ·
                  refine ⟨4746923714981965983084865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329231619975954644113153 4746923714981965983084865)
                  ·
                    refine ⟨3560192786236474487313649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746923714981965983084865 3560192786236474487313649)
                    ·
                      refine ⟨2670144589677355865485237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560192786236474487313649 2670144589677355865485237)
                      ·
                        rfl

theorem cell23_5200088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_5200088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200088 prefixEnd_5200088 := by exact prefixLift 5200088
  have htrace : WordTrace (prefixWord ++ tailWord_5200088) baseStart_5200088 baseEnd_5200088 := by
    simpa [prefixWord, tailWord_5200088, baseEnd_5200088] using wordTrace_append hprefix tailTrace_5200088
  have hstable : (prefixWord ++ tailWord_5200088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200088).length < 2 ^ (prefixWord ++ tailWord_5200088).sum := by decide
  have hdescent : baseEnd_5200088 < baseStart_5200088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200098 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5200098 : Nat := 118140960795 + 5200098 * 2 ^ 59
def prefixEnd_5200098 : Nat := 4983230072969 + 3 ^ 40 * 5200098 * 2
def baseEnd_5200098 : Nat := 890049908161300275453397

theorem tailTrace_5200098 : CollatzResearch.WordTrace tailWord_5200098 prefixEnd_5200098 890049908161300275453397 := by
  unfold tailWord_5200098
  simp only [CollatzResearch.WordTrace]
  refine ⟨47415788878735131719444237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126442103676627017918517965 47415788878735131719444237)
  ·
    refine ⟨17780920829525674394791589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47415788878735131719444237 17780920829525674394791589)
    ·
      refine ⟨3333922655536063949023423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17780920829525674394791589 3333922655536063949023423)
      ·
        refine ⟨5000883983304095923535135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333922655536063949023423 5000883983304095923535135)
        ·
          refine ⟨7501325974956143885302703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000883983304095923535135 7501325974956143885302703)
          ·
            refine ⟨11251988962434215827954055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501325974956143885302703 11251988962434215827954055)
            ·
              refine ⟨16877983443651323741931083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11251988962434215827954055 16877983443651323741931083)
              ·
                refine ⟨25316975165476985612896625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16877983443651323741931083 25316975165476985612896625)
                ·
                  refine ⟨18987731374107739209672469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25316975165476985612896625 18987731374107739209672469)
                  ·
                    refine ⟨890049908161300275453397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18987731374107739209672469 890049908161300275453397)
                    ·
                      rfl

theorem cell23_5200098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5200098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200098 prefixEnd_5200098 := by exact prefixLift 5200098
  have htrace : WordTrace (prefixWord ++ tailWord_5200098) baseStart_5200098 baseEnd_5200098 := by
    simpa [prefixWord, tailWord_5200098, baseEnd_5200098] using wordTrace_append hprefix tailTrace_5200098
  have hstable : (prefixWord ++ tailWord_5200098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200098).length < 2 ^ (prefixWord ++ tailWord_5200098).sum := by decide
  have hdescent : baseEnd_5200098 < baseStart_5200098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200104 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5200104 : Nat := 118140960795 + 5200104 * 2 ^ 59
def prefixEnd_5200104 : Nat := 4983230072969 + 3 ^ 40 * 5200104 * 2
def baseEnd_5200104 : Nat := 2670152805367827802885163

theorem tailTrace_5200104 : CollatzResearch.WordTrace tailWord_5200104 prefixEnd_5200104 2670152805367827802885163 := by
  unfold tailWord_5200104
  simp only [CollatzResearch.WordTrace]
  refine ⟨94831687176459394951247683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126442249568612526601663577 94831687176459394951247683)
  ·
    refine ⟨142247530764689092426871525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94831687176459394951247683 142247530764689092426871525)
    ·
      refine ⟨26671412018379204830038411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142247530764689092426871525 26671412018379204830038411)
      ·
        refine ⟨40007118027568807245057617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26671412018379204830038411 40007118027568807245057617)
        ·
          refine ⟨30005338520676605433793213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40007118027568807245057617 30005338520676605433793213)
          ·
            refine ⟨11252001945253727037672455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30005338520676605433793213 11252001945253727037672455)
            ·
              refine ⟨16878002917880590556508683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252001945253727037672455 16878002917880590556508683)
              ·
                refine ⟨25317004376820885834763025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16878002917880590556508683 25317004376820885834763025)
                ·
                  refine ⟨18987753282615664376072269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25317004376820885834763025 18987753282615664376072269)
                  ·
                    refine ⟨7120407480980874141027101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18987753282615664376072269 7120407480980874141027101)
                    ·
                      refine ⟨2670152805367827802885163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120407480980874141027101 2670152805367827802885163)
                      ·
                        rfl

theorem cell23_5200104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5200104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200104 prefixEnd_5200104 := by exact prefixLift 5200104
  have htrace : WordTrace (prefixWord ++ tailWord_5200104) baseStart_5200104 baseEnd_5200104 := by
    simpa [prefixWord, tailWord_5200104, baseEnd_5200104] using wordTrace_append hprefix tailTrace_5200104
  have hstable : (prefixWord ++ tailWord_5200104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200104).length < 2 ^ (prefixWord ++ tailWord_5200104).sum := by decide
  have hdescent : baseEnd_5200104 < baseStart_5200104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200124 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_5200124 : Nat := 118140960795 + 5200124 * 2 ^ 59
def prefixEnd_5200124 : Nat := 4983230072969 + 3 ^ 40 * 5200124 * 2
def baseEnd_5200124 : Nat := 890054358326972574878357

theorem tailTrace_5200124 : CollatzResearch.WordTrace tailWord_5200124 prefixEnd_5200124 890054358326972574878357 := by
  unfold tailWord_5200124
  simp only [CollatzResearch.WordTrace]
  refine ⟨94832051906423166659111713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126442735875230888878815617 94832051906423166659111713)
  ·
    refine ⟨71124038929817374994333785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94832051906423166659111713 71124038929817374994333785)
    ·
      refine ⟨53343029197363031245750339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71124038929817374994333785 53343029197363031245750339)
      ·
        refine ⟨80014543796044546868625509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53343029197363031245750339 80014543796044546868625509)
        ·
          refine ⟨15002726961758352537867283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80014543796044546868625509 15002726961758352537867283)
          ·
            refine ⟨22504090442637528806800925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15002726961758352537867283 22504090442637528806800925)
            ·
              refine ⟨8439033915989073302550347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22504090442637528806800925 8439033915989073302550347)
              ·
                refine ⟨12658550873983609953825521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8439033915989073302550347 12658550873983609953825521)
                ·
                  refine ⟨9493913155487707465369141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12658550873983609953825521 9493913155487707465369141)
                  ·
                    refine ⟨890054358326972574878357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9493913155487707465369141 890054358326972574878357)
                    ·
                      rfl

theorem cell23_5200124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_5200124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200124 prefixEnd_5200124 := by exact prefixLift 5200124
  have htrace : WordTrace (prefixWord ++ tailWord_5200124) baseStart_5200124 baseEnd_5200124 := by
    simpa [prefixWord, tailWord_5200124, baseEnd_5200124] using wordTrace_append hprefix tailTrace_5200124
  have hstable : (prefixWord ++ tailWord_5200124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200124).length < 2 ^ (prefixWord ++ tailWord_5200124).sum := by decide
  have hdescent : baseEnd_5200124 < baseStart_5200124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200127 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_5200127 : Nat := 118140960795 + 5200127 * 2 ^ 59
def prefixEnd_5200127 : Nat := 4983230072969 + 3 ^ 40 * 5200127 * 2
def baseEnd_5200127 : Nat := 2670164615422881212897557

theorem tailTrace_5200127 : CollatzResearch.WordTrace tailWord_5200127 prefixEnd_5200127 2670164615422881212897557 := by
  unfold tailWord_5200127
  simp only [CollatzResearch.WordTrace]
  refine ⟨189664213231835464830582635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126442808821223643220388423 189664213231835464830582635)
  ·
    refine ⟨284496319847753197245873953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189664213231835464830582635 284496319847753197245873953)
    ·
      refine ⟨213372239885814897934405465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284496319847753197245873953 213372239885814897934405465)
      ·
        refine ⟨160029179914361173450804099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213372239885814897934405465 160029179914361173450804099)
        ·
          refine ⟨240043769871541760176206149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160029179914361173450804099 240043769871541760176206149)
          ·
            refine ⟨45008206850914080033038653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240043769871541760176206149 45008206850914080033038653)
            ·
              refine ⟨16878077569092780012389495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45008206850914080033038653 16878077569092780012389495)
              ·
                refine ⟨25317116353639170018584243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16878077569092780012389495 25317116353639170018584243)
                ·
                  refine ⟨37975674530458755027876365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25317116353639170018584243 37975674530458755027876365)
                  ·
                    refine ⟨14240877948922033135453637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37975674530458755027876365 14240877948922033135453637)
                    ·
                      refine ⟨2670164615422881212897557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14240877948922033135453637 2670164615422881212897557)
                      ·
                        rfl

theorem cell23_5200127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_5200127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200127 prefixEnd_5200127 := by exact prefixLift 5200127
  have htrace : WordTrace (prefixWord ++ tailWord_5200127) baseStart_5200127 baseEnd_5200127 := by
    simpa [prefixWord, tailWord_5200127, baseEnd_5200127] using wordTrace_append hprefix tailTrace_5200127
  have hstable : (prefixWord ++ tailWord_5200127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200127).length < 2 ^ (prefixWord ++ tailWord_5200127).sum := by decide
  have hdescent : baseEnd_5200127 < baseStart_5200127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200164 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_5200164 : Nat := 118140960795 + 5200164 * 2 ^ 59
def prefixEnd_5200164 : Nat := 4983230072969 + 3 ^ 40 * 5200164 * 2
def baseEnd_5200164 : Nat := 2670183614207097568134887

theorem tailTrace_5200164 : CollatzResearch.WordTrace tailWord_5200164 prefixEnd_5200164 2670183614207097568134887 := by
  unfold tailWord_5200164
  simp only [CollatzResearch.WordTrace]
  refine ⟨94832781366350710074839773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126443708488467613433119697 94832781366350710074839773)
  ·
    refine ⟨35562293012381516278064915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94832781366350710074839773 35562293012381516278064915)
    ·
      refine ⟨53343439518572274417097373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35562293012381516278064915 53343439518572274417097373)
      ·
        refine ⟨20003789819464602906411515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53343439518572274417097373 20003789819464602906411515)
        ·
          refine ⟨30005684729196904359617273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20003789819464602906411515 30005684729196904359617273)
          ·
            refine ⟨22504263546897678269712955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30005684729196904359617273 22504263546897678269712955)
            ·
              refine ⟨33756395320346517404569433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22504263546897678269712955 33756395320346517404569433)
              ·
                refine ⟨25317296490259888053427075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33756395320346517404569433 25317296490259888053427075)
                ·
                  refine ⟨37975944735389832080140613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25317296490259888053427075 37975944735389832080140613)
                  ·
                    refine ⟨7120489637885593515026365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37975944735389832080140613 7120489637885593515026365)
                    ·
                      refine ⟨2670183614207097568134887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120489637885593515026365 2670183614207097568134887)
                      ·
                        rfl

theorem cell23_5200164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_5200164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200164 prefixEnd_5200164 := by exact prefixLift 5200164
  have htrace : WordTrace (prefixWord ++ tailWord_5200164) baseStart_5200164 baseEnd_5200164 := by
    simpa [prefixWord, tailWord_5200164, baseEnd_5200164] using wordTrace_append hprefix tailTrace_5200164
  have hstable : (prefixWord ++ tailWord_5200164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200164).length < 2 ^ (prefixWord ++ tailWord_5200164).sum := by decide
  have hdescent : baseEnd_5200164 < baseStart_5200164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200197 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_5200197 : Nat := 118140960795 + 5200197 * 2 ^ 59
def prefixEnd_5200197 : Nat := 4983230072969 + 3 ^ 40 * 5200197 * 2
def baseEnd_5200197 : Nat := 890066853022898646340745

theorem tailTrace_5200197 : CollatzResearch.WordTrace tailWord_5200197 prefixEnd_5200197 890066853022898646340745 := by
  unfold tailWord_5200197
  simp only [CollatzResearch.WordTrace]
  refine ⟨189666766341581866785630845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126444510894387911190420563 189666766341581866785630845)
  ·
    refine ⟨71125037378093200044611567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189666766341581866785630845 71125037378093200044611567)
    ·
      refine ⟨106687556067139800066917351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71125037378093200044611567 106687556067139800066917351)
      ·
        refine ⟨160031334100709700100376027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106687556067139800066917351 160031334100709700100376027)
        ·
          refine ⟨240047001151064550150564041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160031334100709700100376027 240047001151064550150564041)
          ·
            refine ⟨180035250863298412612923031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240047001151064550150564041 180035250863298412612923031)
            ·
              refine ⟨270052876294947618919384547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180035250863298412612923031 270052876294947618919384547)
              ·
                refine ⟨405079314442421428379076821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270052876294947618919384547 405079314442421428379076821)
                ·
                  refine ⟨9494046432244252227634613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 405079314442421428379076821 9494046432244252227634613)
                  ·
                    refine ⟨890066853022898646340745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9494046432244252227634613 890066853022898646340745)
                    ·
                      rfl

theorem cell23_5200197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_5200197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200197 prefixEnd_5200197 := by exact prefixLift 5200197
  have htrace : WordTrace (prefixWord ++ tailWord_5200197) baseStart_5200197 baseEnd_5200197 := by
    simpa [prefixWord, tailWord_5200197, baseEnd_5200197] using wordTrace_append hprefix tailTrace_5200197
  have hstable : (prefixWord ++ tailWord_5200197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200197).length < 2 ^ (prefixWord ++ tailWord_5200197).sum := by decide
  have hdescent : baseEnd_5200197 < baseStart_5200197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200217 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_5200217 : Nat := 118140960795 + 5200217 * 2 ^ 59
def prefixEnd_5200217 : Nat := 4983230072969 + 3 ^ 40 * 5200217 * 2
def baseEnd_5200217 : Nat := 2670210828681785860772143

theorem tailTrace_5200217 : CollatzResearch.WordTrace tailWord_5200217 prefixEnd_5200217 2670210828681785860772143 := by
  unfold tailWord_5200217
  simp only [CollatzResearch.WordTrace]
  refine ⟨189667495801509410201358905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126444997201006273467572603 189667495801509410201358905)
  ·
    refine ⟨142250621851132057651019179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189667495801509410201358905 142250621851132057651019179)
    ·
      refine ⟨213375932776698086476528769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142250621851132057651019179 213375932776698086476528769)
      ·
        refine ⟨160031949582523564857396577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213375932776698086476528769 160031949582523564857396577)
        ·
          refine ⟨120023962186892673643047433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160031949582523564857396577 120023962186892673643047433)
          ·
            refine ⟨90017971640169505232285575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120023962186892673643047433 90017971640169505232285575)
            ·
              refine ⟨135026957460254257848428363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90017971640169505232285575 135026957460254257848428363)
              ·
                refine ⟨202540436190381386772642545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135026957460254257848428363 202540436190381386772642545)
                ·
                  refine ⟨151905327142786040079481909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202540436190381386772642545 151905327142786040079481909)
                  ·
                    refine ⟨14241124419636191257451429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151905327142786040079481909 14241124419636191257451429)
                    ·
                      refine ⟨2670210828681785860772143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14241124419636191257451429 2670210828681785860772143)
                      ·
                        rfl

theorem cell23_5200217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_5200217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200217 prefixEnd_5200217 := by exact prefixLift 5200217
  have htrace : WordTrace (prefixWord ++ tailWord_5200217) baseStart_5200217 baseEnd_5200217 := by
    simpa [prefixWord, tailWord_5200217, baseEnd_5200217] using wordTrace_append hprefix tailTrace_5200217
  have hstable : (prefixWord ++ tailWord_5200217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200217).length < 2 ^ (prefixWord ++ tailWord_5200217).sum := by decide
  have hdescent : baseEnd_5200217 < baseStart_5200217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200231 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 1, 5]
def baseStart_5200231 : Nat := 118140960795 + 5200231 * 2 ^ 59
def prefixEnd_5200231 : Nat := 4983230072969 + 3 ^ 40 * 5200231 * 2
def baseEnd_5200231 : Nat := 890072672470316268665693

theorem tailTrace_5200231 : CollatzResearch.WordTrace tailWord_5200231 prefixEnd_5200231 890072672470316268665693 := by
  unfold tailWord_5200231
  simp only [CollatzResearch.WordTrace]
  refine ⟨189668006423458690592368547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126445337615639127061579031 189668006423458690592368547)
  ·
    refine ⟨284502009635188035888552821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189668006423458690592368547 284502009635188035888552821)
    ·
      refine ⟨26672063403298878364551827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284502009635188035888552821 26672063403298878364551827)
      ·
        refine ⟨40008095104948317546827741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26672063403298878364551827 40008095104948317546827741)
        ·
          refine ⟨15003035664355619080060403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40008095104948317546827741 15003035664355619080060403)
          ·
            refine ⟨22504553496533428620090605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15003035664355619080060403 22504553496533428620090605)
            ·
              refine ⟨8439207561200035732533977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22504553496533428620090605 8439207561200035732533977)
              ·
                refine ⟨6329405670900026799400483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8439207561200035732533977 6329405670900026799400483)
                ·
                  refine ⟨9494108506350040199100725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329405670900026799400483 9494108506350040199100725)
                  ·
                    refine ⟨890072672470316268665693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9494108506350040199100725 890072672470316268665693)
                    ·
                      rfl

theorem cell23_5200231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_5200231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200231 prefixEnd_5200231 := by exact prefixLift 5200231
  have htrace : WordTrace (prefixWord ++ tailWord_5200231) baseStart_5200231 baseEnd_5200231 := by
    simpa [prefixWord, tailWord_5200231, baseEnd_5200231] using wordTrace_append hprefix tailTrace_5200231
  have hstable : (prefixWord ++ tailWord_5200231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200231).length < 2 ^ (prefixWord ++ tailWord_5200231).sum := by decide
  have hdescent : baseEnd_5200231 < baseStart_5200231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200247 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_5200247 : Nat := 118140960795 + 5200247 * 2 ^ 59
def prefixEnd_5200247 : Nat := 4983230072969 + 3 ^ 40 * 5200247 * 2
def baseEnd_5200247 : Nat := 2670226233101420743397005

theorem tailTrace_5200247 : CollatzResearch.WordTrace tailWord_5200247 prefixEnd_5200247 2670226233101420743397005 := by
  unfold tailWord_5200247
  simp only [CollatzResearch.WordTrace]
  refine ⟨189668589991400725324950995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126445726660933816883300663 189668589991400725324950995)
  ·
    refine ⟨284502884987101087987426493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189668589991400725324950995 284502884987101087987426493)
    ·
      refine ⟨106688581870162907995284935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284502884987101087987426493 106688581870162907995284935)
      ·
        refine ⟨160032872805244361992927403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106688581870162907995284935 160032872805244361992927403)
        ·
          refine ⟨240049309207866542989391105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160032872805244361992927403 240049309207866542989391105)
          ·
            refine ⟨180036981905899907242043329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240049309207866542989391105 180036981905899907242043329)
            ·
              refine ⟨135027736429424930431532497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180036981905899907242043329 135027736429424930431532497)
              ·
                refine ⟨101270802322068697823649373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135027736429424930431532497 101270802322068697823649373)
                ·
                  refine ⟨37976550870775761683868515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101270802322068697823649373 37976550870775761683868515)
                  ·
                    refine ⟨56964826306163642525802773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37976550870775761683868515 56964826306163642525802773)
                    ·
                      refine ⟨2670226233101420743397005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56964826306163642525802773 2670226233101420743397005)
                      ·
                        rfl

theorem cell23_5200247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_5200247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200247 prefixEnd_5200247 := by exact prefixLift 5200247
  have htrace : WordTrace (prefixWord ++ tailWord_5200247) baseStart_5200247 baseEnd_5200247 := by
    simpa [prefixWord, tailWord_5200247, baseEnd_5200247] using wordTrace_append hprefix tailTrace_5200247
  have hstable : (prefixWord ++ tailWord_5200247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200247).length < 2 ^ (prefixWord ++ tailWord_5200247).sum := by decide
  have hdescent : baseEnd_5200247 < baseStart_5200247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200264 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_5200264 : Nat := 118140960795 + 5200264 * 2 ^ 59
def prefixEnd_5200264 : Nat := 4983230072969 + 3 ^ 40 * 5200264 * 2
def baseEnd_5200264 : Nat := 2670234962272547176884427

theorem tailTrace_5200264 : CollatzResearch.WordTrace tailWord_5200264 prefixEnd_5200264 2670234962272547176884427 := by
  unfold tailWord_5200264
  simp only [CollatzResearch.WordTrace]
  refine ⟨94834605016169568614159923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126446140021559424818879897 94834605016169568614159923)
  ·
    refine ⟨142251907524254352921239885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94834605016169568614159923 142251907524254352921239885)
    ·
      refine ⟨53344465321595382345464957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142251907524254352921239885 53344465321595382345464957)
      ·
        refine ⟨20004174495598268379549359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53344465321595382345464957 20004174495598268379549359)
        ·
          refine ⟨30006261743397402569324039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20004174495598268379549359 30006261743397402569324039)
          ·
            refine ⟨45009392615096103853986059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30006261743397402569324039 45009392615096103853986059)
            ·
              refine ⟨67514088922644155780979089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45009392615096103853986059 67514088922644155780979089)
              ·
                refine ⟨50635566691983116835734317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67514088922644155780979089 50635566691983116835734317)
                ·
                  refine ⟨18988337509493668813400369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50635566691983116835734317 18988337509493668813400369)
                  ·
                    refine ⟨14241253132120251610050277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18988337509493668813400369 14241253132120251610050277)
                    ·
                      refine ⟨2670234962272547176884427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14241253132120251610050277 2670234962272547176884427)
                      ·
                        rfl

theorem cell23_5200264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_5200264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200264 prefixEnd_5200264 := by exact prefixLift 5200264
  have htrace : WordTrace (prefixWord ++ tailWord_5200264) baseStart_5200264 baseEnd_5200264 := by
    simpa [prefixWord, tailWord_5200264, baseEnd_5200264] using wordTrace_append hprefix tailTrace_5200264
  have hstable : (prefixWord ++ tailWord_5200264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200264).length < 2 ^ (prefixWord ++ tailWord_5200264).sum := by decide
  have hdescent : baseEnd_5200264 < baseStart_5200264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200285 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_5200285 : Nat := 118140960795 + 5200285 * 2 ^ 59
def prefixEnd_5200285 : Nat := 4983230072969 + 3 ^ 40 * 5200285 * 2
def baseEnd_5200285 : Nat := 2670245745366291594721831

theorem tailTrace_5200285 : CollatzResearch.WordTrace tailWord_5200285 prefixEnd_5200285 2670245745366291594721831 := by
  unfold tailWord_5200285
  simp only [CollatzResearch.WordTrace]
  refine ⟨189669975965263057814834309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126446650643508705209889539 189669975965263057814834309)
  ·
    refine ⟨35563120493486823340281433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189669975965263057814834309 35563120493486823340281433)
    ·
      refine ⟨26672340370115117505211075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35563120493486823340281433 26672340370115117505211075)
      ·
        refine ⟨40008510555172676257816613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26672340370115117505211075 40008510555172676257816613)
        ·
          refine ⟨7501595729094876798340615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40008510555172676257816613 7501595729094876798340615)
          ·
            refine ⟨11252393593642315197510923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501595729094876798340615 11252393593642315197510923)
            ·
              refine ⟨16878590390463472796266385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252393593642315197510923 16878590390463472796266385)
              ·
                refine ⟨12658942792847604597199789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16878590390463472796266385 12658942792847604597199789)
                ·
                  refine ⟨4747103547317851723949921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12658942792847604597199789 4747103547317851723949921)
                  ·
                    refine ⟨3560327660488388792962441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4747103547317851723949921 3560327660488388792962441)
                    ·
                      refine ⟨2670245745366291594721831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560327660488388792962441 2670245745366291594721831)
                      ·
                        rfl

theorem cell23_5200285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_5200285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200285 prefixEnd_5200285 := by exact prefixLift 5200285
  have htrace : WordTrace (prefixWord ++ tailWord_5200285) baseStart_5200285 baseEnd_5200285 := by
    simpa [prefixWord, tailWord_5200285, baseEnd_5200285] using wordTrace_append hprefix tailTrace_5200285
  have hstable : (prefixWord ++ tailWord_5200285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200285).length < 2 ^ (prefixWord ++ tailWord_5200285).sum := by decide
  have hdescent : baseEnd_5200285 < baseStart_5200285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200305 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5200305 : Nat := 118140960795 + 5200305 * 2 ^ 59
def prefixEnd_5200305 : Nat := 4983230072969 + 3 ^ 40 * 5200305 * 2
def baseEnd_5200305 : Nat := 2670256014979381516471739

theorem tailTrace_5200305 : CollatzResearch.WordTrace tailWord_5200305 prefixEnd_5200305 2670256014979381516471739 := by
  unfold tailWord_5200305
  simp only [CollatzResearch.WordTrace]
  refine ⟨189670705425190601230562369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126447136950127067487041579 189670705425190601230562369)
  ·
    refine ⟨142253029068892950922921777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189670705425190601230562369 142253029068892950922921777)
    ·
      refine ⟨106689771801669713192191333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142253029068892950922921777 106689771801669713192191333)
      ·
        refine ⟨20004332212813071223535875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106689771801669713192191333 20004332212813071223535875)
        ·
          refine ⟨30006498319219606835303813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20004332212813071223535875 30006498319219606835303813)
          ·
            refine ⟨5626218434853676281619465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30006498319219606835303813 5626218434853676281619465)
            ·
              refine ⟨4219663826140257211214599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626218434853676281619465 4219663826140257211214599)
              ·
                refine ⟨6329495739210385816821899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219663826140257211214599 6329495739210385816821899)
                ·
                  refine ⟨9494243608815578725232849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329495739210385816821899 9494243608815578725232849)
                  ·
                    refine ⟨7120682706611684043924637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9494243608815578725232849 7120682706611684043924637)
                    ·
                      refine ⟨2670256014979381516471739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120682706611684043924637 2670256014979381516471739)
                      ·
                        rfl

theorem cell23_5200305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5200305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200305 prefixEnd_5200305 := by exact prefixLift 5200305
  have htrace : WordTrace (prefixWord ++ tailWord_5200305) baseStart_5200305 baseEnd_5200305 := by
    simpa [prefixWord, tailWord_5200305, baseEnd_5200305] using wordTrace_append hprefix tailTrace_5200305
  have hstable : (prefixWord ++ tailWord_5200305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200305).length < 2 ^ (prefixWord ++ tailWord_5200305).sum := by decide
  have hdescent : baseEnd_5200305 < baseStart_5200305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200308 : List Nat := [2, 5, 2, 2, 1, 1, 10]
def baseStart_5200308 : Nat := 118140960795 + 5200308 * 2 ^ 59
def prefixEnd_5200308 : Nat := 4983230072969 + 3 ^ 40 * 5200308 * 2
def baseEnd_5200308 : Nat := 32966142659522777836225

theorem tailTrace_5200308 : CollatzResearch.WordTrace tailWord_5200308 prefixEnd_5200308 32966142659522777836225 := by
  unfold tailWord_5200308
  simp only [CollatzResearch.WordTrace]
  refine ⟨94835407422089866371460789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126447209896119821828614385 94835407422089866371460789)
  ·
    refine ⟨8890819445820924972324449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94835407422089866371460789 8890819445820924972324449)
    ·
      refine ⟨6668114584365693729243337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8890819445820924972324449 6668114584365693729243337)
      ·
        refine ⟨5001085938274270296932503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6668114584365693729243337 5001085938274270296932503)
        ·
          refine ⟨7501628907411405445398755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001085938274270296932503 7501628907411405445398755)
          ·
            refine ⟨11252443361117108168098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501628907411405445398755 11252443361117108168098133)
            ·
              refine ⟨32966142659522777836225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11252443361117108168098133 32966142659522777836225)
              ·
                rfl

theorem cell23_5200308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 10].length) (baseStart_5200308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200308 prefixEnd_5200308 := by exact prefixLift 5200308
  have htrace : WordTrace (prefixWord ++ tailWord_5200308) baseStart_5200308 baseEnd_5200308 := by
    simpa [prefixWord, tailWord_5200308, baseEnd_5200308] using wordTrace_append hprefix tailTrace_5200308
  have hstable : (prefixWord ++ tailWord_5200308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200308).length < 2 ^ (prefixWord ++ tailWord_5200308).sum := by decide
  have hdescent : baseEnd_5200308 < baseStart_5200308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200344 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_5200344 : Nat := 118140960795 + 5200344 * 2 ^ 59
def prefixEnd_5200344 : Nat := 4983230072969 + 3 ^ 40 * 5200344 * 2
def baseEnd_5200344 : Nat := 2670276040724906863884059

theorem tailTrace_5200344 : CollatzResearch.WordTrace tailWord_5200344 prefixEnd_5200344 2670276040724906863884059 := by
  unfold tailWord_5200344
  simp only [CollatzResearch.WordTrace]
  refine ⟨94836063936024655445616043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126448085248032873927488057 94836063936024655445616043)
  ·
    refine ⟨142254095904036983168424065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94836063936024655445616043 142254095904036983168424065)
    ·
      refine ⟨106690571928027737376318049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142254095904036983168424065 106690571928027737376318049)
      ·
        refine ⟨80017928946020803032238537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106690571928027737376318049 80017928946020803032238537)
        ·
          refine ⟨60013446709515602274178903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80017928946020803032238537 60013446709515602274178903)
          ·
            refine ⟨90020170064273403411268355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60013446709515602274178903 90020170064273403411268355)
            ·
              refine ⟨135030255096410105116902533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90020170064273403411268355 135030255096410105116902533)
              ·
                refine ⟨25318172830576894709419225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135030255096410105116902533 25318172830576894709419225)
                ·
                  refine ⟨18988629622932671032064419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25318172830576894709419225 18988629622932671032064419)
                  ·
                    refine ⟨28482944434399006548096629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18988629622932671032064419 28482944434399006548096629)
                    ·
                      refine ⟨2670276040724906863884059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28482944434399006548096629 2670276040724906863884059)
                      ·
                        rfl

theorem cell23_5200344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_5200344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200344 prefixEnd_5200344 := by exact prefixLift 5200344
  have htrace : WordTrace (prefixWord ++ tailWord_5200344) baseStart_5200344 baseEnd_5200344 := by
    simpa [prefixWord, tailWord_5200344, baseEnd_5200344] using wordTrace_append hprefix tailTrace_5200344
  have hstable : (prefixWord ++ tailWord_5200344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200344).length < 2 ^ (prefixWord ++ tailWord_5200344).sum := by decide
  have hdescent : baseEnd_5200344 < baseStart_5200344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200386 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5200386 : Nat := 118140960795 + 5200386 * 2 ^ 59
def prefixEnd_5200386 : Nat := 4983230072969 + 3 ^ 40 * 5200386 * 2
def baseEnd_5200386 : Nat := 2670297606912395699558867

theorem tailTrace_5200386 : CollatzResearch.WordTrace tailWord_5200386 prefixEnd_5200386 2670297606912395699558867 := by
  unfold tailWord_5200386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47418414934474288016065253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126449106491931434709507341 47418414934474288016065253)
  ·
    refine ⟨8890952800213929003012235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47418414934474288016065253 8890952800213929003012235)
    ·
      refine ⟨13336429200320893504518353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8890952800213929003012235 13336429200320893504518353)
      ·
        refine ⟨10002321900240670128388765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13336429200320893504518353 10002321900240670128388765)
        ·
          refine ⟨3750870712590251298145787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10002321900240670128388765 3750870712590251298145787)
          ·
            refine ⟨5626306068885376947218681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750870712590251298145787 5626306068885376947218681)
            ·
              refine ⟨4219729551664032710414011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626306068885376947218681 4219729551664032710414011)
              ·
                refine ⟨6329594327496049065621017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219729551664032710414011 6329594327496049065621017)
                ·
                  refine ⟨4747195745622036799215763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329594327496049065621017 4747195745622036799215763)
                  ·
                    refine ⟨7120793618433055198823645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4747195745622036799215763 7120793618433055198823645)
                    ·
                      refine ⟨2670297606912395699558867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120793618433055198823645 2670297606912395699558867)
                      ·
                        rfl

theorem cell23_5200386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5200386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200386 prefixEnd_5200386 := by exact prefixLift 5200386
  have htrace : WordTrace (prefixWord ++ tailWord_5200386) baseStart_5200386 baseEnd_5200386 := by
    simpa [prefixWord, tailWord_5200386, baseEnd_5200386] using wordTrace_append hprefix tailTrace_5200386
  have hstable : (prefixWord ++ tailWord_5200386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200386).length < 2 ^ (prefixWord ++ tailWord_5200386).sum := by decide
  have hdescent : baseEnd_5200386 < baseStart_5200386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200401 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_5200401 : Nat := 118140960795 + 5200401 * 2 ^ 59
def prefixEnd_5200401 : Nat := 4983230072969 + 3 ^ 40 * 5200401 * 2
def baseEnd_5200401 : Nat := 2670305309122213140871297

theorem tailTrace_5200401 : CollatzResearch.WordTrace tailWord_5200401 prefixEnd_5200401 2670305309122213140871297 := by
  unfold tailWord_5200401
  simp only [CollatzResearch.WordTrace]
  refine ⟨189674206832842809626057057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126449471221895206417371371 189674206832842809626057057)
  ·
    refine ⟨142255655124632107219542793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189674206832842809626057057 142255655124632107219542793)
    ·
      refine ⟨106691741343474080414657095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142255655124632107219542793 106691741343474080414657095)
      ·
        refine ⟨160037612015211120621985643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106691741343474080414657095 160037612015211120621985643)
        ·
          refine ⟨240056418022816680932978465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160037612015211120621985643 240056418022816680932978465)
          ·
            refine ⟨180042313517112510699733849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240056418022816680932978465 180042313517112510699733849)
            ·
              refine ⟨135031735137834383024800387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180042313517112510699733849 135031735137834383024800387)
              ·
                refine ⟨202547602706751574537200581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135031735137834383024800387 202547602706751574537200581)
                ·
                  refine ⟨37977675507515920225725109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202547602706751574537200581 37977675507515920225725109)
                  ·
                    refine ⟨3560407078829617521161729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37977675507515920225725109 3560407078829617521161729)
                    ·
                      refine ⟨2670305309122213140871297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560407078829617521161729 2670305309122213140871297)
                      ·
                        rfl

theorem cell23_5200401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_5200401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200401 prefixEnd_5200401 := by exact prefixLift 5200401
  have htrace : WordTrace (prefixWord ++ tailWord_5200401) baseStart_5200401 baseEnd_5200401 := by
    simpa [prefixWord, tailWord_5200401, baseEnd_5200401] using wordTrace_append hprefix tailTrace_5200401
  have hstable : (prefixWord ++ tailWord_5200401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200401).length < 2 ^ (prefixWord ++ tailWord_5200401).sum := by decide
  have hdescent : baseEnd_5200401 < baseStart_5200401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200431 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 6, 2]
def baseStart_5200431 : Nat := 118140960795 + 5200431 * 2 ^ 59
def prefixEnd_5200431 : Nat := 4983230072969 + 3 ^ 40 * 5200431 * 2
def baseEnd_5200431 : Nat := 2670320713541848023496159

theorem tailTrace_5200431 : CollatzResearch.WordTrace tailWord_5200431 prefixEnd_5200431 2670320713541848023496159 := by
  unfold tailWord_5200431
  simp only [CollatzResearch.WordTrace]
  refine ⟨189675301022734124749649147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126450200681822749833099431 189675301022734124749649147)
  ·
    refine ⟨284512951534101187124473721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189675301022734124749649147 284512951534101187124473721)
    ·
      refine ⟨213384713650575890343355291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284512951534101187124473721 213384713650575890343355291)
      ·
        refine ⟨320077070475863835515032937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213384713650575890343355291 320077070475863835515032937)
        ·
          refine ⟨240057802856897876636274703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320077070475863835515032937 240057802856897876636274703)
          ·
            refine ⟨360086704285346814954412055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240057802856897876636274703 360086704285346814954412055)
            ·
              refine ⟨540130056428020222431618083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360086704285346814954412055 540130056428020222431618083)
              ·
                refine ⟨810195084642030333647427125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540130056428020222431618083 810195084642030333647427125)
                ·
                  refine ⟨75955789185190343779446293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810195084642030333647427125 75955789185190343779446293)
                  ·
                    refine ⟨3560427618055797364661545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75955789185190343779446293 3560427618055797364661545)
                    ·
                      refine ⟨2670320713541848023496159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560427618055797364661545 2670320713541848023496159)
                      ·
                        rfl

theorem cell23_5200431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 6, 2].length) (baseStart_5200431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200431 prefixEnd_5200431 := by exact prefixLift 5200431
  have htrace : WordTrace (prefixWord ++ tailWord_5200431) baseStart_5200431 baseEnd_5200431 := by
    simpa [prefixWord, tailWord_5200431, baseEnd_5200431] using wordTrace_append hprefix tailTrace_5200431
  have hstable : (prefixWord ++ tailWord_5200431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200431).length < 2 ^ (prefixWord ++ tailWord_5200431).sum := by decide
  have hdescent : baseEnd_5200431 < baseStart_5200431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200438 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5200438 : Nat := 118140960795 + 5200438 * 2 ^ 59
def prefixEnd_5200438 : Nat := 4983230072969 + 3 ^ 40 * 5200438 * 2
def baseEnd_5200438 : Nat := 2670324307906429496108627

theorem tailTrace_5200438 : CollatzResearch.WordTrace tailWord_5200438 prefixEnd_5200438 2670324307906429496108627 := by
  unfold tailWord_5200438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11854722270856797809072123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126450370889139176630102645 11854722270856797809072123)
  ·
    refine ⟨17782083406285196713608185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11854722270856797809072123 17782083406285196713608185)
    ·
      refine ⟨13336562554713897535206139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17782083406285196713608185 13336562554713897535206139)
      ·
        refine ⟨20004843832070846302809209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13336562554713897535206139 20004843832070846302809209)
        ·
          refine ⟨15003632874053134727106907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20004843832070846302809209 15003632874053134727106907)
          ·
            refine ⟨22505449311079702090660361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15003632874053134727106907 22505449311079702090660361)
            ·
              refine ⟨16879086983309776567995271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22505449311079702090660361 16879086983309776567995271)
              ·
                refine ⟨25318630474964664851992907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16879086983309776567995271 25318630474964664851992907)
                ·
                  refine ⟨37977945712446997277989361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25318630474964664851992907 37977945712446997277989361)
                  ·
                    refine ⟨28483459284335247958492021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37977945712446997277989361 28483459284335247958492021)
                    ·
                      refine ⟨2670324307906429496108627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28483459284335247958492021 2670324307906429496108627)
                      ·
                        rfl

theorem cell23_5200438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5200438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200438 prefixEnd_5200438 := by exact prefixLift 5200438
  have htrace : WordTrace (prefixWord ++ tailWord_5200438) baseStart_5200438 baseEnd_5200438 := by
    simpa [prefixWord, tailWord_5200438, baseEnd_5200438] using wordTrace_append hprefix tailTrace_5200438
  have hstable : (prefixWord ++ tailWord_5200438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200438).length < 2 ^ (prefixWord ++ tailWord_5200438).sum := by decide
  have hdescent : baseEnd_5200438 < baseStart_5200438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200451 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3]
def baseStart_5200451 : Nat := 118140960795 + 5200451 * 2 ^ 59
def prefixEnd_5200451 : Nat := 4983230072969 + 3 ^ 40 * 5200451 * 2
def baseEnd_5200451 : Nat := 2670330983154937945246067

theorem tailTrace_5200451 : CollatzResearch.WordTrace tailWord_5200451 prefixEnd_5200451 2670330983154937945246067 := by
  unfold tailWord_5200451
  simp only [CollatzResearch.WordTrace]
  refine ⟨189676030482661668165377207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126450686988441112110251471 189676030482661668165377207)
  ·
    refine ⟨284514045723992502248065811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189676030482661668165377207 284514045723992502248065811)
    ·
      refine ⟨426771068585988753372098717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284514045723992502248065811 426771068585988753372098717)
      ·
        refine ⟨160039150719745782514537019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426771068585988753372098717 160039150719745782514537019)
        ·
          refine ⟨240058726079618673771805529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160039150719745782514537019 240058726079618673771805529)
          ·
            refine ⟨180044044559714005328854147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240058726079618673771805529 180044044559714005328854147)
            ·
              refine ⟨270066066839571007993281221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180044044559714005328854147 270066066839571007993281221)
              ·
                refine ⟨50637387532419563998740229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270066066839571007993281221 50637387532419563998740229)
                ·
                  refine ⟨9494510162328668249763793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50637387532419563998740229 9494510162328668249763793)
                  ·
                    refine ⟨7120882621746501187322845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9494510162328668249763793 7120882621746501187322845)
                    ·
                      refine ⟨2670330983154937945246067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120882621746501187322845 2670330983154937945246067)
                      ·
                        rfl

theorem cell23_5200451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_5200451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200451 prefixEnd_5200451 := by exact prefixLift 5200451
  have htrace : WordTrace (prefixWord ++ tailWord_5200451) baseStart_5200451 baseEnd_5200451 := by
    simpa [prefixWord, tailWord_5200451, baseEnd_5200451] using wordTrace_append hprefix tailTrace_5200451
  have hstable : (prefixWord ++ tailWord_5200451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200451).length < 2 ^ (prefixWord ++ tailWord_5200451).sum := by decide
  have hdescent : baseEnd_5200451 < baseStart_5200451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200458 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_5200458 : Nat := 118140960795 + 5200458 * 2 ^ 59
def prefixEnd_5200458 : Nat := 4983230072969 + 3 ^ 40 * 5200458 * 2
def baseEnd_5200458 : Nat := 890111525839839805952845

theorem tailTrace_5200458 : CollatzResearch.WordTrace tailWord_5200458 prefixEnd_5200458 890111525839839805952845 := by
  unfold tailWord_5200458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47419071448409077090220507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126450857195757538907254685 47419071448409077090220507)
  ·
    refine ⟨71128607172613615635330761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47419071448409077090220507 71128607172613615635330761)
    ·
      refine ⟨53346455379460211726498071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71128607172613615635330761 53346455379460211726498071)
      ·
        refine ⟨80019683069190317589747107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53346455379460211726498071 80019683069190317589747107)
        ·
          refine ⟨120029524603785476384620661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80019683069190317589747107 120029524603785476384620661)
          ·
            refine ⟨11252767931604888411058187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120029524603785476384620661 11252767931604888411058187)
            ·
              refine ⟨16879151897407332616587281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252767931604888411058187 16879151897407332616587281)
              ·
                refine ⟨12659363923055499462440461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16879151897407332616587281 12659363923055499462440461)
                ·
                  refine ⟨4747261471145812298415173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12659363923055499462440461 4747261471145812298415173)
                  ·
                    refine ⟨890111525839839805952845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747261471145812298415173 890111525839839805952845)
                    ·
                      rfl

theorem cell23_5200458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_5200458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200458 prefixEnd_5200458 := by exact prefixLift 5200458
  have htrace : WordTrace (prefixWord ++ tailWord_5200458) baseStart_5200458 baseEnd_5200458 := by
    simpa [prefixWord, tailWord_5200458, baseEnd_5200458] using wordTrace_append hprefix tailTrace_5200458
  have hstable : (prefixWord ++ tailWord_5200458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200458).length < 2 ^ (prefixWord ++ tailWord_5200458).sum := by decide
  have hdescent : baseEnd_5200458 < baseStart_5200458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200468 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_5200468 : Nat := 118140960795 + 5200468 * 2 ^ 59
def prefixEnd_5200468 : Nat := 4983230072969 + 3 ^ 40 * 5200468 * 2
def baseEnd_5200468 : Nat := 2670339712326064378733489

theorem tailTrace_5200468 : CollatzResearch.WordTrace tailWord_5200468 prefixEnd_5200468 2670339712326064378733489 := by
  unfold tailWord_5200468
  simp only [CollatzResearch.WordTrace]
  refine ⟨94838325261800040034373029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126451100349066720045830705 94838325261800040034373029)
  ·
    refine ⟨17782185986587507506444943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94838325261800040034373029 17782185986587507506444943)
    ·
      refine ⟨26673278979881261259667415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17782185986587507506444943 26673278979881261259667415)
      ·
        refine ⟨40009918469821891889501123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26673278979881261259667415 40009918469821891889501123)
        ·
          refine ⟨60014877704732837834251685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40009918469821891889501123 60014877704732837834251685)
          ·
            refine ⟨11252789569637407093922191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60014877704732837834251685 11252789569637407093922191)
            ·
              refine ⟨16879184354456110640883287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252789569637407093922191 16879184354456110640883287)
              ·
                refine ⟨25318776531684165961324931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16879184354456110640883287 25318776531684165961324931)
                ·
                  refine ⟨37978164797526248941987397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25318776531684165961324931 37978164797526248941987397)
                  ·
                    refine ⟨7120905899536171676622637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37978164797526248941987397 7120905899536171676622637)
                    ·
                      refine ⟨2670339712326064378733489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7120905899536171676622637 2670339712326064378733489)
                      ·
                        rfl

theorem cell23_5200468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_5200468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200468 prefixEnd_5200468 := by exact prefixLift 5200468
  have htrace : WordTrace (prefixWord ++ tailWord_5200468) baseStart_5200468 baseEnd_5200468 := by
    simpa [prefixWord, tailWord_5200468, baseEnd_5200468] using wordTrace_append hprefix tailTrace_5200468
  have hstable : (prefixWord ++ tailWord_5200468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200468).length < 2 ^ (prefixWord ++ tailWord_5200468).sum := by decide
  have hdescent : baseEnd_5200468 < baseStart_5200468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200488 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 8]
def baseStart_5200488 : Nat := 118140960795 + 5200488 * 2 ^ 59
def prefixEnd_5200488 : Nat := 4983230072969 + 3 ^ 40 * 5200488 * 2
def baseEnd_5200488 : Nat := 296705553548794922275933

theorem tailTrace_5200488 : CollatzResearch.WordTrace tailWord_5200488 prefixEnd_5200488 296705553548794922275933 := by
  unfold tailWord_5200488
  simp only [CollatzResearch.WordTrace]
  refine ⟨94838689991763811742237059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126451586655685082322982745 94838689991763811742237059)
  ·
    refine ⟨142258034987645717613355589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94838689991763811742237059 142258034987645717613355589)
    ·
      refine ⟨26673381560183572052504173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142258034987645717613355589 26673381560183572052504173)
      ·
        refine ⟨10002518085068839519689065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26673381560183572052504173 10002518085068839519689065)
        ·
          refine ⟨7501888563801629639766799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10002518085068839519689065 7501888563801629639766799)
          ·
            refine ⟨11252832845702444459650199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501888563801629639766799 11252832845702444459650199)
            ·
              refine ⟨16879249268553666689475299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252832845702444459650199 16879249268553666689475299)
              ·
                refine ⟨25318873902830500034212949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16879249268553666689475299 25318873902830500034212949)
                ·
                  refine ⟨296705553548794922275933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25318873902830500034212949 296705553548794922275933)
                  ·
                    rfl

theorem cell23_5200488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_5200488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200488 prefixEnd_5200488 := by exact prefixLift 5200488
  have htrace : WordTrace (prefixWord ++ tailWord_5200488) baseStart_5200488 baseEnd_5200488 := by
    simpa [prefixWord, tailWord_5200488, baseEnd_5200488] using wordTrace_append hprefix tailTrace_5200488
  have hstable : (prefixWord ++ tailWord_5200488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200488).length < 2 ^ (prefixWord ++ tailWord_5200488).sum := by decide
  have hdescent : baseEnd_5200488 < baseStart_5200488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200508 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_5200508 : Nat := 118140960795 + 5200508 * 2 ^ 59
def prefixEnd_5200508 : Nat := 4983230072969 + 3 ^ 40 * 5200508 * 2
def baseEnd_5200508 : Nat := 2670360251552244222233305

theorem tailTrace_5200508 : CollatzResearch.WordTrace tailWord_5200508 prefixEnd_5200508 2670360251552244222233305 := by
  unfold tailWord_5200508
  simp only [CollatzResearch.WordTrace]
  refine ⟨94839054721727583450101089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126452072962303444600134785 94839054721727583450101089)
  ·
    refine ⟨71129291041295687587575817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94839054721727583450101089 71129291041295687587575817)
    ·
      refine ⟨53346968280971765690681863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71129291041295687587575817 53346968280971765690681863)
      ·
        refine ⟨80020452421457648536022795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53346968280971765690681863 80020452421457648536022795)
        ·
          refine ⟨120030678632186472804034193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80020452421457648536022795 120030678632186472804034193)
          ·
            refine ⟨90023008974139854603025645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120030678632186472804034193 90023008974139854603025645)
            ·
              refine ⟨33758628365302445476134617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90023008974139854603025645 33758628365302445476134617)
              ·
                refine ⟨25318971273976834107100963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33758628365302445476134617 25318971273976834107100963)
                ·
                  refine ⟨37978456910965251160651445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25318971273976834107100963 37978456910965251160651445)
                  ·
                    refine ⟨3560480335402992296311073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37978456910965251160651445 3560480335402992296311073)
                    ·
                      refine ⟨2670360251552244222233305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560480335402992296311073 2670360251552244222233305)
                      ·
                        rfl

theorem cell23_5200508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_5200508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200508 prefixEnd_5200508 := by exact prefixLift 5200508
  have htrace : WordTrace (prefixWord ++ tailWord_5200508) baseStart_5200508 baseEnd_5200508 := by
    simpa [prefixWord, tailWord_5200508, baseEnd_5200508] using wordTrace_append hprefix tailTrace_5200508
  have hstable : (prefixWord ++ tailWord_5200508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200508).length < 2 ^ (prefixWord ++ tailWord_5200508).sum := by decide
  have hdescent : baseEnd_5200508 < baseStart_5200508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200542 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5200542 : Nat := 118140960795 + 5200542 * 2 ^ 59
def prefixEnd_5200542 : Nat := 4983230072969 + 3 ^ 40 * 5200542 * 2
def baseEnd_5200542 : Nat := 2670377709894497089208149

theorem tailTrace_5200542 : CollatzResearch.WordTrace tailWord_5200542 prefixEnd_5200542 2670377709894497089208149 := by
  unfold tailWord_5200542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23709918690666498838367485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126452899683554660471293253 23709918690666498838367485)
  ·
    refine ⟨8891219508999937064387807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23709918690666498838367485 8891219508999937064387807)
    ·
      refine ⟨13336829263499905596581711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8891219508999937064387807 13336829263499905596581711)
      ·
        refine ⟨20005243895249858394872567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13336829263499905596581711 20005243895249858394872567)
        ·
          refine ⟨30007865842874787592308851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20005243895249858394872567 30007865842874787592308851)
          ·
            refine ⟨45011798764312181388463277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30007865842874787592308851 45011798764312181388463277)
            ·
              refine ⟨16879424536617068020673729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45011798764312181388463277 16879424536617068020673729)
              ·
                refine ⟨12659568402462801015505297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16879424536617068020673729 12659568402462801015505297)
                ·
                  refine ⟨9494676301847100761628973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12659568402462801015505297 9494676301847100761628973)
                  ·
                    refine ⟨3560503613192662785610865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9494676301847100761628973 3560503613192662785610865)
                    ·
                      refine ⟨2670377709894497089208149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560503613192662785610865 2670377709894497089208149)
                      ·
                        rfl

theorem cell23_5200542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5200542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200542 prefixEnd_5200542 := by exact prefixLift 5200542
  have htrace : WordTrace (prefixWord ++ tailWord_5200542) baseStart_5200542 baseEnd_5200542 := by
    simpa [prefixWord, tailWord_5200542, baseEnd_5200542] using wordTrace_append hprefix tailTrace_5200542
  have hstable : (prefixWord ++ tailWord_5200542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200542).length < 2 ^ (prefixWord ++ tailWord_5200542).sum := by decide
  have hdescent : baseEnd_5200542 < baseStart_5200542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200548 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_5200548 : Nat := 118140960795 + 5200548 * 2 ^ 59
def prefixEnd_5200548 : Nat := 4983230072969 + 3 ^ 40 * 5200548 * 2
def baseEnd_5200548 : Nat := 890126930259474688577707

theorem tailTrace_5200548 : CollatzResearch.WordTrace tailWord_5200548 prefixEnd_5200548 890126930259474688577707 := by
  unfold tailWord_5200548
  simp only [CollatzResearch.WordTrace]
  refine ⟨94839784181655126865829149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126453045575540169154438865 94839784181655126865829149)
  ·
    refine ⟨35564919068120672574685931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94839784181655126865829149 35564919068120672574685931)
    ·
      refine ⟨53347378602181008862028897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35564919068120672574685931 53347378602181008862028897)
      ·
        refine ⟨40010533951635756646521673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53347378602181008862028897 40010533951635756646521673)
        ·
          refine ⟨30007900463726817484891255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40010533951635756646521673 30007900463726817484891255)
          ·
            refine ⟨45011850695590226227336883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30007900463726817484891255 45011850695590226227336883)
            ·
              refine ⟨67517776043385339341005325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45011850695590226227336883 67517776043385339341005325)
              ·
                refine ⟨25319166016269502252876997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67517776043385339341005325 25319166016269502252876997)
                ·
                  refine ⟨4747343628050531672414437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25319166016269502252876997 4747343628050531672414437)
                  ·
                    refine ⟨890126930259474688577707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747343628050531672414437 890126930259474688577707)
                    ·
                      rfl

theorem cell23_5200548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_5200548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200548 prefixEnd_5200548 := by exact prefixLift 5200548
  have htrace : WordTrace (prefixWord ++ tailWord_5200548) baseStart_5200548 baseEnd_5200548 := by
    simpa [prefixWord, tailWord_5200548, baseEnd_5200548] using wordTrace_append hprefix tailTrace_5200548
  have hstable : (prefixWord ++ tailWord_5200548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200548).length < 2 ^ (prefixWord ++ tailWord_5200548).sum := by decide
  have hdescent : baseEnd_5200548 < baseStart_5200548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200575 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_5200575 : Nat := 118140960795 + 5200575 * 2 ^ 59
def prefixEnd_5200575 : Nat := 4983230072969 + 3 ^ 40 * 5200575 * 2
def baseEnd_5200575 : Nat := 2670394654756095460095497

theorem tailTrace_5200575 : CollatzResearch.WordTrace tailWord_5200575 prefixEnd_5200575 2670394654756095460095497 := by
  unfold tailWord_5200575
  simp only [CollatzResearch.WordTrace]
  refine ⟨189680553134212437342891179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126453702089474958228594119 189680553134212437342891179)
  ·
    refine ⟨284520829701318656014336769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189680553134212437342891179 284520829701318656014336769)
    ·
      refine ⟨213390622275988992010752577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284520829701318656014336769 213390622275988992010752577)
      ·
        refine ⟨160042966706991744008064433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213390622275988992010752577 160042966706991744008064433)
        ·
          refine ⟨120032225030243808006048325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160042966706991744008064433 120032225030243808006048325)
          ·
            refine ⟨22506042193170714001134061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120032225030243808006048325 22506042193170714001134061)
            ·
              refine ⟨8439765822439017750425273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22506042193170714001134061 8439765822439017750425273)
              ·
                refine ⟨6329824366829263312818955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8439765822439017750425273 6329824366829263312818955)
                ·
                  refine ⟨9494736550243894969228433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329824366829263312818955 9494736550243894969228433)
                  ·
                    refine ⟨7121052412682921226921325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9494736550243894969228433 7121052412682921226921325)
                    ·
                      refine ⟨2670394654756095460095497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7121052412682921226921325 2670394654756095460095497)
                      ·
                        rfl

theorem cell23_5200575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_5200575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200575 prefixEnd_5200575 := by exact prefixLift 5200575
  have htrace : WordTrace (prefixWord ++ tailWord_5200575) baseStart_5200575 baseEnd_5200575 := by
    simpa [prefixWord, tailWord_5200575, baseEnd_5200575] using wordTrace_append hprefix tailTrace_5200575
  have hstable : (prefixWord ++ tailWord_5200575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200575).length < 2 ^ (prefixWord ++ tailWord_5200575).sum := by decide
  have hdescent : baseEnd_5200575 < baseStart_5200575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200622 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_5200622 : Nat := 118140960795 + 5200622 * 2 ^ 59
def prefixEnd_5200622 : Nat := 4983230072969 + 3 ^ 40 * 5200622 * 2
def baseEnd_5200622 : Nat := 2670418788346856776207781

theorem tailTrace_5200622 : CollatzResearch.WordTrace tailWord_5200622 prefixEnd_5200622 2670418788346856776207781 := by
  unfold tailWord_5200622
  simp only [CollatzResearch.WordTrace]
  refine ⟨23710283420630270546231515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126454844910028109579901413 23710283420630270546231515)
  ·
    refine ⟨35565425130945405819347273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23710283420630270546231515 35565425130945405819347273)
    ·
      refine ⟨26674068848209054364510455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35565425130945405819347273 26674068848209054364510455)
      ·
        refine ⟨40011103272313581546765683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26674068848209054364510455 40011103272313581546765683)
        ·
          refine ⟨60016654908470372320148525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40011103272313581546765683 60016654908470372320148525)
          ·
            refine ⟨22506245590676389620055697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60016654908470372320148525 22506245590676389620055697)
            ·
              refine ⟨16879684193007292215041773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22506245590676389620055697 16879684193007292215041773)
              ·
                refine ⟨6329881572377734580640665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16879684193007292215041773 6329881572377734580640665)
                ·
                  refine ⟨4747411179283300935480499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329881572377734580640665 4747411179283300935480499)
                  ·
                    refine ⟨7121116768924951403220749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4747411179283300935480499 7121116768924951403220749)
                    ·
                      refine ⟨2670418788346856776207781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7121116768924951403220749 2670418788346856776207781)
                      ·
                        rfl

theorem cell23_5200622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_5200622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200622 prefixEnd_5200622 := by exact prefixLift 5200622
  have htrace : WordTrace (prefixWord ++ tailWord_5200622) baseStart_5200622 baseEnd_5200622 := by
    simpa [prefixWord, tailWord_5200622, baseEnd_5200622] using wordTrace_append hprefix tailTrace_5200622
  have hstable : (prefixWord ++ tailWord_5200622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200622).length < 2 ^ (prefixWord ++ tailWord_5200622).sum := by decide
  have hdescent : baseEnd_5200622 < baseStart_5200622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200629 : List Nat := [1, 3, 6, 1, 1, 1, 3, 7]
def baseStart_5200629 : Nat := 118140960795 + 5200629 * 2 ^ 59
def prefixEnd_5200629 : Nat := 4983230072969 + 3 ^ 40 * 5200629 * 2
def baseEnd_5200629 : Nat := 98904532693016231437787

theorem tailTrace_5200629 : CollatzResearch.WordTrace tailWord_5200629 prefixEnd_5200629 98904532693016231437787 := by
  unfold tailWord_5200629
  simp only [CollatzResearch.WordTrace]
  refine ⟨189682522676016804565356941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126455015117344536376904627 189682522676016804565356941)
  ·
    refine ⟨71130946003506301712008853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189682522676016804565356941 71130946003506301712008853)
    ·
      refine ⟨3334263093914357892750415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71130946003506301712008853 3334263093914357892750415)
      ·
        refine ⟨5001394640871536839125623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3334263093914357892750415 5001394640871536839125623)
        ·
          refine ⟨7502091961307305258688435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001394640871536839125623 7502091961307305258688435)
          ·
            refine ⟨11253137941960957888032653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502091961307305258688435 11253137941960957888032653)
            ·
              refine ⟨4219926728235359208012245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11253137941960957888032653 4219926728235359208012245)
              ·
                refine ⟨98904532693016231437787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4219926728235359208012245 98904532693016231437787)
                ·
                  rfl

theorem cell23_5200629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 7].length) (baseStart_5200629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200629 prefixEnd_5200629 := by exact prefixLift 5200629
  have htrace : WordTrace (prefixWord ++ tailWord_5200629) baseStart_5200629 baseEnd_5200629 := by
    simpa [prefixWord, tailWord_5200629, baseEnd_5200629] using wordTrace_append hprefix tailTrace_5200629
  have hstable : (prefixWord ++ tailWord_5200629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200629).length < 2 ^ (prefixWord ++ tailWord_5200629).sum := by decide
  have hdescent : baseEnd_5200629 < baseStart_5200629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200651 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 11]
def baseStart_5200651 : Nat := 118140960795 + 5200651 * 2 ^ 59
def prefixEnd_5200651 : Nat := 4983230072969 + 3 ^ 40 * 5200651 * 2
def baseEnd_5200651 : Nat := 296714853253981906971683

theorem tailTrace_5200651 : CollatzResearch.WordTrace tailWord_5200651 prefixEnd_5200651 296714853253981906971683 := by
  unfold tailWord_5200651
  simp only [CollatzResearch.WordTrace]
  refine ⟨189683325081937102322657807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126455550054624734881771871 189683325081937102322657807)
  ·
    refine ⟨284524987622905653483986711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189683325081937102322657807 284524987622905653483986711)
    ·
      refine ⟨426787481434358480225980067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284524987622905653483986711 426787481434358480225980067)
      ·
        refine ⟨640181222151537720338970101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426787481434358480225980067 640181222151537720338970101)
        ·
          refine ⟨60016989576706661281778447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 640181222151537720338970101 60016989576706661281778447)
          ·
            refine ⟨90025484365059991922667671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60016989576706661281778447 90025484365059991922667671)
            ·
              refine ⟨135038226547589987884001507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90025484365059991922667671 135038226547589987884001507)
              ·
                refine ⟨202557339821384981826002261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135038226547589987884001507 202557339821384981826002261)
                ·
                  refine ⟨296714853253981906971683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 202557339821384981826002261 296714853253981906971683)
                  ·
                    rfl

theorem cell23_5200651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 11].length) (baseStart_5200651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200651 prefixEnd_5200651 := by exact prefixLift 5200651
  have htrace : WordTrace (prefixWord ++ tailWord_5200651) baseStart_5200651 baseEnd_5200651 := by
    simpa [prefixWord, tailWord_5200651, baseEnd_5200651] using wordTrace_append hprefix tailTrace_5200651
  have hstable : (prefixWord ++ tailWord_5200651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200651).length < 2 ^ (prefixWord ++ tailWord_5200651).sum := by decide
  have hdescent : baseEnd_5200651 < baseStart_5200651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200668 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 7]
def baseStart_5200668 : Nat := 118140960795 + 5200668 * 2 ^ 59
def prefixEnd_5200668 : Nat := 4983230072969 + 3 ^ 40 * 5200668 * 2
def baseEnd_5200668 : Nat := 296715823161884844025841

theorem tailTrace_5200668 : CollatzResearch.WordTrace tailWord_5200668 prefixEnd_5200668 296715823161884844025841 := by
  unfold tailWord_5200668
  simp only [CollatzResearch.WordTrace]
  refine ⟨94841972561437757113013329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126455963415250342817351105 94841972561437757113013329)
  ·
    refine ⟨71131479421078317834759997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94841972561437757113013329 71131479421078317834759997)
    ·
      refine ⟨26674304782904369188034999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71131479421078317834759997 26674304782904369188034999)
      ·
        refine ⟨40011457174356553782052499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26674304782904369188034999 40011457174356553782052499)
        ·
          refine ⟨60017185761534830673078749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40011457174356553782052499 60017185761534830673078749)
          ·
            refine ⟨22506444660575561502404531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60017185761534830673078749 22506444660575561502404531)
            ·
              refine ⟨33759666990863342253606797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22506444660575561502404531 33759666990863342253606797)
              ·
                refine ⟨12659875121573753345102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33759666990863342253606797 12659875121573753345102549)
                ·
                  refine ⟨296715823161884844025841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12659875121573753345102549 296715823161884844025841)
                  ·
                    rfl

theorem cell23_5200668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_5200668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200668 prefixEnd_5200668 := by exact prefixLift 5200668
  have htrace : WordTrace (prefixWord ++ tailWord_5200668) baseStart_5200668 baseEnd_5200668 := by
    simpa [prefixWord, tailWord_5200668, baseEnd_5200668] using wordTrace_append hprefix tailTrace_5200668
  have hstable : (prefixWord ++ tailWord_5200668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200668).length < 2 ^ (prefixWord ++ tailWord_5200668).sum := by decide
  have hdescent : baseEnd_5200668 < baseStart_5200668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200735 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 6, 2]
def baseStart_5200735 : Nat := 118140960795 + 5200735 * 2 ^ 59
def prefixEnd_5200735 : Nat := 4983230072969 + 3 ^ 40 * 5200735 * 2
def baseEnd_5200735 : Nat := 2670476811660814834094761

theorem tailTrace_5200735 : CollatzResearch.WordTrace tailWord_5200735 prefixEnd_5200735 2670476811660814834094761 := by
  unfold tailWord_5200735
  simp only [CollatzResearch.WordTrace]
  refine ⟨189686388813632784668715659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126457592542421856445810439 189686388813632784668715659)
  ·
    refine ⟨284529583220449177003073489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189686388813632784668715659 284529583220449177003073489)
    ·
      refine ⟨213397187415336882752305117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284529583220449177003073489 213397187415336882752305117)
      ·
        refine ⟨80023945280751331032114419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213397187415336882752305117 80023945280751331032114419)
        ·
          refine ⟨120035917921126996548171629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80023945280751331032114419 120035917921126996548171629)
          ·
            refine ⟨45013469220422623705564361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120035917921126996548171629 45013469220422623705564361)
            ·
              refine ⟨33760101915316967779173271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45013469220422623705564361 33760101915316967779173271)
              ·
                refine ⟨50640152872975451668759907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33760101915316967779173271 50640152872975451668759907)
                ·
                  refine ⟨75960229309463177503139861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50640152872975451668759907 75960229309463177503139861)
                  ·
                    refine ⟨3560635748881086445459681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75960229309463177503139861 3560635748881086445459681)
                    ·
                      refine ⟨2670476811660814834094761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560635748881086445459681 2670476811660814834094761)
                      ·
                        rfl

theorem cell23_5200735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_5200735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200735 prefixEnd_5200735 := by exact prefixLift 5200735
  have htrace : WordTrace (prefixWord ++ tailWord_5200735) baseStart_5200735 baseEnd_5200735 := by
    simpa [prefixWord, tailWord_5200735, baseEnd_5200735] using wordTrace_append hprefix tailTrace_5200735
  have hstable : (prefixWord ++ tailWord_5200735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200735).length < 2 ^ (prefixWord ++ tailWord_5200735).sum := by decide
  have hdescent : baseEnd_5200735 < baseStart_5200735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200755 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3]
def baseStart_5200755 : Nat := 118140960795 + 5200755 * 2 ^ 59
def prefixEnd_5200755 : Nat := 4983230072969 + 3 ^ 40 * 5200755 * 2
def baseEnd_5200755 : Nat := 2670487081273904755844669

theorem tailTrace_5200755 : CollatzResearch.WordTrace tailWord_5200755 prefixEnd_5200755 2670487081273904755844669 := by
  unfold tailWord_5200755
  simp only [CollatzResearch.WordTrace]
  refine ⟨189687118273560328084443719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126458078849040218722962479 189687118273560328084443719)
  ·
    refine ⟨284530677410340492126665579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189687118273560328084443719 284530677410340492126665579)
    ·
      refine ⟨426796016115510738189998369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284530677410340492126665579 426796016115510738189998369)
      ·
        refine ⟨320097012086633053642498777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426796016115510738189998369 320097012086633053642498777)
        ·
          refine ⟨240072759064974790231874083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320097012086633053642498777 240072759064974790231874083)
          ·
            refine ⟨360109138597462185347811125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240072759064974790231874083 360109138597462185347811125)
            ·
              refine ⟨33760231743512079876357293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360109138597462185347811125 33760231743512079876357293)
              ·
                refine ⟨12660086903817029953633985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33760231743512079876357293 12660086903817029953633985)
                ·
                  refine ⟨9495065177862772465225489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12660086903817029953633985 9495065177862772465225489)
                  ·
                    refine ⟨7121298883397079348919117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9495065177862772465225489 7121298883397079348919117)
                    ·
                      refine ⟨2670487081273904755844669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7121298883397079348919117 2670487081273904755844669)
                      ·
                        rfl

theorem cell23_5200755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_5200755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200755 prefixEnd_5200755 := by exact prefixLift 5200755
  have htrace : WordTrace (prefixWord ++ tailWord_5200755) baseStart_5200755 baseEnd_5200755 := by
    simpa [prefixWord, tailWord_5200755, baseEnd_5200755] using wordTrace_append hprefix tailTrace_5200755
  have hstable : (prefixWord ++ tailWord_5200755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200755).length < 2 ^ (prefixWord ++ tailWord_5200755).sum := by decide
  have hdescent : baseEnd_5200755 < baseStart_5200755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200762 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_5200762 : Nat := 118140960795 + 5200762 * 2 ^ 59
def prefixEnd_5200762 : Nat := 4983230072969 + 3 ^ 40 * 5200762 * 2
def baseEnd_5200762 : Nat := 890163558546162076152379

theorem tailTrace_5200762 : CollatzResearch.WordTrace tailWord_5200762 prefixEnd_5200762 890163558546162076152379 := by
  unfold tailWord_5200762
  simp only [CollatzResearch.WordTrace]
  refine ⟨47421843396133742069987135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126458249056356645519965693 47421843396133742069987135)
  ·
    refine ⟨71132765094200613104980703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47421843396133742069987135 71132765094200613104980703)
    ·
      refine ⟨106699147641300919657471055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71132765094200613104980703 106699147641300919657471055)
      ·
        refine ⟨160048721461951379486206583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106699147641300919657471055 160048721461951379486206583)
        ·
          refine ⟨240073082192927069229309875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160048721461951379486206583 240073082192927069229309875)
          ·
            refine ⟨360109623289390603843964813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240073082192927069229309875 360109623289390603843964813)
            ·
              refine ⟨135041108733521476441486805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360109623289390603843964813 135041108733521476441486805)
              ·
                refine ⟨3165025985941909604097347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135041108733521476441486805 3165025985941909604097347)
                ·
                  refine ⟨4747538978912864406146021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165025985941909604097347 4747538978912864406146021)
                  ·
                    refine ⟨890163558546162076152379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747538978912864406146021 890163558546162076152379)
                    ·
                      rfl

theorem cell23_5200762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_5200762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200762 prefixEnd_5200762 := by exact prefixLift 5200762
  have htrace : WordTrace (prefixWord ++ tailWord_5200762) baseStart_5200762 baseEnd_5200762 := by
    simpa [prefixWord, tailWord_5200762, baseEnd_5200762] using wordTrace_append hprefix tailTrace_5200762
  have hstable : (prefixWord ++ tailWord_5200762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200762).length < 2 ^ (prefixWord ++ tailWord_5200762).sum := by decide
  have hdescent : baseEnd_5200762 < baseStart_5200762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200770 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5200770 : Nat := 118140960795 + 5200770 * 2 ^ 59
def prefixEnd_5200770 : Nat := 4983230072969 + 3 ^ 40 * 5200770 * 2
def baseEnd_5200770 : Nat := 296721642609302466350789

theorem tailTrace_5200770 : CollatzResearch.WordTrace tailWord_5200770 prefixEnd_5200770 296721642609302466350789 := by
  unfold tailWord_5200770
  simp only [CollatzResearch.WordTrace]
  refine ⟨47421916342126496411559941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126458443579003990430826509 47421916342126496411559941)
  ·
    refine ⟨8891609314148718077167489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47421916342126496411559941 8891609314148718077167489)
    ·
      refine ⟨6668706985611538557875617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8891609314148718077167489 6668706985611538557875617)
      ·
        refine ⟨5001530239208653918406713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6668706985611538557875617 5001530239208653918406713)
        ·
          refine ⟨3751147679406490438805035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001530239208653918406713 3751147679406490438805035)
          ·
            refine ⟨5626721519109735658207553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751147679406490438805035 5626721519109735658207553)
            ·
              refine ⟨4220041139332301743655665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626721519109735658207553 4220041139332301743655665)
              ·
                refine ⟨3165030854499226307741749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220041139332301743655665 3165030854499226307741749)
                ·
                  refine ⟨296721642609302466350789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165030854499226307741749 296721642609302466350789)
                  ·
                    rfl

theorem cell23_5200770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5200770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200770 prefixEnd_5200770 := by exact prefixLift 5200770
  have htrace : WordTrace (prefixWord ++ tailWord_5200770) baseStart_5200770 baseEnd_5200770 := by
    simpa [prefixWord, tailWord_5200770, baseEnd_5200770] using wordTrace_append hprefix tailTrace_5200770
  have hstable : (prefixWord ++ tailWord_5200770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200770).length < 2 ^ (prefixWord ++ tailWord_5200770).sum := by decide
  have hdescent : baseEnd_5200770 < baseStart_5200770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200775 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 6]
def baseStart_5200775 : Nat := 118140960795 + 5200775 * 2 ^ 59
def prefixEnd_5200775 : Nat := 4983230072969 + 3 ^ 40 * 5200775 * 2
def baseEnd_5200775 : Nat := 296721927876332741954953

theorem tailTrace_5200775 : CollatzResearch.WordTrace tailWord_5200775 prefixEnd_5200775 296721927876332741954953 := by
  unfold tailWord_5200775
  simp only [CollatzResearch.WordTrace]
  refine ⟨189687847733487871500171779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126458565155658581000114519 189687847733487871500171779)
  ·
    refine ⟨284531771600231807250257669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189687847733487871500171779 284531771600231807250257669)
    ·
      refine ⟨53349707175043463859423313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284531771600231807250257669 53349707175043463859423313)
      ·
        refine ⟨40012280381282597894567485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53349707175043463859423313 40012280381282597894567485)
        ·
          refine ⟨15004605142980974210462807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40012280381282597894567485 15004605142980974210462807)
          ·
            refine ⟨22506907714471461315694211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15004605142980974210462807 22506907714471461315694211)
            ·
              refine ⟨33760361571707191973541317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22506907714471461315694211 33760361571707191973541317)
              ·
                refine ⟨6330067794695098495038997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33760361571707191973541317 6330067794695098495038997)
                ·
                  refine ⟨296721927876332741954953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6330067794695098495038997 296721927876332741954953)
                  ·
                    rfl

theorem cell23_5200775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 6].length) (baseStart_5200775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200775 prefixEnd_5200775 := by exact prefixLift 5200775
  have htrace : WordTrace (prefixWord ++ tailWord_5200775) baseStart_5200775 baseEnd_5200775 := by
    simpa [prefixWord, tailWord_5200775, baseEnd_5200775] using wordTrace_append hprefix tailTrace_5200775
  have hstable : (prefixWord ++ tailWord_5200775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200775).length < 2 ^ (prefixWord ++ tailWord_5200775).sum := by decide
  have hdescent : baseEnd_5200775 < baseStart_5200775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200779 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 1, 4]
def baseStart_5200779 : Nat := 118140960795 + 5200779 * 2 ^ 59
def prefixEnd_5200779 : Nat := 4983230072969 + 3 ^ 40 * 5200779 * 2
def baseEnd_5200779 : Nat := 890166468269870887314853

theorem tailTrace_5200779 : CollatzResearch.WordTrace tailWord_5200779 prefixEnd_5200779 890166468269870887314853 := by
  unfold tailWord_5200779
  simp only [CollatzResearch.WordTrace]
  refine ⟨189687993625473380183317391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126458662416982253455544927 189687993625473380183317391)
  ·
    refine ⟨284531990438210070274976087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189687993625473380183317391 284531990438210070274976087)
    ·
      refine ⟨426797985657315105412464131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284531990438210070274976087 426797985657315105412464131)
      ·
        refine ⟨640196978485972658118696197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426797985657315105412464131 640196978485972658118696197)
        ·
          refine ⟨120036933466119873397255537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 640196978485972658118696197 120036933466119873397255537)
          ·
            refine ⟨90027700099589905047941653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120036933466119873397255537 90027700099589905047941653)
            ·
              refine ⟨4220048442168276799122265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90027700099589905047941653 4220048442168276799122265)
              ·
                refine ⟨3165036331626207599341699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220048442168276799122265 3165036331626207599341699)
                ·
                  refine ⟨4747554497439311399012549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165036331626207599341699 4747554497439311399012549)
                  ·
                    refine ⟨890166468269870887314853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747554497439311399012549 890166468269870887314853)
                    ·
                      rfl

theorem cell23_5200779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 4].length) (baseStart_5200779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200779 prefixEnd_5200779 := by exact prefixLift 5200779
  have htrace : WordTrace (prefixWord ++ tailWord_5200779) baseStart_5200779 baseEnd_5200779 := by
    simpa [prefixWord, tailWord_5200779, baseEnd_5200779] using wordTrace_append hprefix tailTrace_5200779
  have hstable : (prefixWord ++ tailWord_5200779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200779).length < 2 ^ (prefixWord ++ tailWord_5200779).sum := by decide
  have hdescent : baseEnd_5200779 < baseStart_5200779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200813 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5200813 : Nat := 118140960795 + 5200813 * 2 ^ 59
def prefixEnd_5200813 : Nat := 4983230072969 + 3 ^ 40 * 5200813 * 2
def baseEnd_5200813 : Nat := 890172287717288509639801

theorem tailTrace_5200813 : CollatzResearch.WordTrace tailWord_5200813 prefixEnd_5200813 890172287717288509639801 := by
  unfold tailWord_5200813
  simp only [CollatzResearch.WordTrace]
  refine ⟨189689233707350203990055093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126459489138233469326703395 189689233707350203990055093)
  ·
    refine ⟨17783365660064081624067665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189689233707350203990055093 17783365660064081624067665)
    ·
      refine ⟨13337524245048061218050749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17783365660064081624067665 13337524245048061218050749)
      ·
        refine ⟨5001571591893022956769031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13337524245048061218050749 5001571591893022956769031)
        ·
          refine ⟨7502357387839534435153547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001571591893022956769031 7502357387839534435153547)
          ·
            refine ⟨11253536081759301652730321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502357387839534435153547 11253536081759301652730321)
            ·
              refine ⟨8440152061319476239547741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11253536081759301652730321 8440152061319476239547741)
              ·
                refine ⟨3165057022994803589830403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8440152061319476239547741 3165057022994803589830403)
                ·
                  refine ⟨4747585534492205384745605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165057022994803589830403 4747585534492205384745605)
                  ·
                    refine ⟨890172287717288509639801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747585534492205384745605 890172287717288509639801)
                    ·
                      rfl

theorem cell23_5200813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5200813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200813 prefixEnd_5200813 := by exact prefixLift 5200813
  have htrace : WordTrace (prefixWord ++ tailWord_5200813) baseStart_5200813 baseEnd_5200813 := by
    simpa [prefixWord, tailWord_5200813, baseEnd_5200813] using wordTrace_append hprefix tailTrace_5200813
  have hstable : (prefixWord ++ tailWord_5200813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200813).length < 2 ^ (prefixWord ++ tailWord_5200813).sum := by decide
  have hdescent : baseEnd_5200813 < baseStart_5200813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200835 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 4, 4]
def baseStart_5200835 : Nat := 118140960795 + 5200835 * 2 ^ 59
def prefixEnd_5200835 : Nat := 4983230072969 + 3 ^ 40 * 5200835 * 2
def baseEnd_5200835 : Nat := 890176053242088147614767

theorem tailTrace_5200835 : CollatzResearch.WordTrace tailWord_5200835 prefixEnd_5200835 890176053242088147614767 := by
  unfold tailWord_5200835
  simp only [CollatzResearch.WordTrace]
  refine ⟨189690036113270501747355959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126460024075513667831570639 189690036113270501747355959)
  ·
    refine ⟨284535054169905752621033939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189690036113270501747355959 284535054169905752621033939)
    ·
      refine ⟨426802581254858628931550909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284535054169905752621033939 426802581254858628931550909)
      ·
        refine ⟨160050967970571985849331591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426802581254858628931550909 160050967970571985849331591)
        ·
          refine ⟨240076451955857978773997387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160050967970571985849331591 240076451955857978773997387)
          ·
            refine ⟨360114677933786968160996081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240076451955857978773997387 360114677933786968160996081)
            ·
              refine ⟨270086008450340226120747061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360114677933786968160996081 270086008450340226120747061)
              ·
                refine ⟨25320563292219396198820037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270086008450340226120747061 25320563292219396198820037)
                ·
                  refine ⟨4747605617291136787278757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25320563292219396198820037 4747605617291136787278757)
                  ·
                    refine ⟨890176053242088147614767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747605617291136787278757 890176053242088147614767)
                    ·
                      rfl

theorem cell23_5200835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 4].length) (baseStart_5200835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200835 prefixEnd_5200835 := by exact prefixLift 5200835
  have htrace : WordTrace (prefixWord ++ tailWord_5200835) baseStart_5200835 baseEnd_5200835 := by
    simpa [prefixWord, tailWord_5200835, baseEnd_5200835] using wordTrace_append hprefix tailTrace_5200835
  have hstable : (prefixWord ++ tailWord_5200835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200835).length < 2 ^ (prefixWord ++ tailWord_5200835).sum := by decide
  have hdescent : baseEnd_5200835 < baseStart_5200835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200848 : List Nat := [2, 1, 1, 1, 1, 2, 3, 12]
def baseStart_5200848 : Nat := 118140960795 + 5200848 * 2 ^ 59
def prefixEnd_5200848 : Nat := 4983230072969 + 3 ^ 40 * 5200848 * 2
def baseEnd_5200848 : Nat := 98908697591658255258583

theorem tailTrace_5200848 : CollatzResearch.WordTrace tailWord_5200848 prefixEnd_5200848 98908697591658255258583 := by
  unfold tailWord_5200848
  simp only [CollatzResearch.WordTrace]
  refine ⟨94845255131111702483789599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126460340174815603311719465 94845255131111702483789599)
  ·
    refine ⟨142267882696667553725684399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94845255131111702483789599 142267882696667553725684399)
    ·
      refine ⟨213401824045001330588526599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142267882696667553725684399 213401824045001330588526599)
      ·
        refine ⟨320102736067501995882789899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213401824045001330588526599 320102736067501995882789899)
        ·
          refine ⟨480154104101252993824184849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320102736067501995882789899 480154104101252993824184849)
          ·
            refine ⟨360115578075939745368138637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480154104101252993824184849 360115578075939745368138637)
            ·
              refine ⟨135043341778477404513051989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360115578075939745368138637 135043341778477404513051989)
              ·
                refine ⟨98908697591658255258583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 135043341778477404513051989 98908697591658255258583)
                ·
                  rfl

theorem cell23_5200848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 12].length) (baseStart_5200848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200848 prefixEnd_5200848 := by exact prefixLift 5200848
  have htrace : WordTrace (prefixWord ++ tailWord_5200848) baseStart_5200848 baseEnd_5200848 := by
    simpa [prefixWord, tailWord_5200848, baseEnd_5200848] using wordTrace_append hprefix tailTrace_5200848
  have hstable : (prefixWord ++ tailWord_5200848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200848).length < 2 ^ (prefixWord ++ tailWord_5200848).sum := by decide
  have hdescent : baseEnd_5200848 < baseStart_5200848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200852 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_5200852 : Nat := 118140960795 + 5200852 * 2 ^ 59
def prefixEnd_5200852 : Nat := 4983230072969 + 3 ^ 40 * 5200852 * 2
def baseEnd_5200852 : Nat := 890178962965796958777241

theorem tailTrace_5200852 : CollatzResearch.WordTrace tailWord_5200852 prefixEnd_5200852 890178962965796958777241 := by
  unfold tailWord_5200852
  simp only [CollatzResearch.WordTrace]
  refine ⟨94845328077104456825362405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126460437436139275767149873 94845328077104456825362405)
  ·
    refine ⟨17783499014457085654755451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94845328077104456825362405 17783499014457085654755451)
    ·
      refine ⟨26675248521685628482133177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17783499014457085654755451 26675248521685628482133177)
      ·
        refine ⟨20006436391264221361599883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26675248521685628482133177 20006436391264221361599883)
        ·
          refine ⟨30009654586896332042399825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20006436391264221361599883 30009654586896332042399825)
          ·
            refine ⟨22507240940172249031799869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30009654586896332042399825 22507240940172249031799869)
            ·
              refine ⟨8440215352564593386924951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22507240940172249031799869 8440215352564593386924951)
              ·
                refine ⟨12660323028846890080387427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440215352564593386924951 12660323028846890080387427)
                ·
                  refine ⟨18990484543270335120581141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12660323028846890080387427 18990484543270335120581141)
                  ·
                    refine ⟨890178962965796958777241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18990484543270335120581141 890178962965796958777241)
                    ·
                      rfl

theorem cell23_5200852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_5200852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200852 prefixEnd_5200852 := by exact prefixLift 5200852
  have htrace : WordTrace (prefixWord ++ tailWord_5200852) baseStart_5200852 baseEnd_5200852 := by
    simpa [prefixWord, tailWord_5200852, baseEnd_5200852] using wordTrace_append hprefix tailTrace_5200852
  have hstable : (prefixWord ++ tailWord_5200852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200852).length < 2 ^ (prefixWord ++ tailWord_5200852).sum := by decide
  have hdescent : baseEnd_5200852 < baseStart_5200852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200855 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_5200855 : Nat := 118140960795 + 5200855 * 2 ^ 59
def prefixEnd_5200855 : Nat := 4983230072969 + 3 ^ 40 * 5200855 * 2
def baseEnd_5200855 : Nat := 2670538429339354364594209

theorem tailTrace_5200855 : CollatzResearch.WordTrace tailWord_5200855 prefixEnd_5200855 2670538429339354364594209 := by
  unfold tailWord_5200855
  simp only [CollatzResearch.WordTrace]
  refine ⟨189690765573198045163084019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126460510382132030108722679 189690765573198045163084019)
  ·
    refine ⟨284536148359797067744626029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189690765573198045163084019 284536148359797067744626029)
    ·
      refine ⟨106701055634923900404234761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284536148359797067744626029 106701055634923900404234761)
      ·
        refine ⟨80025791726192925303176071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106701055634923900404234761 80025791726192925303176071)
        ·
          refine ⟨120038687589289387954764107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80025791726192925303176071 120038687589289387954764107)
          ·
            refine ⟨180058031383934081932146161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120038687589289387954764107 180058031383934081932146161)
            ·
              refine ⟨135043523537950561449109621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180058031383934081932146161 135043523537950561449109621)
              ·
                refine ⟨12660330331682865135854027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135043523537950561449109621 12660330331682865135854027)
                ·
                  refine ⟨18990495497524297703781041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12660330331682865135854027 18990495497524297703781041)
                  ·
                    refine ⟨14242871623143223277835781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18990495497524297703781041 14242871623143223277835781)
                    ·
                      refine ⟨2670538429339354364594209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14242871623143223277835781 2670538429339354364594209)
                      ·
                        rfl

theorem cell23_5200855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_5200855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200855 prefixEnd_5200855 := by exact prefixLift 5200855
  have htrace : WordTrace (prefixWord ++ tailWord_5200855) baseStart_5200855 baseEnd_5200855 := by
    simpa [prefixWord, tailWord_5200855, baseEnd_5200855] using wordTrace_append hprefix tailTrace_5200855
  have hstable : (prefixWord ++ tailWord_5200855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200855).length < 2 ^ (prefixWord ++ tailWord_5200855).sum := by decide
  have hdescent : baseEnd_5200855 < baseStart_5200855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200942 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5200942 : Nat := 118140960795 + 5200942 * 2 ^ 59
def prefixEnd_5200942 : Nat := 4983230072969 + 3 ^ 40 * 5200942 * 2
def baseEnd_5200942 : Nat := 890194367385431841402103

theorem tailTrace_5200942 : CollatzResearch.WordTrace tailWord_5200942 prefixEnd_5200942 890194367385431841402103 := by
  unfold tailWord_5200942
  simp only [CollatzResearch.WordTrace]
  refine ⟨23711742340485357377687635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126462625815921906014334053 23711742340485357377687635)
  ·
    refine ⟨35567613510728036066531453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23711742340485357377687635 35567613510728036066531453)
    ·
      refine ⟨13337855066523013524949295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35567613510728036066531453 13337855066523013524949295)
      ·
        refine ⟨20006782599784520287423943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13337855066523013524949295 20006782599784520287423943)
        ·
          refine ⟨30010173899676780431135915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20006782599784520287423943 30010173899676780431135915)
          ·
            refine ⟨45015260849515170646703873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30010173899676780431135915 45015260849515170646703873)
            ·
              refine ⟨33761445637136377985027905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45015260849515170646703873 33761445637136377985027905)
              ·
                refine ⟨25321084227852283488770929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33761445637136377985027905 25321084227852283488770929)
                ·
                  refine ⟨18990813170889212616578197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25321084227852283488770929 18990813170889212616578197)
                  ·
                    refine ⟨890194367385431841402103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18990813170889212616578197 890194367385431841402103)
                    ·
                      rfl

theorem cell23_5200942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5200942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200942 prefixEnd_5200942 := by exact prefixLift 5200942
  have htrace : WordTrace (prefixWord ++ tailWord_5200942) baseStart_5200942 baseEnd_5200942 := by
    simpa [prefixWord, tailWord_5200942, baseEnd_5200942] using wordTrace_append hprefix tailTrace_5200942
  have hstable : (prefixWord ++ tailWord_5200942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200942).length < 2 ^ (prefixWord ++ tailWord_5200942).sum := by decide
  have hdescent : baseEnd_5200942 < baseStart_5200942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5200952 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_5200952 : Nat := 118140960795 + 5200952 * 2 ^ 59
def prefixEnd_5200952 : Nat := 4983230072969 + 3 ^ 40 * 5200952 * 2
def baseEnd_5200952 : Nat := 2670588236962840485081263

theorem tailTrace_5200952 : CollatzResearch.WordTrace tailWord_5200952 prefixEnd_5200952 2670588236962840485081263 := by
  unfold tailWord_5200952
  simp only [CollatzResearch.WordTrace]
  refine ⟨94847151726923315364682555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126462868969231087152910073 94847151726923315364682555)
  ·
    refine ⟨142270727590384973047023833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94847151726923315364682555 142270727590384973047023833)
    ·
      refine ⟨106703045692788729785267875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142270727590384973047023833 106703045692788729785267875)
      ·
        refine ⟨160054568539183094677901813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106703045692788729785267875 160054568539183094677901813)
        ·
          refine ⟨15005115800548415126053295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160054568539183094677901813 15005115800548415126053295)
          ·
            refine ⟨22507673700822622689079943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15005115800548415126053295 22507673700822622689079943)
            ·
              refine ⟨33761510551233934033619915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22507673700822622689079943 33761510551233934033619915)
              ·
                refine ⟨50642265826850901050429873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33761510551233934033619915 50642265826850901050429873)
                ·
                  refine ⟨37981699370138175787822405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50642265826850901050429873 37981699370138175787822405)
                  ·
                    refine ⟨7121568631900907960216701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37981699370138175787822405 7121568631900907960216701)
                    ·
                      refine ⟨2670588236962840485081263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7121568631900907960216701 2670588236962840485081263)
                      ·
                        rfl

theorem cell23_5200952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_5200952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5200952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5200952 prefixEnd_5200952 := by exact prefixLift 5200952
  have htrace : WordTrace (prefixWord ++ tailWord_5200952) baseStart_5200952 baseEnd_5200952 := by
    simpa [prefixWord, tailWord_5200952, baseEnd_5200952] using wordTrace_append hprefix tailTrace_5200952
  have hstable : (prefixWord ++ tailWord_5200952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5200952).length < 2 ^ (prefixWord ++ tailWord_5200952).sum := by decide
  have hdescent : baseEnd_5200952 < baseStart_5200952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5200952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201090 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5201090 : Nat := 118140960795 + 5201090 * 2 ^ 59
def prefixEnd_5201090 : Nat := 4983230072969 + 3 ^ 40 * 5201090 * 2
def baseEnd_5201090 : Nat := 2670659097293160945155629

theorem tailTrace_5201090 : CollatzResearch.WordTrace tailWord_5201090 prefixEnd_5201090 2670659097293160945155629 := by
  unfold tailWord_5201090
  simp only [CollatzResearch.WordTrace]
  refine ⟨47424834181836670074472181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126466224484897786865259149 47424834181836670074472181)
  ·
    refine ⟨4446078204547187819481767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47424834181836670074472181 4446078204547187819481767)
    ·
      refine ⟨6669117306820781729222651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446078204547187819481767 6669117306820781729222651)
      ·
        refine ⟨10003675960231172593833977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6669117306820781729222651 10003675960231172593833977)
        ·
          refine ⟨7502756970173379445375483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10003675960231172593833977 7502756970173379445375483)
          ·
            refine ⟨11254135455260069168063225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502756970173379445375483 11254135455260069168063225)
            ·
              refine ⟨8440601591445051876047419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11254135455260069168063225 8440601591445051876047419)
              ·
                refine ⟨12660902387167577814071129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440601591445051876047419 12660902387167577814071129)
                ·
                  refine ⟨9495676790375683360553347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12660902387167577814071129 9495676790375683360553347)
                  ·
                    refine ⟨14243515185563525040830021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9495676790375683360553347 14243515185563525040830021)
                    ·
                      refine ⟨2670659097293160945155629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14243515185563525040830021 2670659097293160945155629)
                      ·
                        rfl

theorem cell23_5201090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5201090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201090 prefixEnd_5201090 := by exact prefixLift 5201090
  have htrace : WordTrace (prefixWord ++ tailWord_5201090) baseStart_5201090 baseEnd_5201090 := by
    simpa [prefixWord, tailWord_5201090, baseEnd_5201090] using wordTrace_append hprefix tailTrace_5201090
  have hstable : (prefixWord ++ tailWord_5201090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201090).length < 2 ^ (prefixWord ++ tailWord_5201090).sum := by decide
  have hdescent : baseEnd_5201090 < baseStart_5201090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201117 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_5201117 : Nat := 118140960795 + 5201117 * 2 ^ 59
def prefixEnd_5201117 : Nat := 4983230072969 + 3 ^ 40 * 5201117 * 2
def baseEnd_5201117 : Nat := 890224320423610779839335

theorem tailTrace_5201117 : CollatzResearch.WordTrace tailWord_5201117 prefixEnd_5201117 890224320423610779839335 := by
  unfold tailWord_5201117
  simp only [CollatzResearch.WordTrace]
  refine ⟨189700321498248863909121605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126466880998832575939414403 189700321498248863909121605)
  ·
    refine ⟨35568810280921661982960301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189700321498248863909121605 35568810280921661982960301)
    ·
      refine ⟨13338303855345623243610113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35568810280921661982960301 13338303855345623243610113)
      ·
        refine ⟨10003727891509217432707585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13338303855345623243610113 10003727891509217432707585)
        ·
          refine ⟨7502795918631913074530689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10003727891509217432707585 7502795918631913074530689)
          ·
            refine ⟨5627096938973934805898017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7502795918631913074530689 5627096938973934805898017)
            ·
              refine ⟨4220322704230451104423513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627096938973934805898017 4220322704230451104423513)
              ·
                refine ⟨3165242028172838328317635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220322704230451104423513 3165242028172838328317635)
                ·
                  refine ⟨4747863042259257492476453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165242028172838328317635 4747863042259257492476453)
                  ·
                    refine ⟨890224320423610779839335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4747863042259257492476453 890224320423610779839335)
                    ·
                      rfl

theorem cell23_5201117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_5201117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201117 prefixEnd_5201117 := by exact prefixLift 5201117
  have htrace : WordTrace (prefixWord ++ tailWord_5201117) baseStart_5201117 baseEnd_5201117 := by
    simpa [prefixWord, tailWord_5201117, baseEnd_5201117] using wordTrace_append hprefix tailTrace_5201117
  have hstable : (prefixWord ++ tailWord_5201117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201117).length < 2 ^ (prefixWord ++ tailWord_5201117).sum := by decide
  have hdescent : baseEnd_5201117 < baseStart_5201117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201139 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 1, 6]
def baseStart_5201139 : Nat := 118140960795 + 5201139 * 2 ^ 59
def prefixEnd_5201139 : Nat := 4983230072969 + 3 ^ 40 * 5201139 * 2
def baseEnd_5201139 : Nat := 890228085948410417814301

theorem tailTrace_5201139 : CollatzResearch.WordTrace tailWord_5201139 prefixEnd_5201139 890228085948410417814301 := by
  unfold tailWord_5201139
  simp only [CollatzResearch.WordTrace]
  refine ⟨189701123904169161666422471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126467415936112774444281647 189701123904169161666422471)
  ·
    refine ⟨284551685856253742499633707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189701123904169161666422471 284551685856253742499633707)
    ·
      refine ⟨426827528784380613749450561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284551685856253742499633707 426827528784380613749450561)
      ·
        refine ⟨320120646588285460312087921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426827528784380613749450561 320120646588285460312087921)
        ·
          refine ⟨240090484941214095234065941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320120646588285460312087921 240090484941214095234065941)
          ·
            refine ⟨11254241481619410714096841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 240090484941214095234065941 11254241481619410714096841)
            ·
              refine ⟨8440681111214558035572631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11254241481619410714096841 8440681111214558035572631)
              ·
                refine ⟨12661021666821837053358947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440681111214558035572631 12661021666821837053358947)
                ·
                  refine ⟨18991532500232755580038421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661021666821837053358947 18991532500232755580038421)
                  ·
                    refine ⟨890228085948410417814301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18991532500232755580038421 890228085948410417814301)
                    ·
                      rfl

theorem cell23_5201139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 6].length) (baseStart_5201139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201139 prefixEnd_5201139 := by exact prefixLift 5201139
  have htrace : WordTrace (prefixWord ++ tailWord_5201139) baseStart_5201139 baseEnd_5201139 := by
    simpa [prefixWord, tailWord_5201139, baseEnd_5201139] using wordTrace_append hprefix tailTrace_5201139
  have hstable : (prefixWord ++ tailWord_5201139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201139).length < 2 ^ (prefixWord ++ tailWord_5201139).sum := by decide
  have hdescent : baseEnd_5201139 < baseStart_5201139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201150 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_5201150 : Nat := 118140960795 + 5201150 * 2 ^ 59
def prefixEnd_5201150 : Nat := 4983230072969 + 3 ^ 40 * 5201150 * 2
def baseEnd_5201150 : Nat := 2670689906132430710405353

theorem tailTrace_5201150 : CollatzResearch.WordTrace tailWord_5201150 prefixEnd_5201150 2670689906132430710405353 := by
  unfold tailWord_5201150
  simp only [CollatzResearch.WordTrace]
  refine ⟨23712690638391163818134113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126467683404752873696715269 23712690638391163818134113)
  ·
    refine ⟨17784517978793372863600585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23712690638391163818134113 17784517978793372863600585)
    ·
      refine ⟨13338388484095029647700439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17784517978793372863600585 13338388484095029647700439)
      ·
        refine ⟨20007582726142544471550659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13338388484095029647700439 20007582726142544471550659)
        ·
          refine ⟨30011374089213816707325989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20007582726142544471550659 30011374089213816707325989)
          ·
            refine ⟨5627132641727590632623623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30011374089213816707325989 5627132641727590632623623)
            ·
              refine ⟨8440698962591385948935435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627132641727590632623623 8440698962591385948935435)
              ·
                refine ⟨12661048443887078923403153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440698962591385948935435 12661048443887078923403153)
                ·
                  refine ⟨9495786332915309192552365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12661048443887078923403153 9495786332915309192552365)
                  ·
                    refine ⟨3560919874843240947207137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9495786332915309192552365 3560919874843240947207137)
                    ·
                      refine ⟨2670689906132430710405353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560919874843240947207137 2670689906132430710405353)
                      ·
                        rfl

theorem cell23_5201150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_5201150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201150 prefixEnd_5201150 := by exact prefixLift 5201150
  have htrace : WordTrace (prefixWord ++ tailWord_5201150) baseStart_5201150 baseEnd_5201150 := by
    simpa [prefixWord, tailWord_5201150, baseEnd_5201150] using wordTrace_append hprefix tailTrace_5201150
  have hstable : (prefixWord ++ tailWord_5201150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201150).length < 2 ^ (prefixWord ++ tailWord_5201150).sum := by decide
  have hdescent : baseEnd_5201150 < baseStart_5201150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201160 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 1, 5]
def baseStart_5201160 : Nat := 118140960795 + 5201160 * 2 ^ 59
def prefixEnd_5201160 : Nat := 4983230072969 + 3 ^ 40 * 5201160 * 2
def baseEnd_5201160 : Nat := 890231680312991890426769

theorem tailTrace_5201160 : CollatzResearch.WordTrace tailWord_5201160 prefixEnd_5201160 890231680312991890426769 := by
  unfold tailWord_5201160
  simp only [CollatzResearch.WordTrace]
  refine ⟨94850944918546541126468467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126467926558062054835291289 94850944918546541126468467)
  ·
    refine ⟨142276417377819811689702701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94850944918546541126468467 142276417377819811689702701)
    ·
      refine ⟨53353656516682429383638513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142276417377819811689702701 53353656516682429383638513)
      ·
        refine ⟨40015242387511822037728885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53353656516682429383638513 40015242387511822037728885)
        ·
          refine ⟨3751428973829233316037083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40015242387511822037728885 3751428973829233316037083)
          ·
            refine ⟨5627143460743849974055625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751428973829233316037083 5627143460743849974055625)
            ·
              refine ⟨4220357595557887480541719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627143460743849974055625 4220357595557887480541719)
              ·
                refine ⟨6330536393336831220812579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220357595557887480541719 6330536393336831220812579)
                ·
                  refine ⟨9495804590005246831218869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330536393336831220812579 9495804590005246831218869)
                  ·
                    refine ⟨890231680312991890426769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9495804590005246831218869 890231680312991890426769)
                    ·
                      rfl

theorem cell23_5201160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_5201160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201160 prefixEnd_5201160 := by exact prefixLift 5201160
  have htrace : WordTrace (prefixWord ++ tailWord_5201160) baseStart_5201160 baseEnd_5201160 := by
    simpa [prefixWord, tailWord_5201160, baseEnd_5201160] using wordTrace_append hprefix tailTrace_5201160
  have hstable : (prefixWord ++ tailWord_5201160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201160).length < 2 ^ (prefixWord ++ tailWord_5201160).sum := by decide
  have hdescent : baseEnd_5201160 < baseStart_5201160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201163 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 1, 1, 4]
def baseStart_5201163 : Nat := 118140960795 + 5201163 * 2 ^ 59
def prefixEnd_5201163 : Nat := 4983230072969 + 3 ^ 40 * 5201163 * 2
def baseEnd_5201163 : Nat := 2670696581380939159542793

theorem tailTrace_5201163 : CollatzResearch.WordTrace tailWord_5201163 prefixEnd_5201163 2670696581380939159542793 := by
  unfold tailWord_5201163
  simp only [CollatzResearch.WordTrace]
  refine ⟨189701999256082213765296143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126467999504054809176864095 189701999256082213765296143)
  ·
    refine ⟨284552998884123320647944215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189701999256082213765296143 284552998884123320647944215)
    ·
      refine ⟨426829498326184980971916323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284552998884123320647944215 426829498326184980971916323)
      ·
        refine ⟨640244247489277471457874485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426829498326184980971916323 640244247489277471457874485)
        ·
          refine ⟨60022898202119762949175733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 640244247489277471457874485 60022898202119762949175733)
          ·
            refine ⟨5627146706448727776485225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60022898202119762949175733 5627146706448727776485225)
            ·
              refine ⟨4220360029836545832363919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627146706448727776485225 4220360029836545832363919)
              ·
                refine ⟨6330540044754818748545879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220360029836545832363919 6330540044754818748545879)
                ·
                  refine ⟨9495810067132228122818819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330540044754818748545879 9495810067132228122818819)
                  ·
                    refine ⟨14243715100698342184228229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9495810067132228122818819 14243715100698342184228229)
                    ·
                      refine ⟨2670696581380939159542793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14243715100698342184228229 2670696581380939159542793)
                      ·
                        rfl

theorem cell23_5201163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 1, 4].length) (baseStart_5201163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201163 prefixEnd_5201163 := by exact prefixLift 5201163
  have htrace : WordTrace (prefixWord ++ tailWord_5201163) baseStart_5201163 baseEnd_5201163 := by
    simpa [prefixWord, tailWord_5201163, baseEnd_5201163] using wordTrace_append hprefix tailTrace_5201163
  have hstable : (prefixWord ++ tailWord_5201163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201163).length < 2 ^ (prefixWord ++ tailWord_5201163).sum := by decide
  have hdescent : baseEnd_5201163 < baseStart_5201163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201180 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_5201180 : Nat := 118140960795 + 5201180 * 2 ^ 59
def prefixEnd_5201180 : Nat := 4983230072969 + 3 ^ 40 * 5201180 * 2
def baseEnd_5201180 : Nat := 2670705310552065593030215

theorem tailTrace_5201180 : CollatzResearch.WordTrace tailWord_5201180 prefixEnd_5201180 2670705310552065593030215 := by
  unfold tailWord_5201180
  simp only [CollatzResearch.WordTrace]
  refine ⟨94851309648510312834332497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126468412864680417112443329 94851309648510312834332497)
  ·
    refine ⟨71138482236382734625749373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94851309648510312834332497 71138482236382734625749373)
    ·
      refine ⟨26676930838643525484656015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71138482236382734625749373 26676930838643525484656015)
      ·
        refine ⟨40015396257965288226984023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26676930838643525484656015 40015396257965288226984023)
        ·
          refine ⟨60023094386947932340476035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40015396257965288226984023 60023094386947932340476035)
          ·
            refine ⟨90034641580421898510714053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60023094386947932340476035 90034641580421898510714053)
            ·
              refine ⟨16881495296329105970758885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90034641580421898510714053 16881495296329105970758885)
              ·
                refine ⟨3165280368061707369517291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16881495296329105970758885 3165280368061707369517291)
                ·
                  refine ⟨4747920552092561054275937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165280368061707369517291 4747920552092561054275937)
                  ·
                    refine ⟨3560940414069420790706953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4747920552092561054275937 3560940414069420790706953)
                    ·
                      refine ⟨2670705310552065593030215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560940414069420790706953 2670705310552065593030215)
                      ·
                        rfl

theorem cell23_5201180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_5201180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201180 prefixEnd_5201180 := by exact prefixLift 5201180
  have htrace : WordTrace (prefixWord ++ tailWord_5201180) baseStart_5201180 baseEnd_5201180 := by
    simpa [prefixWord, tailWord_5201180, baseEnd_5201180] using wordTrace_append hprefix tailTrace_5201180
  have hstable : (prefixWord ++ tailWord_5201180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201180).length < 2 ^ (prefixWord ++ tailWord_5201180).sum := by decide
  have hdescent : baseEnd_5201180 < baseStart_5201180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201223 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_5201223 : Nat := 118140960795 + 5201223 * 2 ^ 59
def prefixEnd_5201223 : Nat := 4983230072969 + 3 ^ 40 * 5201223 * 2
def baseEnd_5201223 : Nat := 2670727390220208924792517

theorem tailTrace_5201223 : CollatzResearch.WordTrace tailWord_5201223 prefixEnd_5201223 2670727390220208924792517 := by
  unfold tailWord_5201223
  simp only [CollatzResearch.WordTrace]
  refine ⟨189704187635864844012480323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126469458423909896008320215 189704187635864844012480323)
  ·
    refine ⟨284556281453797266018720485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189704187635864844012480323 284556281453797266018720485)
    ·
      refine ⟨53354302772586987378510091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284556281453797266018720485 53354302772586987378510091)
      ·
        refine ⟨80031454158880481067765137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53354302772586987378510091 80031454158880481067765137)
        ·
          refine ⟨60023590619160360800823853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80031454158880481067765137 60023590619160360800823853)
          ·
            refine ⟨22508846482185135300308945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60023590619160360800823853 22508846482185135300308945)
            ·
              refine ⟨16881634861638851475231709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22508846482185135300308945 16881634861638851475231709)
              ·
                refine ⟨6330613073114569303211891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16881634861638851475231709 6330613073114569303211891)
                ·
                  refine ⟨9495919609671853954817837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330613073114569303211891 9495919609671853954817837)
                  ·
                    refine ⟨3560969853626945233056689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9495919609671853954817837 3560969853626945233056689)
                    ·
                      refine ⟨2670727390220208924792517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3560969853626945233056689 2670727390220208924792517)
                      ·
                        rfl

theorem cell23_5201223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_5201223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201223 prefixEnd_5201223 := by exact prefixLift 5201223
  have htrace : WordTrace (prefixWord ++ tailWord_5201223) baseStart_5201223 baseEnd_5201223 := by
    simpa [prefixWord, tailWord_5201223, baseEnd_5201223] using wordTrace_append hprefix tailTrace_5201223
  have hstable : (prefixWord ++ tailWord_5201223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201223).length < 2 ^ (prefixWord ++ tailWord_5201223).sum := by decide
  have hdescent : baseEnd_5201223 < baseStart_5201223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201249 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_5201249 : Nat := 118140960795 + 5201249 * 2 ^ 59
def prefixEnd_5201249 : Nat := 4983230072969 + 3 ^ 40 * 5201249 * 2
def baseEnd_5201249 : Nat := 2670740740717225823067397

theorem tailTrace_5201249 : CollatzResearch.WordTrace tailWord_5201249 prefixEnd_5201249 2670740740717225823067397 := by
  unfold tailWord_5201249
  simp only [CollatzResearch.WordTrace]
  refine ⟨189705135933770650452926801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126470090622513766968617867 189705135933770650452926801)
  ·
    refine ⟨142278851950327987839695101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189705135933770650452926801 142278851950327987839695101)
    ·
      refine ⟨53354569481372995439885663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142278851950327987839695101 53354569481372995439885663)
      ·
        refine ⟨80031854222059493159828495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53354569481372995439885663 80031854222059493159828495)
        ·
          refine ⟨120047781333089239739742743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80031854222059493159828495 120047781333089239739742743)
          ·
            refine ⟨180071671999633859609614115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120047781333089239739742743 180071671999633859609614115)
            ·
              refine ⟨270107507999450789414421173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180071671999633859609614115 270107507999450789414421173)
              ·
                refine ⟨25322578874948511507601985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270107507999450789414421173 25322578874948511507601985)
                ·
                  refine ⟨18991934156211383630701489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25322578874948511507601985 18991934156211383630701489)
                  ·
                    refine ⟨14243950617158537723026117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18991934156211383630701489 14243950617158537723026117)
                    ·
                      refine ⟨2670740740717225823067397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14243950617158537723026117 2670740740717225823067397)
                      ·
                        rfl

theorem cell23_5201249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_5201249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201249 prefixEnd_5201249 := by exact prefixLift 5201249
  have htrace : WordTrace (prefixWord ++ tailWord_5201249) baseStart_5201249 baseEnd_5201249 := by
    simpa [prefixWord, tailWord_5201249, baseEnd_5201249] using wordTrace_append hprefix tailTrace_5201249
  have hstable : (prefixWord ++ tailWord_5201249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201249).length < 2 ^ (prefixWord ++ tailWord_5201249).sum := by decide
  have hdescent : baseEnd_5201249 < baseStart_5201249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201276 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 5]
def baseStart_5201276 : Nat := 118140960795 + 5201276 * 2 ^ 59
def prefixEnd_5201276 : Nat := 4983230072969 + 3 ^ 40 * 5201276 * 2
def baseEnd_5201276 : Nat := 296750511632766357492197

theorem tailTrace_5201276 : CollatzResearch.WordTrace tailWord_5201276 prefixEnd_5201276 296750511632766357492197 := by
  unfold tailWord_5201276
  simp only [CollatzResearch.WordTrace]
  refine ⟨94853060352336417032079841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126470747136448556042773121 94853060352336417032079841)
  ·
    refine ⟨71139795264252312774059881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94853060352336417032079841 71139795264252312774059881)
    ·
      refine ⟨53354846448189234580544911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71139795264252312774059881 53354846448189234580544911)
      ·
        refine ⟨80032269672283851870817367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53354846448189234580544911 80032269672283851870817367)
        ·
          refine ⟨120048404508425777806226051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80032269672283851870817367 120048404508425777806226051)
          ·
            refine ⟨180072606762638666709339077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120048404508425777806226051 180072606762638666709339077)
            ·
              refine ⟨33763613767994750008001077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180072606762638666709339077 33763613767994750008001077)
              ·
                refine ⟨3165338790749507813250101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33763613767994750008001077 3165338790749507813250101)
                ·
                  refine ⟨296750511632766357492197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165338790749507813250101 296750511632766357492197)
                  ·
                    rfl

theorem cell23_5201276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_5201276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201276 prefixEnd_5201276 := by exact prefixLift 5201276
  have htrace : WordTrace (prefixWord ++ tailWord_5201276) baseStart_5201276 baseEnd_5201276 := by
    simpa [prefixWord, tailWord_5201276, baseEnd_5201276] using wordTrace_append hprefix tailTrace_5201276
  have hstable : (prefixWord ++ tailWord_5201276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201276).length < 2 ^ (prefixWord ++ tailWord_5201276).sum := by decide
  have hdescent : baseEnd_5201276 < baseStart_5201276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201403 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 2, 3, 2]
def baseStart_5201403 : Nat := 118140960795 + 5201403 * 2 ^ 59
def prefixEnd_5201403 : Nat := 4983230072969 + 3 ^ 40 * 5201403 * 2
def baseEnd_5201403 : Nat := 2670819816738018220541689

theorem tailTrace_5201403 : CollatzResearch.WordTrace tailWord_5201403 prefixEnd_5201403 2670819816738018220541689 := by
  unfold tailWord_5201403
  simp only [CollatzResearch.WordTrace]
  refine ⟨189710752775212734754032863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126473835183475156502688575 189710752775212734754032863)
  ·
    refine ⟨284566129162819102131049295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189710752775212734754032863 284566129162819102131049295)
    ·
      refine ⟨426849193744228653196573943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284566129162819102131049295 426849193744228653196573943)
      ·
        refine ⟨640273790616342979794860915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426849193744228653196573943 640273790616342979794860915)
        ·
          refine ⟨960410685924514469692291373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640273790616342979794860915 960410685924514469692291373)
          ·
            refine ⟨360154007221692926134609265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960410685924514469692291373 360154007221692926134609265)
            ·
              refine ⟨270115505416269694600956949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360154007221692926134609265 270115505416269694600956949)
              ·
                refine ⟨12661664316387641934419857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270115505416269694600956949 12661664316387641934419857)
                ·
                  refine ⟨9496248237290731450814893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12661664316387641934419857 9496248237290731450814893)
                  ·
                    refine ⟨3561093088984024294055585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9496248237290731450814893 3561093088984024294055585)
                    ·
                      refine ⟨2670819816738018220541689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3561093088984024294055585 2670819816738018220541689)
                      ·
                        rfl

theorem cell23_5201403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 3, 2].length) (baseStart_5201403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201403 prefixEnd_5201403 := by exact prefixLift 5201403
  have htrace : WordTrace (prefixWord ++ tailWord_5201403) baseStart_5201403 baseEnd_5201403 := by
    simpa [prefixWord, tailWord_5201403, baseEnd_5201403] using wordTrace_append hprefix tailTrace_5201403
  have hstable : (prefixWord ++ tailWord_5201403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201403).length < 2 ^ (prefixWord ++ tailWord_5201403).sum := by decide
  have hdescent : baseEnd_5201403 < baseStart_5201403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201443 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 1, 6]
def baseStart_5201443 : Nat := 118140960795 + 5201443 * 2 ^ 59
def prefixEnd_5201443 : Nat := 4983230072969 + 3 ^ 40 * 5201443 * 2
def baseEnd_5201443 : Nat := 890280118654732688013835

theorem tailTrace_5201443 : CollatzResearch.WordTrace tailWord_5201443 prefixEnd_5201443 890280118654732688013835 := by
  unfold tailWord_5201443
  simp only [CollatzResearch.WordTrace]
  refine ⟨189712211695067821585488983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126474807796711881056992655 189712211695067821585488983)
  ·
    refine ⟨284568317542601732378233475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189712211695067821585488983 284568317542601732378233475)
    ·
      refine ⟨426852476313902598567350213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284568317542601732378233475 426852476313902598567350213)
      ·
        refine ⟨80034839308856737231378165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 426852476313902598567350213 80034839308856737231378165)
        ·
          refine ⟨7503266185205319115441703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80034839308856737231378165 7503266185205319115441703)
          ·
            refine ⟨11254899277807978673162555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7503266185205319115441703 11254899277807978673162555)
            ·
              refine ⟨16882348916711968009743833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11254899277807978673162555 16882348916711968009743833)
              ·
                refine ⟨12661761687533976007307875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16882348916711968009743833 12661761687533976007307875)
                ·
                  refine ⟨18992642531300964010961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661761687533976007307875 18992642531300964010961813)
                  ·
                    refine ⟨890280118654732688013835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18992642531300964010961813 890280118654732688013835)
                    ·
                      rfl

theorem cell23_5201443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 6].length) (baseStart_5201443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201443 prefixEnd_5201443 := by exact prefixLift 5201443
  have htrace : WordTrace (prefixWord ++ tailWord_5201443) baseStart_5201443 baseEnd_5201443 := by
    simpa [prefixWord, tailWord_5201443, baseEnd_5201443] using wordTrace_append hprefix tailTrace_5201443
  have hstable : (prefixWord ++ tailWord_5201443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201443).length < 2 ^ (prefixWord ++ tailWord_5201443).sum := by decide
  have hdescent : baseEnd_5201443 < baseStart_5201443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201483 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 3]
def baseStart_5201483 : Nat := 118140960795 + 5201483 * 2 ^ 59
def prefixEnd_5201483 : Nat := 4983230072969 + 3 ^ 40 * 5201483 * 2
def baseEnd_5201483 : Nat := 2670860895190377907541321

theorem tailTrace_5201483 : CollatzResearch.WordTrace tailWord_5201483 prefixEnd_5201483 2670860895190377907541321 := by
  unfold tailWord_5201483
  simp only [CollatzResearch.WordTrace]
  refine ⟨189713670614922908416945103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126475780409948605611296735 189713670614922908416945103)
  ·
    refine ⟨284570505922384362625417655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189713670614922908416945103 284570505922384362625417655)
    ·
      refine ⟨426855758883576543938126483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284570505922384362625417655 426855758883576543938126483)
      ·
        refine ⟨640283638325364815907189725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426855758883576543938126483 640283638325364815907189725)
        ·
          refine ⟨240106364372011805965196147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640283638325364815907189725 240106364372011805965196147)
          ·
            refine ⟨360159546558017708947794221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240106364372011805965196147 360159546558017708947794221)
            ·
              refine ⟨135059829959256640855422833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360159546558017708947794221 135059829959256640855422833)
              ·
                refine ⟨101294872469442480641567125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135059829959256640855422833 101294872469442480641567125)
                ·
                  refine ⟨4748197147005116280073459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101294872469442480641567125 4748197147005116280073459)
                  ·
                    refine ⟨7122295720507674420110189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4748197147005116280073459 7122295720507674420110189)
                    ·
                      refine ⟨2670860895190377907541321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122295720507674420110189 2670860895190377907541321)
                      ·
                        rfl

theorem cell23_5201483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 3].length) (baseStart_5201483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201483 prefixEnd_5201483 := by exact prefixLift 5201483
  have htrace : WordTrace (prefixWord ++ tailWord_5201483) baseStart_5201483 baseEnd_5201483 := by
    simpa [prefixWord, tailWord_5201483, baseEnd_5201483] using wordTrace_append hprefix tailTrace_5201483
  have hstable : (prefixWord ++ tailWord_5201483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201483).length < 2 ^ (prefixWord ++ tailWord_5201483).sum := by decide
  have hdescent : baseEnd_5201483 < baseStart_5201483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201486 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_5201486 : Nat := 118140960795 + 5201486 * 2 ^ 59
def prefixEnd_5201486 : Nat := 4983230072969 + 3 ^ 40 * 5201486 * 2
def baseEnd_5201486 : Nat := 890287478544113798601269

theorem tailTrace_5201486 : CollatzResearch.WordTrace tailWord_5201486 prefixEnd_5201486 890287478544113798601269 := by
  unfold tailWord_5201486
  simp only [CollatzResearch.WordTrace]
  refine ⟨23714222504239004991163039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126475853355941359952869541 23714222504239004991163039)
  ·
    refine ⟨35571333756358507486744559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23714222504239004991163039 35571333756358507486744559)
    ·
      refine ⟨53357000634537761230116839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35571333756358507486744559 53357000634537761230116839)
      ·
        refine ⟨80035500951806641845175259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53357000634537761230116839 80035500951806641845175259)
        ·
          refine ⟨120053251427709962767762889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80035500951806641845175259 120053251427709962767762889)
          ·
            refine ⟨90039938570782472075822167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120053251427709962767762889 90039938570782472075822167)
            ·
              refine ⟨135059907856173708113733251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90039938570782472075822167 135059907856173708113733251)
              ·
                refine ⟨202589861784260562170599877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135059907856173708113733251 202589861784260562170599877)
                ·
                  refine ⟨37985599084548855406987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202589861784260562170599877 37985599084548855406987477)
                  ·
                    refine ⟨890287478544113798601269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37985599084548855406987477 890287478544113798601269)
                    ·
                      rfl

theorem cell23_5201486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_5201486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201486 prefixEnd_5201486 := by exact prefixLift 5201486
  have htrace : WordTrace (prefixWord ++ tailWord_5201486) baseStart_5201486 baseEnd_5201486 := by
    simpa [prefixWord, tailWord_5201486, baseEnd_5201486] using wordTrace_append hprefix tailTrace_5201486
  have hstable : (prefixWord ++ tailWord_5201486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201486).length < 2 ^ (prefixWord ++ tailWord_5201486).sum := by decide
  have hdescent : baseEnd_5201486 < baseStart_5201486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201496 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_5201496 : Nat := 118140960795 + 5201496 * 2 ^ 59
def prefixEnd_5201496 : Nat := 4983230072969 + 3 ^ 40 * 5201496 * 2
def baseEnd_5201496 : Nat := 2670867570438886356678761

theorem tailTrace_5201496 : CollatzResearch.WordTrace tailWord_5201496 prefixEnd_5201496 2670867570438886356678761 := by
  unfold tailWord_5201496
  simp only [CollatzResearch.WordTrace]
  refine ⟨94857072381937905818584171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126476096509250541091445561 94857072381937905818584171)
  ·
    refine ⟨142285608572906858727876257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94857072381937905818584171 142285608572906858727876257)
    ·
      refine ⟨106714206429680144045907193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142285608572906858727876257 106714206429680144045907193)
      ·
        refine ⟨80035654822260108034430395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106714206429680144045907193 80035654822260108034430395)
        ·
          refine ⟨120053482233390162051645593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80035654822260108034430395 120053482233390162051645593)
          ·
            refine ⟨90040111675042621538734195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120053482233390162051645593 90040111675042621538734195)
            ·
              refine ⟨135060167512563932308101293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90040111675042621538734195 135060167512563932308101293)
              ·
                refine ⟨50647562817211474615537985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135060167512563932308101293 50647562817211474615537985)
                ·
                  refine ⟨37985672112908605961653489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50647562817211474615537985 37985672112908605961653489)
                  ·
                    refine ⟨28489254084681454471240117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37985672112908605961653489 28489254084681454471240117)
                    ·
                      refine ⟨2670867570438886356678761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28489254084681454471240117 2670867570438886356678761)
                      ·
                        rfl

theorem cell23_5201496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_5201496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201496 prefixEnd_5201496 := by exact prefixLift 5201496
  have htrace : WordTrace (prefixWord ++ tailWord_5201496) baseStart_5201496 baseEnd_5201496 := by
    simpa [prefixWord, tailWord_5201496, baseEnd_5201496] using wordTrace_append hprefix tailTrace_5201496
  have hstable : (prefixWord ++ tailWord_5201496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201496).length < 2 ^ (prefixWord ++ tailWord_5201496).sum := by decide
  have hdescent : baseEnd_5201496 < baseStart_5201496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201500 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_5201500 : Nat := 118140960795 + 5201500 * 2 ^ 59
def prefixEnd_5201500 : Nat := 4983230072969 + 3 ^ 40 * 5201500 * 2
def baseEnd_5201500 : Nat := 2670869624361504341028743

theorem tailTrace_5201500 : CollatzResearch.WordTrace tailWord_5201500 prefixEnd_5201500 2670869624361504341028743 := by
  unfold tailWord_5201500
  simp only [CollatzResearch.WordTrace]
  refine ⟨94857145327930660160156977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126476193770574213546875969 94857145327930660160156977)
  ·
    refine ⟨71142858995947995120117733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94857145327930660160156977 71142858995947995120117733)
    ·
      refine ⟨13339286061740249085022075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71142858995947995120117733 13339286061740249085022075)
      ·
        refine ⟨20008929092610373627533113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13339286061740249085022075 20008929092610373627533113)
        ·
          refine ⟨15006696819457780220649835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20008929092610373627533113 15006696819457780220649835)
          ·
            refine ⟨22510045229186670330974753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15006696819457780220649835 22510045229186670330974753)
            ·
              refine ⟨16882533921890002748231065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22510045229186670330974753 16882533921890002748231065)
              ·
                refine ⟨12661900441417502061173299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16882533921890002748231065 12661900441417502061173299)
                ·
                  refine ⟨18992850662126253091759949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661900441417502061173299 18992850662126253091759949)
                  ·
                    refine ⟨7122318998297344909409981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18992850662126253091759949 7122318998297344909409981)
                    ·
                      refine ⟨2670869624361504341028743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122318998297344909409981 2670869624361504341028743)
                      ·
                        rfl

theorem cell23_5201500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_5201500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201500 prefixEnd_5201500 := by exact prefixLift 5201500
  have htrace : WordTrace (prefixWord ++ tailWord_5201500) baseStart_5201500 baseEnd_5201500 := by
    simpa [prefixWord, tailWord_5201500, baseEnd_5201500] using wordTrace_append hprefix tailTrace_5201500
  have hstable : (prefixWord ++ tailWord_5201500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201500).length < 2 ^ (prefixWord ++ tailWord_5201500).sum := by decide
  have hdescent : baseEnd_5201500 < baseStart_5201500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201501 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5201501 : Nat := 118140960795 + 5201501 * 2 ^ 59
def prefixEnd_5201501 : Nat := 4983230072969 + 3 ^ 40 * 5201501 * 2
def baseEnd_5201501 : Nat := 2670870137842158837116239

theorem tailTrace_5201501 : CollatzResearch.WordTrace tailWord_5201501 prefixEnd_5201501 2670870137842158837116239 := by
  unfold tailWord_5201501
  simp only [CollatzResearch.WordTrace]
  refine ⟨189714327128857697491100357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126476218085905131660733571 189714327128857697491100357)
  ·
    refine ⟨35571436336660818279581317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189714327128857697491100357 35571436336660818279581317)
    ·
      refine ⟨6669644313123903427421497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35571436336660818279581317 6669644313123903427421497)
      ·
        refine ⟨5002233234842927570566123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6669644313123903427421497 5002233234842927570566123)
        ·
          refine ⟨7503349852264391355849185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5002233234842927570566123 7503349852264391355849185)
          ·
            refine ⟨5627512389198293516886889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7503349852264391355849185 5627512389198293516886889)
            ·
              refine ⟨4220634291898720137665167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627512389198293516886889 4220634291898720137665167)
              ·
                refine ⟨6330951437848080206497751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220634291898720137665167 6330951437848080206497751)
                ·
                  refine ⟨9496427156772120309746627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6330951437848080206497751 9496427156772120309746627)
                  ·
                    refine ⟨14244640735158180464619941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9496427156772120309746627 14244640735158180464619941)
                    ·
                      refine ⟨2670870137842158837116239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14244640735158180464619941 2670870137842158837116239)
                      ·
                        rfl

theorem cell23_5201501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5201501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201501 prefixEnd_5201501 := by exact prefixLift 5201501
  have htrace : WordTrace (prefixWord ++ tailWord_5201501) baseStart_5201501 baseEnd_5201501 := by
    simpa [prefixWord, tailWord_5201501, baseEnd_5201501] using wordTrace_append hprefix tailTrace_5201501
  have hstable : (prefixWord ++ tailWord_5201501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201501).length < 2 ^ (prefixWord ++ tailWord_5201501).sum := by decide
  have hdescent : baseEnd_5201501 < baseStart_5201501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201517 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5201517 : Nat := 118140960795 + 5201517 * 2 ^ 59
def prefixEnd_5201517 : Nat := 4983230072969 + 3 ^ 40 * 5201517 * 2
def baseEnd_5201517 : Nat := 2670878353532630774516165

theorem tailTrace_5201517 : CollatzResearch.WordTrace tailWord_5201517 prefixEnd_5201517 2670878353532630774516165 := by
  unfold tailWord_5201517
  simp only [CollatzResearch.WordTrace]
  refine ⟨189714910696799732223682805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126476607131199821482455203 189714910696799732223682805)
  ·
    refine ⟨17785772877824974895970263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189714910696799732223682805 17785772877824974895970263)
    ·
      refine ⟨26678659316737462343955395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17785772877824974895970263 26678659316737462343955395)
      ·
        refine ⟨40017988975106193515933093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26678659316737462343955395 40017988975106193515933093)
        ·
          refine ⟨7503372932832411284237455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40017988975106193515933093 7503372932832411284237455)
          ·
            refine ⟨11255059399248616926356183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7503372932832411284237455 11255059399248616926356183)
            ·
              refine ⟨16882589098872925389534275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255059399248616926356183 16882589098872925389534275)
              ·
                refine ⟨25323883648309388084301413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16882589098872925389534275 25323883648309388084301413)
                ·
                  refine ⟨4748228184058010265806515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25323883648309388084301413 4748228184058010265806515)
                  ·
                    refine ⟨7122342276087015398709773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4748228184058010265806515 7122342276087015398709773)
                    ·
                      refine ⟨2670878353532630774516165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122342276087015398709773 2670878353532630774516165)
                      ·
                        rfl

theorem cell23_5201517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5201517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201517 prefixEnd_5201517 := by exact prefixLift 5201517
  have htrace : WordTrace (prefixWord ++ tailWord_5201517) baseStart_5201517 baseEnd_5201517 := by
    simpa [prefixWord, tailWord_5201517, baseEnd_5201517] using wordTrace_append hprefix tailTrace_5201517
  have hstable : (prefixWord ++ tailWord_5201517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201517).length < 2 ^ (prefixWord ++ tailWord_5201517).sum := by decide
  have hdescent : baseEnd_5201517 < baseStart_5201517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201533 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_5201533 : Nat := 118140960795 + 5201533 * 2 ^ 59
def prefixEnd_5201533 : Nat := 4983230072969 + 3 ^ 40 * 5201533 * 2
def baseEnd_5201533 : Nat := 890295523074367570638697

theorem tailTrace_5201533 : CollatzResearch.WordTrace tailWord_5201533 prefixEnd_5201533 890295523074367570638697 := by
  unfold tailWord_5201533
  simp only [CollatzResearch.WordTrace]
  refine ⟨189715494264741766956265253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126476996176494511304176835 189715494264741766956265253)
  ·
    refine ⟨35571655174639081304299735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189715494264741766956265253 35571655174639081304299735)
    ·
      refine ⟨53357482761958621956449603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35571655174639081304299735 53357482761958621956449603)
      ·
        refine ⟨80036224142937932934674405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53357482761958621956449603 80036224142937932934674405)
        ·
          refine ⟨15006792026800862425251451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80036224142937932934674405 15006792026800862425251451)
          ·
            refine ⟨22510188040201293637877177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15006792026800862425251451 22510188040201293637877177)
            ·
              refine ⟨16882641030150970228407883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22510188040201293637877177 16882641030150970228407883)
              ·
                refine ⟨25323961545226455342611825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16882641030150970228407883 25323961545226455342611825)
                ·
                  refine ⟨18992971158919841506958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25323961545226455342611825 18992971158919841506958869)
                  ·
                    refine ⟨890295523074367570638697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18992971158919841506958869 890295523074367570638697)
                    ·
                      rfl

theorem cell23_5201533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_5201533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201533 prefixEnd_5201533 := by exact prefixLift 5201533
  have htrace : WordTrace (prefixWord ++ tailWord_5201533) baseStart_5201533 baseEnd_5201533 := by
    simpa [prefixWord, tailWord_5201533, baseEnd_5201533] using wordTrace_append hprefix tailTrace_5201533
  have hstable : (prefixWord ++ tailWord_5201533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201533).length < 2 ^ (prefixWord ++ tailWord_5201533).sum := by decide
  have hdescent : baseEnd_5201533 < baseStart_5201533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5201573 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_5201573 : Nat := 118140960795 + 5201573 * 2 ^ 59
def prefixEnd_5201573 : Nat := 4983230072969 + 3 ^ 40 * 5201573 * 2
def baseEnd_5201573 : Nat := 2670907108449282555415907

theorem tailTrace_5201573 : CollatzResearch.WordTrace tailWord_5201573 prefixEnd_5201573 2670907108449282555415907 := by
  unfold tailWord_5201573
  simp only [CollatzResearch.WordTrace]
  refine ⟨189716953184596853787721373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126477968789731235858480915 189716953184596853787721373)
  ·
    refine ⟨71143857444223820170395515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189716953184596853787721373 71143857444223820170395515)
    ·
      refine ⟨106715786166335730255593273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71143857444223820170395515 106715786166335730255593273)
      ·
        refine ⟨80036839624751797691694955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106715786166335730255593273 80036839624751797691694955)
        ·
          refine ⟨120055259437127696537542433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80036839624751797691694955 120055259437127696537542433)
          ·
            refine ⟨90041444577845772403156825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120055259437127696537542433 90041444577845772403156825)
            ·
              refine ⟨67531083433384329302367619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90041444577845772403156825 67531083433384329302367619)
              ·
                refine ⟨101296625150076493953551429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67531083433384329302367619 101296625150076493953551429)
                ·
                  refine ⟨18993117215639342616290893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101296625150076493953551429 18993117215639342616290893)
                  ·
                    refine ⟨7122418955864753481109085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18993117215639342616290893 7122418955864753481109085)
                    ·
                      refine ⟨2670907108449282555415907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7122418955864753481109085 2670907108449282555415907)
                      ·
                        rfl

theorem cell23_5201573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_5201573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5201573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5201573 prefixEnd_5201573 := by exact prefixLift 5201573
  have htrace : WordTrace (prefixWord ++ tailWord_5201573) baseStart_5201573 baseEnd_5201573 := by
    simpa [prefixWord, tailWord_5201573, baseEnd_5201573] using wordTrace_append hprefix tailTrace_5201573
  have hstable : (prefixWord ++ tailWord_5201573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5201573).length < 2 ^ (prefixWord ++ tailWord_5201573).sum := by decide
  have hdescent : baseEnd_5201573 < baseStart_5201573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5201573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
