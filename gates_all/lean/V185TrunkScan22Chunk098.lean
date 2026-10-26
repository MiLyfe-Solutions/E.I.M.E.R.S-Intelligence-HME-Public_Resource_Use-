import V185TrunkScan22Chunk097

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_878625 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_878625 : Nat := 118140960795 + 878625 * 2 ^ 59
def prefixEnd_878625 : Nat := 4983230072969 + 3 ^ 40 * 878625 * 2
def baseEnd_878625 : Nat := 300771293371153406231189

theorem tailTrace_878625 : CollatzResearch.WordTrace tailWord_878625 prefixEnd_878625 300771293371153406231189 := by
  unfold tailWord_878625
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046086441899157048445329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21364057627932771365630219 32046086441899157048445329)
  ·
    refine ⟨24034564831424367786333997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32046086441899157048445329 24034564831424367786333997)
    ·
      refine ⟨9012961811784137919875249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24034564831424367786333997 9012961811784137919875249)
      ·
        refine ⟨6759721358838103439906437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9012961811784137919875249 6759721358838103439906437)
        ·
          refine ⟨1267447754782144394982457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6759721358838103439906437 1267447754782144394982457)
          ·
            refine ⟨950585816086608296236843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267447754782144394982457 950585816086608296236843)
            ·
              refine ⟨1425878724129912444355265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950585816086608296236843 1425878724129912444355265)
              ·
                refine ⟨1069409043097434333266449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425878724129912444355265 1069409043097434333266449)
                ·
                  refine ⟨802056782323075749949837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069409043097434333266449 802056782323075749949837)
                  ·
                    refine ⟨300771293371153406231189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802056782323075749949837 300771293371153406231189)
                    ·
                      rfl

theorem cell22_878625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_878625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878625 prefixEnd_878625 := by exact prefixLift 878625
  have htrace : WordTrace (prefixWord ++ tailWord_878625) baseStart_878625 baseEnd_878625 := by
    simpa [prefixWord, tailWord_878625, baseEnd_878625] using wordTrace_append hprefix tailTrace_878625
  have hstable : (prefixWord ++ tailWord_878625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878625).length < 2 ^ (prefixWord ++ tailWord_878625).sum := by decide
  have hdescent : baseEnd_878625 < baseStart_878625 := by decide
  rcases family_descends (prefixWord ++ tailWord_878625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878664 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_878664 : Nat := 118140960795 + 878664 * 2 ^ 59
def prefixEnd_878664 : Nat := 4983230072969 + 3 ^ 40 * 878664 * 2
def baseEnd_878664 : Nat := 300784643868170304506069

theorem tailTrace_878664 : CollatzResearch.WordTrace tailWord_878664 prefixEnd_878664 300784643868170304506069 := by
  unfold tailWord_878664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023754444378933354557523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21365005925838577806076697 16023754444378933354557523)
  ·
    refine ⟨24035631666568400031836285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16023754444378933354557523 24035631666568400031836285)
    ·
      refine ⟨9013361874963150011938607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24035631666568400031836285 9013361874963150011938607)
      ·
        refine ⟨13520042812444725017907911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013361874963150011938607 13520042812444725017907911)
        ·
          refine ⟨20280064218667087526861867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520042812444725017907911 20280064218667087526861867)
          ·
            refine ⟨30420096328000631290292801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20280064218667087526861867 30420096328000631290292801)
            ·
              refine ⟨22815072246000473467719601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30420096328000631290292801 22815072246000473467719601)
              ·
                refine ⟨17111304184500355100789701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22815072246000473467719601 17111304184500355100789701)
                ·
                  refine ⟨3208369534593816581398069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17111304184500355100789701 3208369534593816581398069)
                  ·
                    refine ⟨300784643868170304506069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3208369534593816581398069 300784643868170304506069)
                    ·
                      rfl

theorem cell22_878664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_878664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878664 prefixEnd_878664 := by exact prefixLift 878664
  have htrace : WordTrace (prefixWord ++ tailWord_878664) baseStart_878664 baseEnd_878664 := by
    simpa [prefixWord, tailWord_878664, baseEnd_878664] using wordTrace_append hprefix tailTrace_878664
  have hstable : (prefixWord ++ tailWord_878664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878664).length < 2 ^ (prefixWord ++ tailWord_878664).sum := by decide
  have hdescent : baseEnd_878664 < baseStart_878664 := by decide
  rcases family_descends (prefixWord ++ tailWord_878664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878670 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_878670 : Nat := 118140960795 + 878670 * 2 ^ 59
def prefixEnd_878670 : Nat := 4983230072969 + 3 ^ 40 * 878670 * 2
def baseEnd_878670 : Nat := 300786697790788288856051

theorem tailTrace_878670 : CollatzResearch.WordTrace tailWord_878670 prefixEnd_878670 300786697790788288856051 := by
  unfold tailWord_878670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005965965842016216729183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21365151817824086489222309 4005965965842016216729183)
  ·
    refine ⟨6008948948763024325093775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4005965965842016216729183 6008948948763024325093775)
    ·
      refine ⟨9013423423144536487640663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008948948763024325093775 9013423423144536487640663)
      ·
        refine ⟨13520135134716804731460995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013423423144536487640663 13520135134716804731460995)
        ·
          refine ⟨20280202702075207097191493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520135134716804731460995 20280202702075207097191493)
          ·
            refine ⟨3802538006639101330723405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20280202702075207097191493 3802538006639101330723405)
            ·
              refine ⟨1425951752489662999021277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3802538006639101330723405 1425951752489662999021277)
              ·
                refine ⟨534731907183623624632979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1425951752489662999021277 534731907183623624632979)
                ·
                  refine ⟨802097860775435436949469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534731907183623624632979 802097860775435436949469)
                  ·
                    refine ⟨300786697790788288856051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802097860775435436949469 300786697790788288856051)
                    ·
                      rfl

theorem cell22_878670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_878670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878670 prefixEnd_878670 := by exact prefixLift 878670
  have htrace : WordTrace (prefixWord ++ tailWord_878670) baseStart_878670 baseEnd_878670 := by
    simpa [prefixWord, tailWord_878670, baseEnd_878670] using wordTrace_append hprefix tailTrace_878670
  have hstable : (prefixWord ++ tailWord_878670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878670).length < 2 ^ (prefixWord ++ tailWord_878670).sum := by decide
  have hdescent : baseEnd_878670 < baseStart_878670 := by decide
  rcases family_descends (prefixWord ++ tailWord_878670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878713 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_878713 : Nat := 118140960795 + 878713 * 2 ^ 59
def prefixEnd_878713 : Nat := 4983230072969 + 3 ^ 40 * 878713 * 2
def baseEnd_878713 : Nat := 300801417569550510030919

theorem tailTrace_878713 : CollatzResearch.WordTrace tailWord_878713 prefixEnd_878713 300801417569550510030919 := by
  unfold tailWord_878713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32049296065580348077648793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21366197377053565385099195 32049296065580348077648793)
  ·
    refine ⟨24036972049185261058236595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32049296065580348077648793 24036972049185261058236595)
    ·
      refine ⟨36055458073777891587354893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24036972049185261058236595 36055458073777891587354893)
      ·
        refine ⟨13520796777666709345258085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36055458073777891587354893 13520796777666709345258085)
        ·
          refine ⟨2535149395812508002235891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13520796777666709345258085 2535149395812508002235891)
          ·
            refine ⟨3802724093718762003353837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535149395812508002235891 3802724093718762003353837)
            ·
              refine ⟨1426021535144535751257689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3802724093718762003353837 1426021535144535751257689)
              ·
                refine ⟨1069516151358401813443267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426021535144535751257689 1069516151358401813443267)
                ·
                  refine ⟨1604274227037602720164901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069516151358401813443267 1604274227037602720164901)
                  ·
                    refine ⟨300801417569550510030919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604274227037602720164901 300801417569550510030919)
                    ·
                      rfl

theorem cell22_878713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_878713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878713 prefixEnd_878713 := by exact prefixLift 878713
  have htrace : WordTrace (prefixWord ++ tailWord_878713) baseStart_878713 baseEnd_878713 := by
    simpa [prefixWord, tailWord_878713, baseEnd_878713] using wordTrace_append hprefix tailTrace_878713
  have hstable : (prefixWord ++ tailWord_878713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878713).length < 2 ^ (prefixWord ++ tailWord_878713).sum := by decide
  have hdescent : baseEnd_878713 < baseStart_878713 := by decide
  rcases family_descends (prefixWord ++ tailWord_878713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878730 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_878730 : Nat := 118140960795 + 878730 * 2 ^ 59
def prefixEnd_878730 : Nat := 4983230072969 + 3 ^ 40 * 878730 * 2
def baseEnd_878730 : Nat := 300807237016968132355867

theorem tailTrace_878730 : CollatzResearch.WordTrace tailWord_878730 prefixEnd_878730 300807237016968132355867 := by
  unfold tailWord_878730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012479026629689995254411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21366610737679173320678429 8012479026629689995254411)
  ·
    refine ⟨12018718539944534992881617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8012479026629689995254411 12018718539944534992881617)
    ·
      refine ⟨9014038904958401244661213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12018718539944534992881617 9014038904958401244661213)
      ·
        refine ⟨3380264589359400466747955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9014038904958401244661213 3380264589359400466747955)
        ·
          refine ⟨5070396884039100700121933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380264589359400466747955 5070396884039100700121933)
          ·
            refine ⟨1901398831514662762545725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5070396884039100700121933 1901398831514662762545725)
            ·
              refine ⟨713024561817998535954647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901398831514662762545725 713024561817998535954647)
              ·
                refine ⟨1069536842726997803931971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713024561817998535954647 1069536842726997803931971)
                ·
                  refine ⟨1604305264090496705897957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069536842726997803931971 1604305264090496705897957)
                  ·
                    refine ⟨300807237016968132355867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604305264090496705897957 300807237016968132355867)
                    ·
                      rfl

theorem cell22_878730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_878730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878730 prefixEnd_878730 := by exact prefixLift 878730
  have htrace : WordTrace (prefixWord ++ tailWord_878730) baseStart_878730 baseEnd_878730 := by
    simpa [prefixWord, tailWord_878730, baseEnd_878730] using wordTrace_append hprefix tailTrace_878730
  have hstable : (prefixWord ++ tailWord_878730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878730).length < 2 ^ (prefixWord ++ tailWord_878730).sum := by decide
  have hdescent : baseEnd_878730 < baseStart_878730 := by decide
  rcases family_descends (prefixWord ++ tailWord_878730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878741 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_878741 : Nat := 118140960795 + 878741 * 2 ^ 59
def prefixEnd_878741 : Nat := 4983230072969 + 3 ^ 40 * 878741 * 2
def baseEnd_878741 : Nat := 300811002541767770330833

theorem tailTrace_878741 : CollatzResearch.WordTrace tailWord_878741 prefixEnd_878741 300811002541767770330833 := by
  unfold tailWord_878741
  simp only [CollatzResearch.WordTrace]
  refine ⟨32050317309478908859668077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21366878206319272573112051 32050317309478908859668077)
  ·
    refine ⟨12018868991054590822375529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32050317309478908859668077 12018868991054590822375529)
    ·
      refine ⟨9014151743290943116781647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12018868991054590822375529 9014151743290943116781647)
      ·
        refine ⟨13521227614936414675172471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9014151743290943116781647 13521227614936414675172471)
        ·
          refine ⟨20281841422404622012758707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13521227614936414675172471 20281841422404622012758707)
          ·
            refine ⟨30422762133606933019138061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20281841422404622012758707 30422762133606933019138061)
            ·
              refine ⟨11408535800102599882176773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30422762133606933019138061 11408535800102599882176773)
              ·
                refine ⟨2139100462519237477908145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11408535800102599882176773 2139100462519237477908145)
                ·
                  refine ⟨1604325346889428108431109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139100462519237477908145 1604325346889428108431109)
                  ·
                    refine ⟨300811002541767770330833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604325346889428108431109 300811002541767770330833)
                    ·
                      rfl

theorem cell22_878741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_878741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878741 prefixEnd_878741 := by exact prefixLift 878741
  have htrace : WordTrace (prefixWord ++ tailWord_878741) baseStart_878741 baseEnd_878741 := by
    simpa [prefixWord, tailWord_878741, baseEnd_878741] using wordTrace_append hprefix tailTrace_878741
  have hstable : (prefixWord ++ tailWord_878741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878741).length < 2 ^ (prefixWord ++ tailWord_878741).sum := by decide
  have hdescent : baseEnd_878741 < baseStart_878741 := by decide
  rcases family_descends (prefixWord ++ tailWord_878741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878816 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_878816 : Nat := 118140960795 + 878816 * 2 ^ 59
def prefixEnd_878816 : Nat := 4983230072969 + 3 ^ 40 * 878816 * 2
def baseEnd_878816 : Nat := 300836676574492574705603

theorem tailTrace_878816 : CollatzResearch.WordTrace tailWord_878816 prefixEnd_878816 300836676574492574705603 := by
  unfold tailWord_878816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026526392103598334324151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21368701856138131112432201 16026526392103598334324151)
  ·
    refine ⟨24039789588155397501486227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16026526392103598334324151 24039789588155397501486227)
    ·
      refine ⟨36059684382233096252229341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24039789588155397501486227 36059684382233096252229341)
      ·
        refine ⟨13522381643337411094586003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36059684382233096252229341 13522381643337411094586003)
        ·
          refine ⟨20283572465006116641879005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13522381643337411094586003 20283572465006116641879005)
          ·
            refine ⟨7606339674377293740704627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20283572465006116641879005 7606339674377293740704627)
            ·
              refine ⟨11409509511565940611056941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606339674377293740704627 11409509511565940611056941)
              ·
                refine ⟨4278566066837227729146353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11409509511565940611056941 4278566066837227729146353)
                ·
                  refine ⟨3208924550127920796859765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278566066837227729146353 3208924550127920796859765)
                  ·
                    refine ⟨300836676574492574705603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3208924550127920796859765 300836676574492574705603)
                    ·
                      rfl

theorem cell22_878816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_878816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878816 prefixEnd_878816 := by exact prefixLift 878816
  have htrace : WordTrace (prefixWord ++ tailWord_878816) baseStart_878816 baseEnd_878816 := by
    simpa [prefixWord, tailWord_878816, baseEnd_878816] using wordTrace_append hprefix tailTrace_878816
  have hstable : (prefixWord ++ tailWord_878816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878816).length < 2 ^ (prefixWord ++ tailWord_878816).sum := by decide
  have hdescent : baseEnd_878816 < baseStart_878816 := by decide
  rcases family_descends (prefixWord ++ tailWord_878816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878848 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_878848 : Nat := 118140960795 + 878848 * 2 ^ 59
def prefixEnd_878848 : Nat := 4983230072969 + 3 ^ 40 * 878848 * 2
def baseEnd_878848 : Nat := 300847630828455157905505

theorem tailTrace_878848 : CollatzResearch.WordTrace tailWord_878848 prefixEnd_878848 300847630828455157905505 := by
  unfold tailWord_878848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027109960045633066906599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21369479946727510755875465 16027109960045633066906599)
  ·
    refine ⟨24040664940068449600359899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16027109960045633066906599 24040664940068449600359899)
    ·
      refine ⟨36060997410102674400539849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24040664940068449600359899 36060997410102674400539849)
      ·
        refine ⟨27045748057577005800404887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36060997410102674400539849 27045748057577005800404887)
        ·
          refine ⟨40568622086365508700607331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27045748057577005800404887 40568622086365508700607331)
          ·
            refine ⟨60852933129548263050910997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40568622086365508700607331 60852933129548263050910997)
            ·
              refine ⟨2852481240447574830511453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60852933129548263050910997 2852481240447574830511453)
              ·
                refine ⟨1069680465167840561441795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852481240447574830511453 1069680465167840561441795)
                ·
                  refine ⟨1604520697751760842162693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069680465167840561441795 1604520697751760842162693)
                  ·
                    refine ⟨300847630828455157905505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604520697751760842162693 300847630828455157905505)
                    ·
                      rfl

theorem cell22_878848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_878848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878848 prefixEnd_878848 := by exact prefixLift 878848
  have htrace : WordTrace (prefixWord ++ tailWord_878848) baseStart_878848 baseEnd_878848 := by
    simpa [prefixWord, tailWord_878848, baseEnd_878848] using wordTrace_append hprefix tailTrace_878848
  have hstable : (prefixWord ++ tailWord_878848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878848).length < 2 ^ (prefixWord ++ tailWord_878848).sum := by decide
  have hdescent : baseEnd_878848 < baseStart_878848 := by decide
  rcases family_descends (prefixWord ++ tailWord_878848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878863 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 4]
def baseStart_878863 : Nat := 118140960795 + 878863 * 2 ^ 59
def prefixEnd_878863 : Nat := 4983230072969 + 3 ^ 40 * 878863 * 2
def baseEnd_878863 : Nat := 100284255211666706260153

theorem tailTrace_878863 : CollatzResearch.WordTrace tailWord_878863 prefixEnd_878863 100284255211666706260153 := by
  unfold tailWord_878863
  simp only [CollatzResearch.WordTrace]
  refine ⟨32054767015036923695609243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21369844676691282463739495 32054767015036923695609243)
  ·
    refine ⟨48082150522555385543413865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32054767015036923695609243 48082150522555385543413865)
    ·
      refine ⟨36061612891916539157560399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48082150522555385543413865 36061612891916539157560399)
      ·
        refine ⟨54092419337874808736340599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36061612891916539157560399 54092419337874808736340599)
        ·
          refine ⟨81138629006812213104510899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54092419337874808736340599 81138629006812213104510899)
          ·
            refine ⟨121707943510218319656766349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81138629006812213104510899 121707943510218319656766349)
            ·
              refine ⟨45640478816331869871287381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121707943510218319656766349 45640478816331869871287381)
              ·
                refine ⟨534849361128889100054149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 45640478816331869871287381 534849361128889100054149)
                ·
                  refine ⟨100284255211666706260153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534849361128889100054149 100284255211666706260153)
                  ·
                    rfl

theorem cell22_878863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 4].length) (baseStart_878863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878863 prefixEnd_878863 := by exact prefixLift 878863
  have htrace : WordTrace (prefixWord ++ tailWord_878863) baseStart_878863 baseEnd_878863 := by
    simpa [prefixWord, tailWord_878863, baseEnd_878863] using wordTrace_append hprefix tailTrace_878863
  have hstable : (prefixWord ++ tailWord_878863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878863).length < 2 ^ (prefixWord ++ tailWord_878863).sum := by decide
  have hdescent : baseEnd_878863 < baseStart_878863 := by decide
  rcases family_descends (prefixWord ++ tailWord_878863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878882 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_878882 : Nat := 118140960795 + 878882 * 2 ^ 59
def prefixEnd_878882 : Nat := 4983230072969 + 3 ^ 40 * 878882 * 2
def baseEnd_878882 : Nat := 300859269723290402555401

theorem tailTrace_878882 : CollatzResearch.WordTrace tailWord_878882 prefixEnd_878882 300859269723290402555401 := by
  unfold tailWord_878882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013865000492022485137725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21370306667978726627033933 8013865000492022485137725)
  ·
    refine ⟨3005199375184508431926647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8013865000492022485137725 3005199375184508431926647)
    ·
      refine ⟨4507799062776762647889971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005199375184508431926647 4507799062776762647889971)
      ·
        refine ⟨6761698594165143971834957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507799062776762647889971 6761698594165143971834957)
        ·
          refine ⟨2535636972811928989438109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6761698594165143971834957 2535636972811928989438109)
          ·
            refine ⟨950863864804473371039291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2535636972811928989438109 950863864804473371039291)
            ·
              refine ⟨1426295797206710056558937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950863864804473371039291 1426295797206710056558937)
              ·
                refine ⟨1069721847905032542419203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426295797206710056558937 1069721847905032542419203)
                ·
                  refine ⟨1604582771857548813628805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069721847905032542419203 1604582771857548813628805)
                  ·
                    refine ⟨300859269723290402555401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604582771857548813628805 300859269723290402555401)
                    ·
                      rfl

theorem cell22_878882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_878882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878882 prefixEnd_878882 := by exact prefixLift 878882
  have htrace : WordTrace (prefixWord ++ tailWord_878882) baseStart_878882 baseEnd_878882 := by
    simpa [prefixWord, tailWord_878882, baseEnd_878882] using wordTrace_append hprefix tailTrace_878882
  have hstable : (prefixWord ++ tailWord_878882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878882).length < 2 ^ (prefixWord ++ tailWord_878882).sum := by decide
  have hdescent : baseEnd_878882 < baseStart_878882 := by decide
  rcases family_descends (prefixWord ++ tailWord_878882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878910 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_878910 : Nat := 118140960795 + 878910 * 2 ^ 59
def prefixEnd_878910 : Nat := 4983230072969 + 3 ^ 40 * 878910 * 2
def baseEnd_878910 : Nat := 300868854695507662855315

theorem tailTrace_878910 : CollatzResearch.WordTrace tailWord_878910 prefixEnd_878910 300868854695507662855315 := by
  unfold tailWord_878910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007060155733331340321273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21370987497244433815046789 4007060155733331340321273)
  ·
    refine ⟨3005295116799998505240955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4007060155733331340321273 3005295116799998505240955)
    ·
      refine ⟨4507942675199997757861433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005295116799998505240955 4507942675199997757861433)
      ·
        refine ⟨3380957006399998318396075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4507942675199997757861433 3380957006399998318396075)
        ·
          refine ⟨5071435509599997477594113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380957006399998318396075 5071435509599997477594113)
          ·
            refine ⟨3803576632199998108195585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5071435509599997477594113 3803576632199998108195585)
            ·
              refine ⟨2852682474149998581146689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803576632199998108195585 2852682474149998581146689)
              ·
                refine ⟨2139511855612498935860017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852682474149998581146689 2139511855612498935860017)
                ·
                  refine ⟨1604633891709374201895013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139511855612498935860017 1604633891709374201895013)
                  ·
                    refine ⟨300868854695507662855315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604633891709374201895013 300868854695507662855315)
                    ·
                      rfl

theorem cell22_878910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_878910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878910 prefixEnd_878910 := by exact prefixLift 878910
  have htrace : WordTrace (prefixWord ++ tailWord_878910) baseStart_878910 baseEnd_878910 := by
    simpa [prefixWord, tailWord_878910, baseEnd_878910] using wordTrace_append hprefix tailTrace_878910
  have hstable : (prefixWord ++ tailWord_878910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878910).length < 2 ^ (prefixWord ++ tailWord_878910).sum := by decide
  have hdescent : baseEnd_878910 < baseStart_878910 := by decide
  rcases family_descends (prefixWord ++ tailWord_878910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879013 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_879013 : Nat := 118140960795 + 879013 * 2 ^ 59
def prefixEnd_879013 : Nat := 4983230072969 + 3 ^ 40 * 879013 * 2
def baseEnd_879013 : Nat := 300904113700449727529999

theorem tailTrace_879013 : CollatzResearch.WordTrace tailWord_879013 prefixEnd_879013 300904113700449727529999 := by
  unfold tailWord_879013
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060237964493499313569693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21373491976328999542379795 32060237964493499313569693)
  ·
    refine ⟨12022589236685062242588635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32060237964493499313569693 12022589236685062242588635)
    ·
      refine ⟨18033883855027593363882953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12022589236685062242588635 18033883855027593363882953)
      ·
        refine ⟨13525412891270695022912215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18033883855027593363882953 13525412891270695022912215)
        ·
          refine ⟨20288119336906042534368323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13525412891270695022912215 20288119336906042534368323)
          ·
            refine ⟨30432179005359063801552485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20288119336906042534368323 30432179005359063801552485)
            ·
              refine ⟨5706033563504824462791091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30432179005359063801552485 5706033563504824462791091)
              ·
                refine ⟨8559050345257236694186637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706033563504824462791091 8559050345257236694186637)
                ·
                  refine ⟨3209643879471463760319989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8559050345257236694186637 3209643879471463760319989)
                  ·
                    refine ⟨300904113700449727529999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3209643879471463760319989 300904113700449727529999)
                    ·
                      rfl

theorem cell22_879013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_879013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879013 prefixEnd_879013 := by exact prefixLift 879013
  have htrace : WordTrace (prefixWord ++ tailWord_879013) baseStart_879013 baseEnd_879013 := by
    simpa [prefixWord, tailWord_879013, baseEnd_879013] using wordTrace_append hprefix tailTrace_879013
  have hstable : (prefixWord ++ tailWord_879013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879013).length < 2 ^ (prefixWord ++ tailWord_879013).sum := by decide
  have hdescent : baseEnd_879013 < baseStart_879013 := by decide
  rcases family_descends (prefixWord ++ tailWord_879013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879047 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 2, 3]
def baseStart_879047 : Nat := 118140960795 + 879047 * 2 ^ 59
def prefixEnd_879047 : Nat := 4983230072969 + 3 ^ 40 * 879047 * 2
def baseEnd_879047 : Nat := 300915752595284972179895

theorem tailTrace_879047 : CollatzResearch.WordTrace tailWord_879047 prefixEnd_879047 300915752595284972179895 := by
  unfold tailWord_879047
  simp only [CollatzResearch.WordTrace]
  refine ⟨32061478046370323120307395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21374318697580215413538263 32061478046370323120307395)
  ·
    refine ⟨48092217069555484680461093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32061478046370323120307395 48092217069555484680461093)
    ·
      refine ⟨9017290700541653377586455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48092217069555484680461093 9017290700541653377586455)
      ·
        refine ⟨13525936050812480066379683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017290700541653377586455 13525936050812480066379683)
        ·
          refine ⟨20288904076218720099569525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13525936050812480066379683 20288904076218720099569525)
          ·
            refine ⟨1902084757145505009334643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20288904076218720099569525 1902084757145505009334643)
            ·
              refine ⟨2853127135718257514001965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902084757145505009334643 2853127135718257514001965)
              ·
                refine ⟨1069922675894346567750737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2853127135718257514001965 1069922675894346567750737)
                ·
                  refine ⟨802442006920759925813053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069922675894346567750737 802442006920759925813053)
                  ·
                    refine ⟨300915752595284972179895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802442006920759925813053 300915752595284972179895)
                    ·
                      rfl

theorem cell22_879047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_879047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879047 prefixEnd_879047 := by exact prefixLift 879047
  have htrace : WordTrace (prefixWord ++ tailWord_879047) baseStart_879047 baseEnd_879047 := by
    simpa [prefixWord, tailWord_879047, baseEnd_879047] using wordTrace_append hprefix tailTrace_879047
  have hstable : (prefixWord ++ tailWord_879047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879047).length < 2 ^ (prefixWord ++ tailWord_879047).sum := by decide
  have hdescent : baseEnd_879047 < baseStart_879047 := by decide
  rcases family_descends (prefixWord ++ tailWord_879047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879060 : List Nat := [2, 4, 1, 2, 2, 1, 2, 8]
def baseStart_879060 : Nat := 118140960795 + 879060 * 2 ^ 59
def prefixEnd_879060 : Nat := 4983230072969 + 3 ^ 40 * 879060 * 2
def baseEnd_879060 : Nat := 33435578084550807956095

theorem tailTrace_879060 : CollatzResearch.WordTrace tailWord_879060 prefixEnd_879060 33435578084550807956095 := by
  unfold tailWord_879060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030976097661613170265317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21374634796882150893687089 16030976097661613170265317)
  ·
    refine ⟨3005808018311552469424747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16030976097661613170265317 3005808018311552469424747)
    ·
      refine ⟨4508712027467328704137121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005808018311552469424747 4508712027467328704137121)
      ·
        refine ⟨3381534020600496528102841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4508712027467328704137121 3381534020600496528102841)
        ·
          refine ⟨2536150515450372396077131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3381534020600496528102841 2536150515450372396077131)
          ·
            refine ⟨3804225773175558594115697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536150515450372396077131 3804225773175558594115697)
            ·
              refine ⟨2853169329881668945586773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3804225773175558594115697 2853169329881668945586773)
              ·
                refine ⟨33435578084550807956095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2853169329881668945586773 33435578084550807956095)
                ·
                  rfl

theorem cell22_879060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_879060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879060 prefixEnd_879060 := by exact prefixLift 879060
  have htrace : WordTrace (prefixWord ++ tailWord_879060) baseStart_879060 baseEnd_879060 := by
    simpa [prefixWord, tailWord_879060, baseEnd_879060] using wordTrace_append hprefix tailTrace_879060
  have hstable : (prefixWord ++ tailWord_879060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879060).length < 2 ^ (prefixWord ++ tailWord_879060).sum := by decide
  have hdescent : baseEnd_879060 < baseStart_879060 := by decide
  rcases family_descends (prefixWord ++ tailWord_879060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879169 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_879169 : Nat := 118140960795 + 879169 * 2 ^ 59
def prefixEnd_879169 : Nat := 4983230072969 + 3 ^ 40 * 879169 * 2
def baseEnd_879169 : Nat := 300957515688517320629521

theorem tailTrace_879169 : CollatzResearch.WordTrace tailWord_879169 prefixEnd_879169 300957515688517320629521 := by
  unfold tailWord_879169
  simp only [CollatzResearch.WordTrace]
  refine ⟨32065927751928337956248561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21377285167952225304165707 32065927751928337956248561)
  ·
    refine ⟨24049445813946253467186421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32065927751928337956248561 24049445813946253467186421)
    ·
      refine ⟨2254635545057461262548727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24049445813946253467186421 2254635545057461262548727)
      ·
        refine ⟨3381953317586191893823091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254635545057461262548727 3381953317586191893823091)
        ·
          refine ⟨5072929976379287840734637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381953317586191893823091 5072929976379287840734637)
          ·
            refine ⟨1902348741142232940275489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5072929976379287840734637 1902348741142232940275489)
            ·
              refine ⟨1426761555856674705206617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902348741142232940275489 1426761555856674705206617)
              ·
                refine ⟨1070071166892506028904963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426761555856674705206617 1070071166892506028904963)
                ·
                  refine ⟨1605106750338759043357445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070071166892506028904963 1605106750338759043357445)
                  ·
                    refine ⟨300957515688517320629521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605106750338759043357445 300957515688517320629521)
                    ·
                      rfl

theorem cell22_879169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_879169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879169 prefixEnd_879169 := by exact prefixLift 879169
  have htrace : WordTrace (prefixWord ++ tailWord_879169) baseStart_879169 baseEnd_879169 := by
    simpa [prefixWord, tailWord_879169, baseEnd_879169] using wordTrace_append hprefix tailTrace_879169
  have hstable : (prefixWord ++ tailWord_879169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879169).length < 2 ^ (prefixWord ++ tailWord_879169).sum := by decide
  have hdescent : baseEnd_879169 < baseStart_879169 := by decide
  rcases family_descends (prefixWord ++ tailWord_879169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879180 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_879180 : Nat := 118140960795 + 879180 * 2 ^ 59
def prefixEnd_879180 : Nat := 4983230072969 + 3 ^ 40 * 879180 * 2
def baseEnd_879180 : Nat := 300961281213316958604487

theorem tailTrace_879180 : CollatzResearch.WordTrace tailWord_879180 prefixEnd_879180 300961281213316958604487 := by
  unfold tailWord_879180
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033164477444243417449497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21377552636592324556599329 16033164477444243417449497)
  ·
    refine ⟨12024873358083182563087123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16033164477444243417449497 12024873358083182563087123)
    ·
      refine ⟨18037310037124773844630685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12024873358083182563087123 18037310037124773844630685)
      ·
        refine ⟨6763991263921790191736507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18037310037124773844630685 6763991263921790191736507)
        ·
          refine ⟨10145986895882685287604761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763991263921790191736507 10145986895882685287604761)
          ·
            refine ⟨7609490171912013965703571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10145986895882685287604761 7609490171912013965703571)
            ·
              refine ⟨11414235257868020948555357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609490171912013965703571 11414235257868020948555357)
              ·
                refine ⟨4280338221700507855708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11414235257868020948555357 4280338221700507855708259)
                ·
                  refine ⟨6420507332550761783562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280338221700507855708259 6420507332550761783562389)
                  ·
                    refine ⟨300961281213316958604487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6420507332550761783562389 300961281213316958604487)
                    ·
                      rfl

theorem cell22_879180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_879180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879180 prefixEnd_879180 := by exact prefixLift 879180
  have htrace : WordTrace (prefixWord ++ tailWord_879180) baseStart_879180 baseEnd_879180 := by
    simpa [prefixWord, tailWord_879180, baseEnd_879180] using wordTrace_append hprefix tailTrace_879180
  have hstable : (prefixWord ++ tailWord_879180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879180).length < 2 ^ (prefixWord ++ tailWord_879180).sum := by decide
  have hdescent : baseEnd_879180 < baseStart_879180 := by decide
  rcases family_descends (prefixWord ++ tailWord_879180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879182 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_879182 : Nat := 118140960795 + 879182 * 2 ^ 59
def prefixEnd_879182 : Nat := 4983230072969 + 3 ^ 40 * 879182 * 2
def baseEnd_879182 : Nat := 300961965854189620054481

theorem tailTrace_879182 : CollatzResearch.WordTrace tailWord_879182 prefixEnd_879182 300961965854189620054481 := by
  unfold tailWord_879182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008300237610155147058975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21377601267254160784314533 4008300237610155147058975)
  ·
    refine ⟨6012450356415232720588463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4008300237610155147058975 6012450356415232720588463)
    ·
      refine ⟨9018675534622849080882695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012450356415232720588463 9018675534622849080882695)
      ·
        refine ⟨13528013301934273621324043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018675534622849080882695 13528013301934273621324043)
        ·
          refine ⟨20292019952901410431986065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528013301934273621324043 20292019952901410431986065)
          ·
            refine ⟨15219014964676057823989549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20292019952901410431986065 15219014964676057823989549)
            ·
              refine ⟨5707130611753521683996081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15219014964676057823989549 5707130611753521683996081)
              ·
                refine ⟨4280347958815141262997061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707130611753521683996081 4280347958815141262997061)
                ·
                  refine ⟨802565242277838986811949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4280347958815141262997061 802565242277838986811949)
                  ·
                    refine ⟨300961965854189620054481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802565242277838986811949 300961965854189620054481)
                    ·
                      rfl

theorem cell22_879182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_879182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879182 prefixEnd_879182 := by exact prefixLift 879182
  have htrace : WordTrace (prefixWord ++ tailWord_879182) baseStart_879182 baseEnd_879182 := by
    simpa [prefixWord, tailWord_879182, baseEnd_879182] using wordTrace_append hprefix tailTrace_879182
  have hstable : (prefixWord ++ tailWord_879182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879182).length < 2 ^ (prefixWord ++ tailWord_879182).sum := by decide
  have hdescent : baseEnd_879182 < baseStart_879182 := by decide
  rcases family_descends (prefixWord ++ tailWord_879182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879257 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 5]
def baseStart_879257 : Nat := 118140960795 + 879257 * 2 ^ 59
def prefixEnd_879257 : Nat := 4983230072969 + 3 ^ 40 * 879257 * 2
def baseEnd_879257 : Nat := 100329213295638141476417

theorem tailTrace_879257 : CollatzResearch.WordTrace tailWord_879257 prefixEnd_879257 100329213295638141476417 := by
  unfold tailWord_879257
  simp only [CollatzResearch.WordTrace]
  refine ⟨32069137375609528985452025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21379424917073019323634683 32069137375609528985452025)
  ·
    refine ⟨24051853031707146739089019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32069137375609528985452025 24051853031707146739089019)
    ·
      refine ⟨36077779547560720108633529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24051853031707146739089019 36077779547560720108633529)
      ·
        refine ⟨27058334660670540081475147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36077779547560720108633529 27058334660670540081475147)
        ·
          refine ⟨40587501991005810122212721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27058334660670540081475147 40587501991005810122212721)
          ·
            refine ⟨30440626493254357591659541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40587501991005810122212721 30440626493254357591659541)
            ·
              refine ⟨1426904366871298012109041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30440626493254357591659541 1426904366871298012109041)
              ·
                refine ⟨1070178275153473509081781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426904366871298012109041 1070178275153473509081781)
                ·
                  refine ⟨100329213295638141476417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1070178275153473509081781 100329213295638141476417)
                  ·
                    rfl

theorem cell22_879257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_879257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879257 prefixEnd_879257 := by exact prefixLift 879257
  have htrace : WordTrace (prefixWord ++ tailWord_879257) baseStart_879257 baseEnd_879257 := by
    simpa [prefixWord, tailWord_879257, baseEnd_879257] using wordTrace_append hprefix tailTrace_879257
  have hstable : (prefixWord ++ tailWord_879257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879257).length < 2 ^ (prefixWord ++ tailWord_879257).sum := by decide
  have hdescent : baseEnd_879257 < baseStart_879257 := by decide
  rcases family_descends (prefixWord ++ tailWord_879257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879304 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_879304 : Nat := 118140960795 + 879304 * 2 ^ 59
def prefixEnd_879304 : Nat := 4983230072969 + 3 ^ 40 * 879304 * 2
def baseEnd_879304 : Nat := 301003728947421968504107

theorem tailTrace_879304 : CollatzResearch.WordTrace tailWord_879304 prefixEnd_879304 301003728947421968504107 := by
  unfold tailWord_879304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035425803219628006206483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21380567737626170674941977 16035425803219628006206483)
  ·
    refine ⟨24053138704829442009309725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16035425803219628006206483 24053138704829442009309725)
    ·
      refine ⟨9019927014311040753491147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24053138704829442009309725 9019927014311040753491147)
      ·
        refine ⟨13529890521466561130236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019927014311040753491147 13529890521466561130236721)
        ·
          refine ⟨10147417891099920847677541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13529890521466561130236721 10147417891099920847677541)
          ·
            refine ⟨1902640854581235158939539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10147417891099920847677541 1902640854581235158939539)
            ·
              refine ⟨2853961281871852738409309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902640854581235158939539 2853961281871852738409309)
              ·
                refine ⟨1070235480701944776903491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2853961281871852738409309 1070235480701944776903491)
                ·
                  refine ⟨1605353221052917165355237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070235480701944776903491 1605353221052917165355237)
                  ·
                    refine ⟨301003728947421968504107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605353221052917165355237 301003728947421968504107)
                    ·
                      rfl

theorem cell22_879304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_879304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879304 prefixEnd_879304 := by exact prefixLift 879304
  have htrace : WordTrace (prefixWord ++ tailWord_879304) baseStart_879304 baseEnd_879304 := by
    simpa [prefixWord, tailWord_879304, baseEnd_879304] using wordTrace_append hprefix tailTrace_879304
  have hstable : (prefixWord ++ tailWord_879304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879304).length < 2 ^ (prefixWord ++ tailWord_879304).sum := by decide
  have hdescent : baseEnd_879304 < baseStart_879304 := by decide
  rcases family_descends (prefixWord ++ tailWord_879304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879319 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 4]
def baseStart_879319 : Nat := 118140960795 + 879319 * 2 ^ 59
def prefixEnd_879319 : Nat := 4983230072969 + 3 ^ 40 * 879319 * 2
def baseEnd_879319 : Nat := 100336287917988976459687

theorem tailTrace_879319 : CollatzResearch.WordTrace tailWord_879319 prefixEnd_879319 100336287917988976459687 := by
  unfold tailWord_879319
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071398701384913574209011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21380932467589942382806007 32071398701384913574209011)
  ·
    refine ⟨48107098052077370361313517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32071398701384913574209011 48107098052077370361313517)
    ·
      refine ⟨18040161769529013885492569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48107098052077370361313517 18040161769529013885492569)
      ·
        refine ⟨13530121327146760414119427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18040161769529013885492569 13530121327146760414119427)
        ·
          refine ⟨20295181990720140621179141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530121327146760414119427 20295181990720140621179141)
          ·
            refine ⟨3805346623260026366471089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20295181990720140621179141 3805346623260026366471089)
            ·
              refine ⟨2854009967445019774853317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3805346623260026366471089 2854009967445019774853317)
              ·
                refine ⟨535126868895941207784997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2854009967445019774853317 535126868895941207784997)
                ·
                  refine ⟨100336287917988976459687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 535126868895941207784997 100336287917988976459687)
                  ·
                    rfl

theorem cell22_879319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 4].length) (baseStart_879319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879319 prefixEnd_879319 := by exact prefixLift 879319
  have htrace : WordTrace (prefixWord ++ tailWord_879319) baseStart_879319 baseEnd_879319 := by
    simpa [prefixWord, tailWord_879319, baseEnd_879319] using wordTrace_append hprefix tailTrace_879319
  have hstable : (prefixWord ++ tailWord_879319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879319).length < 2 ^ (prefixWord ++ tailWord_879319).sum := by decide
  have hdescent : baseEnd_879319 < baseStart_879319 := by decide
  rcases family_descends (prefixWord ++ tailWord_879319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879332 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_879332 : Nat := 118140960795 + 879332 * 2 ^ 59
def prefixEnd_879332 : Nat := 4983230072969 + 3 ^ 40 * 879332 * 2
def baseEnd_879332 : Nat := 301013313919639228804021

theorem tailTrace_879332 : CollatzResearch.WordTrace tailWord_879332 prefixEnd_879332 301013313919639228804021 := by
  unfold tailWord_879332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035936425168908397216125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21381248566891877862954833 16035936425168908397216125)
  ·
    refine ⟨6013476159438340648956047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16035936425168908397216125 6013476159438340648956047)
    ·
      refine ⟨9020214239157510973434071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013476159438340648956047 9020214239157510973434071)
      ·
        refine ⟨13530321358736266460151107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020214239157510973434071 13530321358736266460151107)
        ·
          refine ⟨20295482038104399690226661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530321358736266460151107 20295482038104399690226661)
          ·
            refine ⟨3805402882144574941917499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20295482038104399690226661 3805402882144574941917499)
            ·
              refine ⟨5708104323216862412876249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805402882144574941917499 5708104323216862412876249)
              ·
                refine ⟨4281078242412646809657187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708104323216862412876249 4281078242412646809657187)
                ·
                  refine ⟨6421617363618970214485781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281078242412646809657187 6421617363618970214485781)
                  ·
                    refine ⟨301013313919639228804021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6421617363618970214485781 301013313919639228804021)
                    ·
                      rfl

theorem cell22_879332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_879332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879332 prefixEnd_879332 := by exact prefixLift 879332
  have htrace : WordTrace (prefixWord ++ tailWord_879332) baseStart_879332 baseEnd_879332 := by
    simpa [prefixWord, tailWord_879332, baseEnd_879332] using wordTrace_append hprefix tailTrace_879332
  have hstable : (prefixWord ++ tailWord_879332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879332).length < 2 ^ (prefixWord ++ tailWord_879332).sum := by decide
  have hdescent : baseEnd_879332 < baseStart_879332 := by decide
  rcases family_descends (prefixWord ++ tailWord_879332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879473 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_879473 : Nat := 118140960795 + 879473 * 2 ^ 59
def prefixEnd_879473 : Nat := 4983230072969 + 3 ^ 40 * 879473 * 2
def baseEnd_879473 : Nat := 301061581101161861028589

theorem tailTrace_879473 : CollatzResearch.WordTrace tailWord_879473 prefixEnd_879473 301061581101161861028589 := by
  unfold tailWord_879473
  simp only [CollatzResearch.WordTrace]
  refine ⟨32077015542826997875315073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21384677028551331916876715 32077015542826997875315073)
  ·
    refine ⟨24057761657120248406486305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32077015542826997875315073 24057761657120248406486305)
    ·
      refine ⟨18043321242840186304864729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24057761657120248406486305 18043321242840186304864729)
      ·
        refine ⟨13532490932130139728648547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18043321242840186304864729 13532490932130139728648547)
        ·
          refine ⟨20298736398195209592972821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13532490932130139728648547 20298736398195209592972821)
          ·
            refine ⟨951503268665400449670601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20298736398195209592972821 951503268665400449670601)
            ·
              refine ⟨713627451499050337252951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951503268665400449670601 713627451499050337252951)
              ·
                refine ⟨1070441177248575505879427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713627451499050337252951 1070441177248575505879427)
                ·
                  refine ⟨1605661765872863258819141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070441177248575505879427 1605661765872863258819141)
                  ·
                    refine ⟨301061581101161861028589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605661765872863258819141 301061581101161861028589)
                    ·
                      rfl

theorem cell22_879473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_879473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879473 prefixEnd_879473 := by exact prefixLift 879473
  have htrace : WordTrace (prefixWord ++ tailWord_879473) baseStart_879473 baseEnd_879473 := by
    simpa [prefixWord, tailWord_879473, baseEnd_879473] using wordTrace_append hprefix tailTrace_879473
  have hstable : (prefixWord ++ tailWord_879473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879473).length < 2 ^ (prefixWord ++ tailWord_879473).sum := by decide
  have hdescent : baseEnd_879473 < baseStart_879473 := by decide
  rcases family_descends (prefixWord ++ tailWord_879473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879484 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_879484 : Nat := 118140960795 + 879484 * 2 ^ 59
def prefixEnd_879484 : Nat := 4983230072969 + 3 ^ 40 * 879484 * 2
def baseEnd_879484 : Nat := 301065346625961499003555

theorem tailTrace_879484 : CollatzResearch.WordTrace tailWord_879484 prefixEnd_879484 301065346625961499003555 := by
  unfold tailWord_879484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038708372893573376982753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21384944497191431169310337 16038708372893573376982753)
  ·
    refine ⟨12029031279670180032737065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16038708372893573376982753 12029031279670180032737065)
    ·
      refine ⟨9021773459752635024552799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12029031279670180032737065 9021773459752635024552799)
      ·
        refine ⟨13532660189628952536829199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9021773459752635024552799 13532660189628952536829199)
        ·
          refine ⟨20298990284443428805243799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13532660189628952536829199 20298990284443428805243799)
          ·
            refine ⟨30448485426665143207865699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20298990284443428805243799 30448485426665143207865699)
            ·
              refine ⟨45672728139997714811798549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30448485426665143207865699 45672728139997714811798549)
              ·
                refine ⟨2140909131562392881803057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45672728139997714811798549 2140909131562392881803057)
                ·
                  refine ⟨1605681848671794661352293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140909131562392881803057 1605681848671794661352293)
                  ·
                    refine ⟨301065346625961499003555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605681848671794661352293 301065346625961499003555)
                    ·
                      rfl

theorem cell22_879484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_879484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879484 prefixEnd_879484 := by exact prefixLift 879484
  have htrace : WordTrace (prefixWord ++ tailWord_879484) baseStart_879484 baseEnd_879484 := by
    simpa [prefixWord, tailWord_879484, baseEnd_879484] using wordTrace_append hprefix tailTrace_879484
  have hstable : (prefixWord ++ tailWord_879484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879484).length < 2 ^ (prefixWord ++ tailWord_879484).sum := by decide
  have hdescent : baseEnd_879484 < baseStart_879484 := by decide
  rcases family_descends (prefixWord ++ tailWord_879484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879516 : List Nat := [2, 2, 3, 3, 2, 1, 1, 8]
def baseStart_879516 : Nat := 118140960795 + 879516 * 2 ^ 59
def prefixEnd_879516 : Nat := 4983230072969 + 3 ^ 40 * 879516 * 2
def baseEnd_879516 : Nat := 33452922319991564689273

theorem tailTrace_879516 : CollatzResearch.WordTrace tailWord_879516 prefixEnd_879516 33452922319991564689273 := by
  unfold tailWord_879516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039291940835608109565201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21385722587780810812753601 16039291940835608109565201)
  ·
    refine ⟨12029468955626706082173901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16039291940835608109565201 12029468955626706082173901)
    ·
      refine ⟨4511050858360014780815213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12029468955626706082173901 4511050858360014780815213)
      ·
        refine ⟨1691644071885005542805705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4511050858360014780815213 1691644071885005542805705)
        ·
          refine ⟨1268733053913754157104279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691644071885005542805705 1268733053913754157104279)
          ·
            refine ⟨1903099580870631235656419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268733053913754157104279 1903099580870631235656419)
            ·
              refine ⟨2854649371305946853484629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903099580870631235656419 2854649371305946853484629)
              ·
                refine ⟨33452922319991564689273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2854649371305946853484629 33452922319991564689273)
                ·
                  rfl

theorem cell22_879516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_879516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879516 prefixEnd_879516 := by exact prefixLift 879516
  have htrace : WordTrace (prefixWord ++ tailWord_879516) baseStart_879516 baseEnd_879516 := by
    simpa [prefixWord, tailWord_879516, baseEnd_879516] using wordTrace_append hprefix tailTrace_879516
  have hstable : (prefixWord ++ tailWord_879516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879516).length < 2 ^ (prefixWord ++ tailWord_879516).sum := by decide
  have hdescent : baseEnd_879516 < baseStart_879516 := by decide
  rcases family_descends (prefixWord ++ tailWord_879516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879533 : List Nat := [1, 5, 2, 3, 1, 2, 8]
def baseStart_879533 : Nat := 118140960795 + 879533 * 2 ^ 59
def prefixEnd_879533 : Nat := 4983230072969 + 3 ^ 40 * 879533 * 2
def baseEnd_879533 : Nat := 11151189641753396464015

theorem tailTrace_879533 : CollatzResearch.WordTrace tailWord_879533 prefixEnd_879533 11151189641753396464015 := by
  unfold tailWord_879533
  simp only [CollatzResearch.WordTrace]
  refine ⟨32079203922609628122499253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21386135948406418748332835 32079203922609628122499253)
  ·
    refine ⟨3007425367744652636484305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32079203922609628122499253 3007425367744652636484305)
    ·
      refine ⟨2255569025808489477363229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3007425367744652636484305 2255569025808489477363229)
      ·
        refine ⟨845838384678183554011211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2255569025808489477363229 845838384678183554011211)
        ·
          refine ⟨1268757577017275331016817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845838384678183554011211 1268757577017275331016817)
          ·
            refine ⟨951568182762956498262613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268757577017275331016817 951568182762956498262613)
            ·
              refine ⟨11151189641753396464015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 951568182762956498262613 11151189641753396464015)
              ·
                rfl

theorem cell22_879533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 8].length) (baseStart_879533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879533 prefixEnd_879533 := by exact prefixLift 879533
  have htrace : WordTrace (prefixWord ++ tailWord_879533) baseStart_879533 baseEnd_879533 := by
    simpa [prefixWord, tailWord_879533, baseEnd_879533] using wordTrace_append hprefix tailTrace_879533
  have hstable : (prefixWord ++ tailWord_879533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879533).length < 2 ^ (prefixWord ++ tailWord_879533).sum := by decide
  have hdescent : baseEnd_879533 < baseStart_879533 := by decide
  rcases family_descends (prefixWord ++ tailWord_879533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879544 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_879544 : Nat := 118140960795 + 879544 * 2 ^ 59
def prefixEnd_879544 : Nat := 4983230072969 + 3 ^ 40 * 879544 * 2
def baseEnd_879544 : Nat := 100361961950713780834457

theorem tailTrace_879544 : CollatzResearch.WordTrace tailWord_879544 prefixEnd_879544 100361961950713780834457 := by
  unfold tailWord_879544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039802562784888500574843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21386403417046518000766457 16039802562784888500574843)
  ·
    refine ⟨24059703844177332750862265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16039802562784888500574843 24059703844177332750862265)
    ·
      refine ⟨18044777883132999563146699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24059703844177332750862265 18044777883132999563146699)
      ·
        refine ⟨27067166824699499344720049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18044777883132999563146699 27067166824699499344720049)
        ·
          refine ⟨20300375118524624508540037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27067166824699499344720049 20300375118524624508540037)
          ·
            refine ⟨3806320334723367095351257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20300375118524624508540037 3806320334723367095351257)
            ·
              refine ⟨2854740251042525321513443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806320334723367095351257 2854740251042525321513443)
              ·
                refine ⟨4282110376563787982270165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854740251042525321513443 4282110376563787982270165)
                ·
                  refine ⟨100361961950713780834457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4282110376563787982270165 100361961950713780834457)
                  ·
                    rfl

theorem cell22_879544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_879544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879544 prefixEnd_879544 := by exact prefixLift 879544
  have htrace : WordTrace (prefixWord ++ tailWord_879544) baseStart_879544 baseEnd_879544 := by
    simpa [prefixWord, tailWord_879544, baseEnd_879544] using wordTrace_append hprefix tailTrace_879544
  have hstable : (prefixWord ++ tailWord_879544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879544).length < 2 ^ (prefixWord ++ tailWord_879544).sum := by decide
  have hdescent : baseEnd_879544 < baseStart_879544 := by decide
  rcases family_descends (prefixWord ++ tailWord_879544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879559 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_879559 : Nat := 118140960795 + 879559 * 2 ^ 59
def prefixEnd_879559 : Nat := 4983230072969 + 3 ^ 40 * 879559 * 2
def baseEnd_879559 : Nat := 301091020658686303378325

theorem tailTrace_879559 : CollatzResearch.WordTrace tailWord_879559 prefixEnd_879559 301091020658686303378325 := by
  unfold tailWord_879559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32080152220515434562945731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21386768147010289708630487 32080152220515434562945731)
  ·
    refine ⟨48120228330773151844418597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32080152220515434562945731 48120228330773151844418597)
    ·
      refine ⟨9022542812019965970828487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48120228330773151844418597 9022542812019965970828487)
      ·
        refine ⟨13533814218029948956242731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9022542812019965970828487 13533814218029948956242731)
        ·
          refine ⟨20300721327044923434364097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13533814218029948956242731 20300721327044923434364097)
          ·
            refine ⟨15225540995283692575773073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20300721327044923434364097 15225540995283692575773073)
            ·
              refine ⟨11419155746462769431829805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15225540995283692575773073 11419155746462769431829805)
              ·
                refine ⟨4282183404923538536936177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11419155746462769431829805 4282183404923538536936177)
                ·
                  refine ⟨3211637553692653902702133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282183404923538536936177 3211637553692653902702133)
                  ·
                    refine ⟨301091020658686303378325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3211637553692653902702133 301091020658686303378325)
                    ·
                      rfl

theorem cell22_879559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_879559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879559 prefixEnd_879559 := by exact prefixLift 879559
  have htrace : WordTrace (prefixWord ++ tailWord_879559) baseStart_879559 baseEnd_879559 := by
    simpa [prefixWord, tailWord_879559, baseEnd_879559] using wordTrace_append hprefix tailTrace_879559
  have hstable : (prefixWord ++ tailWord_879559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879559).length < 2 ^ (prefixWord ++ tailWord_879559).sum := by decide
  have hdescent : baseEnd_879559 < baseStart_879559 := by decide
  rcases family_descends (prefixWord ++ tailWord_879559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879621 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_879621 : Nat := 118140960795 + 879621 * 2 ^ 59
def prefixEnd_879621 : Nat := 4983230072969 + 3 ^ 40 * 879621 * 2
def baseEnd_879621 : Nat := 301112244525738808328135

theorem tailTrace_879621 : CollatzResearch.WordTrace tailWord_879621 prefixEnd_879621 301112244525738808328135 := by
  unfold tailWord_879621
  simp only [CollatzResearch.WordTrace]
  refine ⟨32082413546290819151702717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21388275697527212767801811 32082413546290819151702717)
  ·
    refine ⟨12030905079859057181888519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32082413546290819151702717 12030905079859057181888519)
    ·
      refine ⟨18046357619788585772832779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12030905079859057181888519 18046357619788585772832779)
      ·
        refine ⟨27069536429682878659249169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18046357619788585772832779 27069536429682878659249169)
        ·
          refine ⟨20302152322262158994436877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27069536429682878659249169 20302152322262158994436877)
          ·
            refine ⟨7613307120848309622913829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20302152322262158994436877 7613307120848309622913829)
            ·
              refine ⟨1427495085159058054296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7613307120848309622913829 1427495085159058054296343)
              ·
                refine ⟨2141242627738587081444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427495085159058054296343 2141242627738587081444515)
                ·
                  refine ⟨3211863941607880622166773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141242627738587081444515 3211863941607880622166773)
                  ·
                    refine ⟨301112244525738808328135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3211863941607880622166773 301112244525738808328135)
                    ·
                      rfl

theorem cell22_879621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_879621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879621 prefixEnd_879621 := by exact prefixLift 879621
  have htrace : WordTrace (prefixWord ++ tailWord_879621) baseStart_879621 baseEnd_879621 := by
    simpa [prefixWord, tailWord_879621, baseEnd_879621] using wordTrace_append hprefix tailTrace_879621
  have hstable : (prefixWord ++ tailWord_879621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879621).length < 2 ^ (prefixWord ++ tailWord_879621).sum := by decide
  have hdescent : baseEnd_879621 < baseStart_879621 := by decide
  rcases family_descends (prefixWord ++ tailWord_879621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879655 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 4, 3]
def baseStart_879655 : Nat := 118140960795 + 879655 * 2 ^ 59
def prefixEnd_879655 : Nat := 4983230072969 + 3 ^ 40 * 879655 * 2
def baseEnd_879655 : Nat := 301123883420574052978031

theorem tailTrace_879655 : CollatzResearch.WordTrace tailWord_879655 prefixEnd_879655 301123883420574052978031 := by
  unfold tailWord_879655
  simp only [CollatzResearch.WordTrace]
  refine ⟨32083653628167642958440419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21389102418778428638960279 32083653628167642958440419)
  ·
    refine ⟨48125480442251464437660629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32083653628167642958440419 48125480442251464437660629)
    ·
      refine ⟨1127940947865268697757671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48125480442251464437660629 1127940947865268697757671)
      ·
        refine ⟨1691911421797903046636507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127940947865268697757671 1691911421797903046636507)
        ·
          refine ⟨2537867132696854569954761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691911421797903046636507 2537867132696854569954761)
          ·
            refine ⟨1903400349522640927466071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537867132696854569954761 1903400349522640927466071)
            ·
              refine ⟨2855100524283961391199107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903400349522640927466071 2855100524283961391199107)
              ·
                refine ⟨4282650786425942086798661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855100524283961391199107 4282650786425942086798661)
                ·
                  refine ⟨802997022454864141274749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4282650786425942086798661 802997022454864141274749)
                  ·
                    refine ⟨301123883420574052978031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 802997022454864141274749 301123883420574052978031)
                    ·
                      rfl

theorem cell22_879655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_879655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879655 prefixEnd_879655 := by exact prefixLift 879655
  have htrace : WordTrace (prefixWord ++ tailWord_879655) baseStart_879655 baseEnd_879655 := by
    simpa [prefixWord, tailWord_879655, baseEnd_879655] using wordTrace_append hprefix tailTrace_879655
  have hstable : (prefixWord ++ tailWord_879655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879655).length < 2 ^ (prefixWord ++ tailWord_879655).sum := by decide
  have hdescent : baseEnd_879655 < baseStart_879655 := by decide
  rcases family_descends (prefixWord ++ tailWord_879655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879702 : List Nat := [5, 2, 2, 1, 3, 1, 8]
def baseStart_879702 : Nat := 118140960795 + 879702 * 2 ^ 59
def prefixEnd_879702 : Nat := 4983230072969 + 3 ^ 40 * 879702 * 2
def baseEnd_879702 : Nat := 11153332314114133224181

theorem tailTrace_879702 : CollatzResearch.WordTrace tailWord_879702 prefixEnd_879702 11153332314114133224181 := by
  unfold tailWord_879702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005335491187335624087585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21390245239331579990267573 2005335491187335624087585)
  ·
    refine ⟨1504001618390501718065689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2005335491187335624087585 1504001618390501718065689)
    ·
      refine ⟨1128001213792876288549267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1504001618390501718065689 1128001213792876288549267)
      ·
        refine ⟨1692001820689314432823901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128001213792876288549267 1692001820689314432823901)
        ·
          refine ⟨634500682758492912308963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1692001820689314432823901 634500682758492912308963)
          ·
            refine ⟨951751024137739368463445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634500682758492912308963 951751024137739368463445)
            ·
              refine ⟨11153332314114133224181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 951751024137739368463445 11153332314114133224181)
              ·
                rfl

theorem cell22_879702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 8].length) (baseStart_879702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879702 prefixEnd_879702 := by exact prefixLift 879702
  have htrace : WordTrace (prefixWord ++ tailWord_879702) baseStart_879702 baseEnd_879702 := by
    simpa [prefixWord, tailWord_879702, baseEnd_879702] using wordTrace_append hprefix tailTrace_879702
  have hstable : (prefixWord ++ tailWord_879702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879702).length < 2 ^ (prefixWord ++ tailWord_879702).sum := by decide
  have hdescent : baseEnd_879702 < baseStart_879702 := by decide
  rcases family_descends (prefixWord ++ tailWord_879702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879717 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_879717 : Nat := 118140960795 + 879717 * 2 ^ 59
def prefixEnd_879717 : Nat := 4983230072969 + 3 ^ 40 * 879717 * 2
def baseEnd_879717 : Nat := 301145107287626557927841

theorem tailTrace_879717 : CollatzResearch.WordTrace tailWord_879717 prefixEnd_879717 301145107287626557927841 := by
  unfold tailWord_879717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085914953943027547197405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21390609969295351698131603 32085914953943027547197405)
  ·
    refine ⟨12032218107728635330199027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32085914953943027547197405 12032218107728635330199027)
    ·
      refine ⟨18048327161592952995298541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032218107728635330199027 18048327161592952995298541)
      ·
        refine ⟨6768122685597357373236953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18048327161592952995298541 6768122685597357373236953)
        ·
          refine ⟨5076092014198018029927715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6768122685597357373236953 5076092014198018029927715)
          ·
            refine ⟨7614138021297027044891573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076092014198018029927715 7614138021297027044891573)
            ·
              refine ⟨713825439496596285458585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7614138021297027044891573 713825439496596285458585)
              ·
                refine ⟨535369079622447214093939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713825439496596285458585 535369079622447214093939)
                ·
                  refine ⟨803053619433670821140909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535369079622447214093939 803053619433670821140909)
                  ·
                    refine ⟨301145107287626557927841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803053619433670821140909 301145107287626557927841)
                    ·
                      rfl

theorem cell22_879717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_879717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879717 prefixEnd_879717 := by exact prefixLift 879717
  have htrace : WordTrace (prefixWord ++ tailWord_879717) baseStart_879717 baseEnd_879717 := by
    simpa [prefixWord, tailWord_879717, baseEnd_879717] using wordTrace_append hprefix tailTrace_879717
  have hstable : (prefixWord ++ tailWord_879717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879717).length < 2 ^ (prefixWord ++ tailWord_879717).sum := by decide
  have hdescent : baseEnd_879717 < baseStart_879717 := by decide
  rcases family_descends (prefixWord ++ tailWord_879717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879741 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 8]
def baseStart_879741 : Nat := 118140960795 + 879741 * 2 ^ 59
def prefixEnd_879741 : Nat := 4983230072969 + 3 ^ 40 * 879741 * 2
def baseEnd_879741 : Nat := 100384440992699498442589

theorem tailTrace_879741 : CollatzResearch.WordTrace tailWord_879741 prefixEnd_879741 100384440992699498442589 := by
  unfold tailWord_879741
  simp only [CollatzResearch.WordTrace]
  refine ⟨32086790305856079646071077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21391193537237386430714051 32086790305856079646071077)
  ·
    refine ⟨6016273182348014933638327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32086790305856079646071077 6016273182348014933638327)
    ·
      refine ⟨9024409773522022400457491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016273182348014933638327 9024409773522022400457491)
      ·
        refine ⟨13536614660283033600686237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024409773522022400457491 13536614660283033600686237)
        ·
          refine ⟨5076230497606137600257339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13536614660283033600686237 5076230497606137600257339)
          ·
            refine ⟨7614345746409206400386009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076230497606137600257339 7614345746409206400386009)
            ·
              refine ⟨5710759309806904800289507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614345746409206400386009 5710759309806904800289507)
              ·
                refine ⟨8566138964710357200434261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710759309806904800289507 8566138964710357200434261)
                ·
                  refine ⟨100384440992699498442589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8566138964710357200434261 100384440992699498442589)
                  ·
                    rfl

theorem cell22_879741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_879741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879741 prefixEnd_879741 := by exact prefixLift 879741
  have htrace : WordTrace (prefixWord ++ tailWord_879741) baseStart_879741 baseEnd_879741 := by
    simpa [prefixWord, tailWord_879741, baseEnd_879741] using wordTrace_append hprefix tailTrace_879741
  have hstable : (prefixWord ++ tailWord_879741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879741).length < 2 ^ (prefixWord ++ tailWord_879741).sum := by decide
  have hdescent : baseEnd_879741 < baseStart_879741 := by decide
  rcases family_descends (prefixWord ++ tailWord_879741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879912 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_879912 : Nat := 118140960795 + 879912 * 2 ^ 59
def prefixEnd_879912 : Nat := 4983230072969 + 3 ^ 40 * 879912 * 2
def baseEnd_879912 : Nat := 301211859772711049302243

theorem tailTrace_879912 : CollatzResearch.WordTrace tailWord_879912 prefixEnd_879912 301211859772711049302243 := by
  unfold tailWord_879912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16046513594118287925272995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21395351458824383900363993 16046513594118287925272995)
  ·
    refine ⟨24069770391177431887909493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16046513594118287925272995 24069770391177431887909493)
    ·
      refine ⟨2256540974172884239491515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24069770391177431887909493 2256540974172884239491515)
      ·
        refine ⟨3384811461259326359237273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256540974172884239491515 3384811461259326359237273)
        ·
          refine ⟨2538608595944494769427955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384811461259326359237273 2538608595944494769427955)
          ·
            refine ⟨3807912893916742154141933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538608595944494769427955 3807912893916742154141933)
            ·
              refine ⟨1427967335218778307803225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3807912893916742154141933 1427967335218778307803225)
              ·
                refine ⟨1070975501414083730852419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427967335218778307803225 1070975501414083730852419)
                ·
                  refine ⟨1606463252121125596278629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070975501414083730852419 1606463252121125596278629)
                  ·
                    refine ⟨301211859772711049302243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1606463252121125596278629 301211859772711049302243)
                    ·
                      rfl

theorem cell22_879912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_879912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879912 prefixEnd_879912 := by exact prefixLift 879912
  have htrace : WordTrace (prefixWord ++ tailWord_879912) baseStart_879912 baseEnd_879912 := by
    simpa [prefixWord, tailWord_879912, baseEnd_879912] using wordTrace_append hprefix tailTrace_879912
  have hstable : (prefixWord ++ tailWord_879912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879912).length < 2 ^ (prefixWord ++ tailWord_879912).sum := by decide
  have hdescent : baseEnd_879912 < baseStart_879912 := by decide
  rcases family_descends (prefixWord ++ tailWord_879912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879925 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_879925 : Nat := 118140960795 + 879925 * 2 ^ 59
def prefixEnd_879925 : Nat := 4983230072969 + 3 ^ 40 * 879925 * 2
def baseEnd_879925 : Nat := 301216309938383348727203

theorem tailTrace_879925 : CollatzResearch.WordTrace tailWord_879925 prefixEnd_879925 301216309938383348727203 := by
  unfold tailWord_879925
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093501337189479070769229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21395667558126319380512819 32093501337189479070769229)
  ·
    refine ⟨12035063001446054651538461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32093501337189479070769229 12035063001446054651538461)
    ·
      refine ⟨4513148625542270494326923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12035063001446054651538461 4513148625542270494326923)
      ·
        refine ⟨6769722938313405741490385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513148625542270494326923 6769722938313405741490385)
        ·
          refine ⟨5077292203735054306117789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6769722938313405741490385 5077292203735054306117789)
          ·
            refine ⟨1903984576400645364794171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5077292203735054306117789 1903984576400645364794171)
            ·
              refine ⟨2855976864600968047191257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903984576400645364794171 2855976864600968047191257)
              ·
                refine ⟨2141982648450726035393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855976864600968047191257 2141982648450726035393443)
                ·
                  refine ⟨3212973972676089053090165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141982648450726035393443 3212973972676089053090165)
                  ·
                    refine ⟨301216309938383348727203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3212973972676089053090165 301216309938383348727203)
                    ·
                      rfl

theorem cell22_879925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_879925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879925 prefixEnd_879925 := by exact prefixLift 879925
  have htrace : WordTrace (prefixWord ++ tailWord_879925) baseStart_879925 baseEnd_879925 := by
    simpa [prefixWord, tailWord_879925, baseEnd_879925] using wordTrace_append hprefix tailTrace_879925
  have hstable : (prefixWord ++ tailWord_879925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879925).length < 2 ^ (prefixWord ++ tailWord_879925).sum := by decide
  have hdescent : baseEnd_879925 < baseStart_879925 := by decide
  rcases family_descends (prefixWord ++ tailWord_879925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879929 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_879929 : Nat := 118140960795 + 879929 * 2 ^ 59
def prefixEnd_879929 : Nat := 4983230072969 + 3 ^ 40 * 879929 * 2
def baseEnd_879929 : Nat := 301217679220128671627191

theorem tailTrace_879929 : CollatzResearch.WordTrace tailWord_879929 prefixEnd_879929 301217679220128671627191 := by
  unfold tailWord_879929
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093647229174987753914841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21395764819449991835943227 32093647229174987753914841)
  ·
    refine ⟨24070235421881240815436131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32093647229174987753914841 24070235421881240815436131)
    ·
      refine ⟨36105353132821861223154197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24070235421881240815436131 36105353132821861223154197)
      ·
        refine ⟨1692438428101024744835353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36105353132821861223154197 1692438428101024744835353)
        ·
          refine ⟨1269328821075768558626515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692438428101024744835353 1269328821075768558626515)
          ·
            refine ⟨1903993231613652837939773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269328821075768558626515 1903993231613652837939773)
            ·
              refine ⟨713997461855119814227415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1903993231613652837939773 713997461855119814227415)
              ·
                refine ⟨1070996192782679721341123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713997461855119814227415 1070996192782679721341123)
                ·
                  refine ⟨1606494289174019582011685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070996192782679721341123 1606494289174019582011685)
                  ·
                    refine ⟨301217679220128671627191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1606494289174019582011685 301217679220128671627191)
                    ·
                      rfl

theorem cell22_879929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_879929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879929 prefixEnd_879929 := by exact prefixLift 879929
  have htrace : WordTrace (prefixWord ++ tailWord_879929) baseStart_879929 baseEnd_879929 := by
    simpa [prefixWord, tailWord_879929, baseEnd_879929] using wordTrace_append hprefix tailTrace_879929
  have hstable : (prefixWord ++ tailWord_879929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879929).length < 2 ^ (prefixWord ++ tailWord_879929).sum := by decide
  have hdescent : baseEnd_879929 < baseStart_879929 := by decide
  rcases family_descends (prefixWord ++ tailWord_879929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879983 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 7]
def baseStart_879983 : Nat := 118140960795 + 879983 * 2 ^ 59
def prefixEnd_879983 : Nat := 4983230072969 + 3 ^ 40 * 879983 * 2
def baseEnd_879983 : Nat := 100412054841230176925675

theorem tailTrace_879983 : CollatzResearch.WordTrace tailWord_879983 prefixEnd_879983 100412054841230176925675 := by
  unfold tailWord_879983
  simp only [CollatzResearch.WordTrace]
  refine ⟨32095616770979354976380603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21397077847319569984253735 32095616770979354976380603)
  ·
    refine ⟨48143425156469032464570905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32095616770979354976380603 48143425156469032464570905)
    ·
      refine ⟨36107568867351774348428179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48143425156469032464570905 36107568867351774348428179)
      ·
        refine ⟨54161353301027661522642269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36107568867351774348428179 54161353301027661522642269)
        ·
          refine ⟨20310507487885373070990851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54161353301027661522642269 20310507487885373070990851)
          ·
            refine ⟨30465761231828059606486277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20310507487885373070990851 30465761231828059606486277)
            ·
              refine ⟨5712330230967761176216177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30465761231828059606486277 5712330230967761176216177)
              ·
                refine ⟨4284247673225820882162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5712330230967761176216177 4284247673225820882162133)
                ·
                  refine ⟨100412054841230176925675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4284247673225820882162133 100412054841230176925675)
                  ·
                    rfl

theorem cell22_879983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_879983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_879983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_879983 prefixEnd_879983 := by exact prefixLift 879983
  have htrace : WordTrace (prefixWord ++ tailWord_879983) baseStart_879983 baseEnd_879983 := by
    simpa [prefixWord, tailWord_879983, baseEnd_879983] using wordTrace_append hprefix tailTrace_879983
  have hstable : (prefixWord ++ tailWord_879983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879983).length < 2 ^ (prefixWord ++ tailWord_879983).sum := by decide
  have hdescent : baseEnd_879983 < baseStart_879983 := by decide
  rcases family_descends (prefixWord ++ tailWord_879983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880004 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_880004 : Nat := 118140960795 + 880004 * 2 ^ 59
def prefixEnd_880004 : Nat := 4983230072969 + 3 ^ 40 * 880004 * 2
def baseEnd_880004 : Nat := 301243353252853476001961

theorem tailTrace_880004 : CollatzResearch.WordTrace tailWord_880004 prefixEnd_880004 301243353252853476001961 := by
  unfold tailWord_880004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048191351951637781447533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21397588469268850375263377 16048191351951637781447533)
  ·
    refine ⟨6018071756981864168042825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16048191351951637781447533 6018071756981864168042825)
    ·
      refine ⟨4513553817736398126032119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6018071756981864168042825 4513553817736398126032119)
      ·
        refine ⟨6770330726604597189048179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513553817736398126032119 6770330726604597189048179)
        ·
          refine ⟨10155496089906895783572269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770330726604597189048179 10155496089906895783572269)
          ·
            refine ⟨3808311033715085918839601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10155496089906895783572269 3808311033715085918839601)
            ·
              refine ⟨2856233275286314439129701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808311033715085918839601 2856233275286314439129701)
              ·
                refine ⟨535543739116183957336819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2856233275286314439129701 535543739116183957336819)
                ·
                  refine ⟨803315608674275936005229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535543739116183957336819 803315608674275936005229)
                  ·
                    refine ⟨301243353252853476001961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803315608674275936005229 301243353252853476001961)
                    ·
                      rfl

theorem cell22_880004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_880004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880004 prefixEnd_880004 := by exact prefixLift 880004
  have htrace : WordTrace (prefixWord ++ tailWord_880004) baseStart_880004 baseEnd_880004 := by
    simpa [prefixWord, tailWord_880004, baseEnd_880004] using wordTrace_append hprefix tailTrace_880004
  have hstable : (prefixWord ++ tailWord_880004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880004).length < 2 ^ (prefixWord ++ tailWord_880004).sum := by decide
  have hdescent : baseEnd_880004 < baseStart_880004 := by decide
  rcases family_descends (prefixWord ++ tailWord_880004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880090 : List Nat := [3, 1, 1, 2, 3, 2, 2, 8]
def baseStart_880090 : Nat := 118140960795 + 880090 * 2 ^ 59
def prefixEnd_880090 : Nat := 4983230072969 + 3 ^ 40 * 880090 * 2
def baseEnd_880090 : Nat := 33474754756708657594633

theorem tailTrace_880090 : CollatzResearch.WordTrace tailWord_880090 prefixEnd_880090 33474754756708657594633 := by
  unfold tailWord_880090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024879845397928062631431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21399679587727808167017149 8024879845397928062631431)
  ·
    refine ⟨12037319768096892093947147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024879845397928062631431 12037319768096892093947147)
    ·
      refine ⟨18055979652145338140920721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12037319768096892093947147 18055979652145338140920721)
      ·
        refine ⟨13541984739109003605690541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18055979652145338140920721 13541984739109003605690541)
        ·
          refine ⟨5078244277165876352133953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13541984739109003605690541 5078244277165876352133953)
          ·
            refine ⟨3808683207874407264100465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5078244277165876352133953 3808683207874407264100465)
            ·
              refine ⟨2856512405905805448075349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808683207874407264100465 2856512405905805448075349)
              ·
                refine ⟨33474754756708657594633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2856512405905805448075349 33474754756708657594633)
                ·
                  rfl

theorem cell22_880090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_880090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880090 prefixEnd_880090 := by exact prefixLift 880090
  have htrace : WordTrace (prefixWord ++ tailWord_880090) baseStart_880090 baseEnd_880090 := by
    simpa [prefixWord, tailWord_880090, baseEnd_880090] using wordTrace_append hprefix tailTrace_880090
  have hstable : (prefixWord ++ tailWord_880090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880090).length < 2 ^ (prefixWord ++ tailWord_880090).sum := by decide
  have hdescent : baseEnd_880090 < baseStart_880090 := by decide
  rcases family_descends (prefixWord ++ tailWord_880090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880120 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_880120 : Nat := 118140960795 + 880120 * 2 ^ 59
def prefixEnd_880120 : Nat := 4983230072969 + 3 ^ 40 * 880120 * 2
def baseEnd_880120 : Nat := 301283062423467840101605

theorem tailTrace_880120 : CollatzResearch.WordTrace tailWord_880120 prefixEnd_880120 301283062423467840101605 := by
  unfold tailWord_880120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050306785741513687058907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21400409047655351582745209 16050306785741513687058907)
  ·
    refine ⟨24075460178612270530588361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16050306785741513687058907 24075460178612270530588361)
    ·
      refine ⟨18056595133959202897941271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24075460178612270530588361 18056595133959202897941271)
      ·
        refine ⟨27084892700938804346911907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18056595133959202897941271 27084892700938804346911907)
        ·
          refine ⟨40627339051408206520367861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27084892700938804346911907 40627339051408206520367861)
          ·
            refine ⟨3808813036069519361284487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40627339051408206520367861 3808813036069519361284487)
            ·
              refine ⟨5713219554104279041926731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808813036069519361284487 5713219554104279041926731)
              ·
                refine ⟨8569829331156418562890097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713219554104279041926731 8569829331156418562890097)
                ·
                  refine ⟨6427371998367313922167573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569829331156418562890097 6427371998367313922167573)
                  ·
                    refine ⟨301283062423467840101605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6427371998367313922167573 301283062423467840101605)
                    ·
                      rfl

theorem cell22_880120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_880120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880120 prefixEnd_880120 := by exact prefixLift 880120
  have htrace : WordTrace (prefixWord ++ tailWord_880120) baseStart_880120 baseEnd_880120 := by
    simpa [prefixWord, tailWord_880120, baseEnd_880120] using wordTrace_append hprefix tailTrace_880120
  have hstable : (prefixWord ++ tailWord_880120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880120).length < 2 ^ (prefixWord ++ tailWord_880120).sum := by decide
  have hdescent : baseEnd_880120 < baseStart_880120 := by decide
  rcases family_descends (prefixWord ++ tailWord_880120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880122 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_880122 : Nat := 118140960795 + 880122 * 2 ^ 59
def prefixEnd_880122 : Nat := 4983230072969 + 3 ^ 40 * 880122 * 2
def baseEnd_880122 : Nat := 301283747064340501551599

theorem tailTrace_880122 : CollatzResearch.WordTrace tailWord_880122 prefixEnd_880122 301283747064340501551599 := by
  unfold tailWord_880122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025171629368945428922655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21400457678317187810460413 8025171629368945428922655)
  ·
    refine ⟨12037757444053418143383983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8025171629368945428922655 12037757444053418143383983)
    ·
      refine ⟨18056636166080127215075975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12037757444053418143383983 18056636166080127215075975)
      ·
        refine ⟨27084954249120190822613963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18056636166080127215075975 27084954249120190822613963)
        ·
          refine ⟨40627431373680286233920945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27084954249120190822613963 40627431373680286233920945)
          ·
            refine ⟨30470573530260214675440709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40627431373680286233920945 30470573530260214675440709)
            ·
              refine ⟨5713232536923790251645133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30470573530260214675440709 5713232536923790251645133)
              ·
                refine ⟨2142462201346421344366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5713232536923790251645133 2142462201346421344366925)
                ·
                  refine ⟨803423325504908004137597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142462201346421344366925 803423325504908004137597)
                  ·
                    refine ⟨301283747064340501551599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803423325504908004137597 301283747064340501551599)
                    ·
                      rfl

theorem cell22_880122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_880122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880122 prefixEnd_880122 := by exact prefixLift 880122
  have htrace : WordTrace (prefixWord ++ tailWord_880122) baseStart_880122 baseEnd_880122 := by
    simpa [prefixWord, tailWord_880122, baseEnd_880122] using wordTrace_append hprefix tailTrace_880122
  have hstable : (prefixWord ++ tailWord_880122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880122).length < 2 ^ (prefixWord ++ tailWord_880122).sum := by decide
  have hdescent : baseEnd_880122 < baseStart_880122 := by decide
  rcases family_descends (prefixWord ++ tailWord_880122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880139 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 3, 3]
def baseStart_880139 : Nat := 118140960795 + 880139 * 2 ^ 59
def prefixEnd_880139 : Nat := 4983230072969 + 3 ^ 40 * 880139 * 2
def baseEnd_880139 : Nat := 301289566511758123876547

theorem tailTrace_880139 : CollatzResearch.WordTrace tailWord_880139 prefixEnd_880139 301289566511758123876547 := by
  unfold tailWord_880139
  simp only [CollatzResearch.WordTrace]
  refine ⟨32101306558414193619059471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21400871038942795746039647 32101306558414193619059471)
  ·
    refine ⟨48151959837621290428589207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32101306558414193619059471 48151959837621290428589207)
    ·
      refine ⟨72227939756431935642883811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48151959837621290428589207 72227939756431935642883811)
      ·
        refine ⟨108341909634647903464325717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72227939756431935642883811 108341909634647903464325717)
        ·
          refine ⟨1269631753531030118722567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 108341909634647903464325717 1269631753531030118722567)
          ·
            refine ⟨1904447630296545178083851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269631753531030118722567 1904447630296545178083851)
            ·
              refine ⟨2856671445444817767125777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904447630296545178083851 2856671445444817767125777)
              ·
                refine ⟨2142503584083613325344333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856671445444817767125777 2142503584083613325344333)
                ·
                  refine ⟨803438844031354997004125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142503584083613325344333 803438844031354997004125)
                  ·
                    refine ⟨301289566511758123876547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803438844031354997004125 301289566511758123876547)
                    ·
                      rfl

theorem cell22_880139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3].length) (baseStart_880139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880139 prefixEnd_880139 := by exact prefixLift 880139
  have htrace : WordTrace (prefixWord ++ tailWord_880139) baseStart_880139 baseEnd_880139 := by
    simpa [prefixWord, tailWord_880139, baseEnd_880139] using wordTrace_append hprefix tailTrace_880139
  have hstable : (prefixWord ++ tailWord_880139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880139).length < 2 ^ (prefixWord ++ tailWord_880139).sum := by decide
  have hdescent : baseEnd_880139 < baseStart_880139 := by decide
  rcases family_descends (prefixWord ++ tailWord_880139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880156 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_880156 : Nat := 118140960795 + 880156 * 2 ^ 59
def prefixEnd_880156 : Nat := 4983230072969 + 3 ^ 40 * 880156 * 2
def baseEnd_880156 : Nat := 301295385959175746201495

theorem tailTrace_880156 : CollatzResearch.WordTrace tailWord_880156 prefixEnd_880156 301295385959175746201495 := by
  unfold tailWord_880156
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050963299676302761214161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21401284399568403681618881 16050963299676302761214161)
  ·
    refine ⟨12038222474757227070910621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16050963299676302761214161 12038222474757227070910621)
    ·
      refine ⟨4514333428033960151591483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12038222474757227070910621 4514333428033960151591483)
      ·
        refine ⟨6771500142050940227387225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514333428033960151591483 6771500142050940227387225)
        ·
          refine ⟨5078625106538205170540419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6771500142050940227387225 5078625106538205170540419)
          ·
            refine ⟨7617937659807307755810629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078625106538205170540419 7617937659807307755810629)
            ·
              refine ⟨1428363311213870204214493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7617937659807307755810629 1428363311213870204214493)
              ·
                refine ⟨535636241705201326580435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1428363311213870204214493 535636241705201326580435)
                ·
                  refine ⟨803454362557801989870653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535636241705201326580435 803454362557801989870653)
                  ·
                    refine ⟨301295385959175746201495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803454362557801989870653 301295385959175746201495)
                    ·
                      rfl

theorem cell22_880156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_880156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880156 prefixEnd_880156 := by exact prefixLift 880156
  have htrace : WordTrace (prefixWord ++ tailWord_880156) baseStart_880156 baseEnd_880156 := by
    simpa [prefixWord, tailWord_880156, baseEnd_880156] using wordTrace_append hprefix tailTrace_880156
  have hstable : (prefixWord ++ tailWord_880156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880156).length < 2 ^ (prefixWord ++ tailWord_880156).sum := by decide
  have hdescent : baseEnd_880156 < baseStart_880156 := by decide
  rcases family_descends (prefixWord ++ tailWord_880156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880212 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_880212 : Nat := 118140960795 + 880212 * 2 ^ 59
def prefixEnd_880212 : Nat := 4983230072969 + 3 ^ 40 * 880212 * 2
def baseEnd_880212 : Nat := 301314555903610266801323

theorem tailTrace_880212 : CollatzResearch.WordTrace tailWord_880212 prefixEnd_880212 301314555903610266801323 := by
  unfold tailWord_880212
  simp only [CollatzResearch.WordTrace]
  refine ⟨16051984543574863543233445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21402646058099818057644593 16051984543574863543233445)
  ·
    refine ⟨3009747101920286914356271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16051984543574863543233445 3009747101920286914356271)
    ·
      refine ⟨4514620652880430371534407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009747101920286914356271 4514620652880430371534407)
      ·
        refine ⟨6771930979320645557301611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514620652880430371534407 6771930979320645557301611)
        ·
          refine ⟨10157896468980968335952417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771930979320645557301611 10157896468980968335952417)
          ·
            refine ⟨7618422351735726251964313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10157896468980968335952417 7618422351735726251964313)
            ·
              refine ⟨5713816763801794688973235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7618422351735726251964313 5713816763801794688973235)
              ·
                refine ⟨8570725145702692033459853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713816763801794688973235 8570725145702692033459853)
                ·
                  refine ⟨3214021929638509512547445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8570725145702692033459853 3214021929638509512547445)
                  ·
                    refine ⟨301314555903610266801323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3214021929638509512547445 301314555903610266801323)
                    ·
                      rfl

theorem cell22_880212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_880212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880212 prefixEnd_880212 := by exact prefixLift 880212
  have htrace : WordTrace (prefixWord ++ tailWord_880212) baseStart_880212 baseEnd_880212 := by
    simpa [prefixWord, tailWord_880212, baseEnd_880212] using wordTrace_append hprefix tailTrace_880212
  have hstable : (prefixWord ++ tailWord_880212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880212).length < 2 ^ (prefixWord ++ tailWord_880212).sum := by decide
  have hdescent : baseEnd_880212 < baseStart_880212 := by decide
  rcases family_descends (prefixWord ++ tailWord_880212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880227 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_880227 : Nat := 118140960795 + 880227 * 2 ^ 59
def prefixEnd_880227 : Nat := 4983230072969 + 3 ^ 40 * 880227 * 2
def baseEnd_880227 : Nat := 301319690710155227676277

theorem tailTrace_880227 : CollatzResearch.WordTrace tailWord_880227 prefixEnd_880227 301319690710155227676277 := by
  unfold tailWord_880227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104516182095384648262935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21403010788063589765508623 32104516182095384648262935)
  ·
    refine ⟨48156774273143076972394403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32104516182095384648262935 48156774273143076972394403)
    ·
      refine ⟨72235161409714615458591605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48156774273143076972394403 72235161409714615458591605)
      ·
        refine ⟨6772046382160745199242963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72235161409714615458591605 6772046382160745199242963)
        ·
          refine ⟨10158069573241117798864445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772046382160745199242963 10158069573241117798864445)
          ·
            refine ⟨3809276089965419174574167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10158069573241117798864445 3809276089965419174574167)
            ·
              refine ⟨5713914134948128761861251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809276089965419174574167 5713914134948128761861251)
              ·
                refine ⟨8570871202422193142791877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713914134948128761861251 8570871202422193142791877)
                ·
                  refine ⟨1607038350454161214273477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8570871202422193142791877 1607038350454161214273477)
                  ·
                    refine ⟨301319690710155227676277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1607038350454161214273477 301319690710155227676277)
                    ·
                      rfl

theorem cell22_880227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_880227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880227 prefixEnd_880227 := by exact prefixLift 880227
  have htrace : WordTrace (prefixWord ++ tailWord_880227) baseStart_880227 baseEnd_880227 := by
    simpa [prefixWord, tailWord_880227, baseEnd_880227] using wordTrace_append hprefix tailTrace_880227
  have hstable : (prefixWord ++ tailWord_880227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880227).length < 2 ^ (prefixWord ++ tailWord_880227).sum := by decide
  have hdescent : baseEnd_880227 < baseStart_880227 := by decide
  rcases family_descends (prefixWord ++ tailWord_880227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880229 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_880229 : Nat := 118140960795 + 880229 * 2 ^ 59
def prefixEnd_880229 : Nat := 4983230072969 + 3 ^ 40 * 880229 * 2
def baseEnd_880229 : Nat := 301320375351027889126271

theorem tailTrace_880229 : CollatzResearch.WordTrace tailWord_880229 prefixEnd_880229 301320375351027889126271 := by
  unfold tailWord_880229
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104589128088138989835741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21403059418725425993223827 32104589128088138989835741)
  ·
    refine ⟨12039220923033052121188403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32104589128088138989835741 12039220923033052121188403)
    ·
      refine ⟨18058831384549578181782605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039220923033052121188403 18058831384549578181782605)
      ·
        refine ⟨6772061769206091818168477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18058831384549578181782605 6772061769206091818168477)
        ·
          refine ⟨2539523163452284431813179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6772061769206091818168477 2539523163452284431813179)
          ·
            refine ⟨3809284745178426647719769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539523163452284431813179 3809284745178426647719769)
            ·
              refine ⟨2856963558883819985789827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809284745178426647719769 2856963558883819985789827)
              ·
                refine ⟨4285445338325729978684741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856963558883819985789827 4285445338325729978684741)
                ·
                  refine ⟨803521000936074371003389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4285445338325729978684741 803521000936074371003389)
                  ·
                    refine ⟨301320375351027889126271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803521000936074371003389 301320375351027889126271)
                    ·
                      rfl

theorem cell22_880229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_880229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880229 prefixEnd_880229 := by exact prefixLift 880229
  have htrace : WordTrace (prefixWord ++ tailWord_880229) baseStart_880229 baseEnd_880229 := by
    simpa [prefixWord, tailWord_880229, baseEnd_880229] using wordTrace_append hprefix tailTrace_880229
  have hstable : (prefixWord ++ tailWord_880229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880229).length < 2 ^ (prefixWord ++ tailWord_880229).sum := by decide
  have hdescent : baseEnd_880229 < baseStart_880229 := by decide
  rcases family_descends (prefixWord ++ tailWord_880229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880242 : List Nat := [3, 2, 1, 2, 3, 1, 1, 9]
def baseStart_880242 : Nat := 118140960795 + 880242 * 2 ^ 59
def prefixEnd_880242 : Nat := 4983230072969 + 3 ^ 40 * 880242 * 2
def baseEnd_880242 : Nat := 33480536168522243172359

theorem tailTrace_880242 : CollatzResearch.WordTrace tailWord_880242 prefixEnd_880242 33480536168522243172359 := by
  unfold tailWord_880242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026265819260260552514745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21403375518027361473372653 8026265819260260552514745)
  ·
    refine ⟨6019699364445195414386059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8026265819260260552514745 6019699364445195414386059)
    ·
      refine ⟨9029549046667793121579089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019699364445195414386059 9029549046667793121579089)
      ·
        refine ⟨6772161785000844841184317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9029549046667793121579089 6772161785000844841184317)
        ·
          refine ⟨2539560669375316815444119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6772161785000844841184317 2539560669375316815444119)
          ·
            refine ⟨3809341004062975223166179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539560669375316815444119 3809341004062975223166179)
            ·
              refine ⟨5714011506094462834749269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809341004062975223166179 5714011506094462834749269)
              ·
                refine ⟨33480536168522243172359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5714011506094462834749269 33480536168522243172359)
                ·
                  rfl

theorem cell22_880242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_880242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880242 prefixEnd_880242 := by exact prefixLift 880242
  have htrace : WordTrace (prefixWord ++ tailWord_880242) baseStart_880242 baseEnd_880242 := by
    simpa [prefixWord, tailWord_880242, baseEnd_880242] using wordTrace_append hprefix tailTrace_880242
  have hstable : (prefixWord ++ tailWord_880242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880242).length < 2 ^ (prefixWord ++ tailWord_880242).sum := by decide
  have hdescent : baseEnd_880242 < baseStart_880242 := by decide
  rcases family_descends (prefixWord ++ tailWord_880242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880291 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 1, 3]
def baseStart_880291 : Nat := 118140960795 + 880291 * 2 ^ 59
def prefixEnd_880291 : Nat := 4983230072969 + 3 ^ 40 * 880291 * 2
def baseEnd_880291 : Nat := 301341599218080394076081

theorem tailTrace_880291 : CollatzResearch.WordTrace tailWord_880291 prefixEnd_880291 301341599218080394076081 := by
  unfold tailWord_880291
  simp only [CollatzResearch.WordTrace]
  refine ⟨32106850453863523578592727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21404566969242349052395151 32106850453863523578592727)
  ·
    refine ⟨48160275680795285367889091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32106850453863523578592727 48160275680795285367889091)
    ·
      refine ⟨72240413521192928051833637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48160275680795285367889091 72240413521192928051833637)
      ·
        refine ⟨13545077535223674009718807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72240413521192928051833637 13545077535223674009718807)
        ·
          refine ⟨20317616302835511014578211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13545077535223674009718807 20317616302835511014578211)
          ·
            refine ⟨30476424454253266521867317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20317616302835511014578211 30476424454253266521867317)
            ·
              refine ⟨2857164792586243736425061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30476424454253266521867317 2857164792586243736425061)
              ·
                refine ⟨535718398609920700579699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2857164792586243736425061 535718398609920700579699)
                ·
                  refine ⟨803577597914881050869549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535718398609920700579699 803577597914881050869549)
                  ·
                    refine ⟨301341599218080394076081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803577597914881050869549 301341599218080394076081)
                    ·
                      rfl

theorem cell22_880291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 3].length) (baseStart_880291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880291 prefixEnd_880291 := by exact prefixLift 880291
  have htrace : WordTrace (prefixWord ++ tailWord_880291) baseStart_880291 baseEnd_880291 := by
    simpa [prefixWord, tailWord_880291, baseEnd_880291] using wordTrace_append hprefix tailTrace_880291
  have hstable : (prefixWord ++ tailWord_880291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880291).length < 2 ^ (prefixWord ++ tailWord_880291).sum := by decide
  have hdescent : baseEnd_880291 < baseStart_880291 := by decide
  rcases family_descends (prefixWord ++ tailWord_880291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880364 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_880364 : Nat := 118140960795 + 880364 * 2 ^ 59
def prefixEnd_880364 : Nat := 4983230072969 + 3 ^ 40 * 880364 * 2
def baseEnd_880364 : Nat := 301366588609932537000857

theorem tailTrace_880364 : CollatzResearch.WordTrace tailWord_880364 prefixEnd_880364 301366588609932537000857 := by
  unfold tailWord_880364
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054756491299528523000073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21406341988399371364000097 16054756491299528523000073)
  ·
    refine ⟨12041067368474646392250055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16054756491299528523000073 12041067368474646392250055)
    ·
      refine ⟨18061601052711969588375083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041067368474646392250055 18061601052711969588375083)
      ·
        refine ⟨27092401579067954382562625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18061601052711969588375083 27092401579067954382562625)
        ·
          refine ⟨20319301184300965786921969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27092401579067954382562625 20319301184300965786921969)
          ·
            refine ⟨15239475888225724340191477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20319301184300965786921969 15239475888225724340191477)
            ·
              refine ⟨1428700864521161656892951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15239475888225724340191477 1428700864521161656892951)
              ·
                refine ⟨2143051296781742485339427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428700864521161656892951 2143051296781742485339427)
                ·
                  refine ⟨3214576945172613728009141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143051296781742485339427 3214576945172613728009141)
                  ·
                    refine ⟨301366588609932537000857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3214576945172613728009141 301366588609932537000857)
                    ·
                      rfl

theorem cell22_880364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_880364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880364 prefixEnd_880364 := by exact prefixLift 880364
  have htrace : WordTrace (prefixWord ++ tailWord_880364) baseStart_880364 baseEnd_880364 := by
    simpa [prefixWord, tailWord_880364, baseEnd_880364] using wordTrace_append hprefix tailTrace_880364
  have hstable : (prefixWord ++ tailWord_880364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880364).length < 2 ^ (prefixWord ++ tailWord_880364).sum := by decide
  have hdescent : baseEnd_880364 < baseStart_880364 := by decide
  rcases family_descends (prefixWord ++ tailWord_880364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880394 : List Nat := [3, 1, 2, 2, 1, 5, 8]
def baseStart_880394 : Nat := 118140960795 + 880394 * 2 ^ 59
def prefixEnd_880394 : Nat := 4983230072969 + 3 ^ 40 * 880394 * 2
def baseEnd_880394 : Nat := 11162105860111942916695

theorem tailTrace_880394 : CollatzResearch.WordTrace tailWord_880394 prefixEnd_880394 11162105860111942916695 := by
  unfold tailWord_880394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027651793122593042398059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21407071448326914779728157 8027651793122593042398059)
  ·
    refine ⟨12041477689683889563597089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8027651793122593042398059 12041477689683889563597089)
    ·
      refine ⟨9031108267262917172697817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12041477689683889563597089 9031108267262917172697817)
      ·
        refine ⟨6773331200447187879523363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9031108267262917172697817 6773331200447187879523363)
        ·
          refine ⟨10159996800670781819285045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773331200447187879523363 10159996800670781819285045)
          ·
            refine ⟨952499700062885795557973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10159996800670781819285045 952499700062885795557973)
            ·
              refine ⟨11162105860111942916695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 952499700062885795557973 11162105860111942916695)
              ·
                rfl

theorem cell22_880394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 8].length) (baseStart_880394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880394 prefixEnd_880394 := by exact prefixLift 880394
  have htrace : WordTrace (prefixWord ++ tailWord_880394) baseStart_880394 baseEnd_880394 := by
    simpa [prefixWord, tailWord_880394, baseEnd_880394] using wordTrace_append hprefix tailTrace_880394
  have hstable : (prefixWord ++ tailWord_880394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880394).length < 2 ^ (prefixWord ++ tailWord_880394).sum := by decide
  have hdescent : baseEnd_880394 < baseStart_880394 := by decide
  rcases family_descends (prefixWord ++ tailWord_880394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880456 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_880456 : Nat := 118140960795 + 880456 * 2 ^ 59
def prefixEnd_880456 : Nat := 4983230072969 + 3 ^ 40 * 880456 * 2
def baseEnd_880456 : Nat := 100466027363358321233525

theorem tailTrace_880456 : CollatzResearch.WordTrace tailWord_880456 prefixEnd_880456 100466027363358321233525 := by
  unfold tailWord_880456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056434249132878379174611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21408578998843837838899481 16056434249132878379174611)
  ·
    refine ⟨24084651373699317568761917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16056434249132878379174611 24084651373699317568761917)
    ·
      refine ⟨9031744265137244088285719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24084651373699317568761917 9031744265137244088285719)
      ·
        refine ⟨13547616397705866132428579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031744265137244088285719 13547616397705866132428579)
        ·
          refine ⟨20321424596558799198642869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13547616397705866132428579 20321424596558799198642869)
          ·
            refine ⟨1905133555927387424872769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20321424596558799198642869 1905133555927387424872769)
            ·
              refine ⟨1428850166945540568654577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905133555927387424872769 1428850166945540568654577)
              ·
                refine ⟨1071637625209155426490933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428850166945540568654577 1071637625209155426490933)
                ·
                  refine ⟨100466027363358321233525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071637625209155426490933 100466027363358321233525)
                  ·
                    rfl

theorem cell22_880456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_880456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880456 prefixEnd_880456 := by exact prefixLift 880456
  have htrace : WordTrace (prefixWord ++ tailWord_880456) baseStart_880456 baseEnd_880456 := by
    simpa [prefixWord, tailWord_880456, baseEnd_880456] using wordTrace_append hprefix tailTrace_880456
  have hstable : (prefixWord ++ tailWord_880456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880456).length < 2 ^ (prefixWord ++ tailWord_880456).sum := by decide
  have hdescent : baseEnd_880456 < baseStart_880456 := by decide
  rcases family_descends (prefixWord ++ tailWord_880456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880460 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_880460 : Nat := 118140960795 + 880460 * 2 ^ 59
def prefixEnd_880460 : Nat := 4983230072969 + 3 ^ 40 * 880460 * 2
def baseEnd_880460 : Nat := 301399451371820286600563

theorem tailTrace_880460 : CollatzResearch.WordTrace tailWord_880460 prefixEnd_880460 301399451371820286600563 := by
  unfold tailWord_880460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056507195125632720747417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21408676260167510294329889 16056507195125632720747417)
  ·
    refine ⟨12042380396344224540560563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16056507195125632720747417 12042380396344224540560563)
    ·
      refine ⟨18063570594516336810840845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12042380396344224540560563 18063570594516336810840845)
      ·
        refine ⟨6773838972943626304065317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18063570594516336810840845 6773838972943626304065317)
        ·
          refine ⟨1270094807426929932012247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6773838972943626304065317 1270094807426929932012247)
          ·
            refine ⟨1905142211140394898018371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270094807426929932012247 1905142211140394898018371)
            ·
              refine ⟨2857713316710592347027557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905142211140394898018371 2857713316710592347027557)
              ·
                refine ⟨535821246883236065067667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2857713316710592347027557 535821246883236065067667)
                ·
                  refine ⟨803731870324854097601501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535821246883236065067667 803731870324854097601501)
                  ·
                    refine ⟨301399451371820286600563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803731870324854097601501 301399451371820286600563)
                    ·
                      rfl

theorem cell22_880460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_880460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880460 prefixEnd_880460 := by exact prefixLift 880460
  have htrace : WordTrace (prefixWord ++ tailWord_880460) baseStart_880460 baseEnd_880460 := by
    simpa [prefixWord, tailWord_880460, baseEnd_880460] using wordTrace_append hprefix tailTrace_880460
  have hstable : (prefixWord ++ tailWord_880460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880460).length < 2 ^ (prefixWord ++ tailWord_880460).sum := by decide
  have hdescent : baseEnd_880460 < baseStart_880460 := by decide
  rcases family_descends (prefixWord ++ tailWord_880460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880471 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 2, 5]
def baseStart_880471 : Nat := 118140960795 + 880471 * 2 ^ 59
def prefixEnd_880471 : Nat := 4983230072969 + 3 ^ 40 * 880471 * 2
def baseEnd_880471 : Nat := 301403216896619924575529

theorem tailTrace_880471 : CollatzResearch.WordTrace tailWord_880471 prefixEnd_880471 301403216896619924575529 := by
  unfold tailWord_880471
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113415593211414320145267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21408943728807609546763511 32113415593211414320145267)
  ·
    refine ⟨48170123389817121480217901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32113415593211414320145267 48170123389817121480217901)
    ·
      refine ⟨18063796271181420555081713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48170123389817121480217901 18063796271181420555081713)
      ·
        refine ⟨13547847203386065416311285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18063796271181420555081713 13547847203386065416311285)
        ·
          refine ⟨1270110675317443632779183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13547847203386065416311285 1270110675317443632779183)
          ·
            refine ⟨1905166012976165449168775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270110675317443632779183 1905166012976165449168775)
            ·
              refine ⟨2857749019464248173753163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905166012976165449168775 2857749019464248173753163)
              ·
                refine ⟨4286623529196372260629745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857749019464248173753163 4286623529196372260629745)
                ·
                  refine ⟨3214967646897279195472309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286623529196372260629745 3214967646897279195472309)
                  ·
                    refine ⟨301403216896619924575529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3214967646897279195472309 301403216896619924575529)
                    ·
                      rfl

theorem cell22_880471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_880471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880471 prefixEnd_880471 := by exact prefixLift 880471
  have htrace : WordTrace (prefixWord ++ tailWord_880471) baseStart_880471 baseEnd_880471 := by
    simpa [prefixWord, tailWord_880471, baseEnd_880471] using wordTrace_append hprefix tailTrace_880471
  have hstable : (prefixWord ++ tailWord_880471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880471).length < 2 ^ (prefixWord ++ tailWord_880471).sum := by decide
  have hdescent : baseEnd_880471 < baseStart_880471 := by decide
  rcases family_descends (prefixWord ++ tailWord_880471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880544 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_880544 : Nat := 118140960795 + 880544 * 2 ^ 59
def prefixEnd_880544 : Nat := 4983230072969 + 3 ^ 40 * 880544 * 2
def baseEnd_880544 : Nat := 301428206288472067500305

theorem tailTrace_880544 : CollatzResearch.WordTrace tailWord_880544 prefixEnd_880544 301428206288472067500305 := by
  unfold tailWord_880544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058039060973473893776343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21410718747964631858368457 16058039060973473893776343)
  ·
    refine ⟨24087058591460210840664515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058039060973473893776343 24087058591460210840664515)
    ·
      refine ⟨36130587887190316260996773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24087058591460210840664515 36130587887190316260996773)
      ·
        refine ⟨6774485228848184298936895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36130587887190316260996773 6774485228848184298936895)
        ·
          refine ⟨10161727843272276448405343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774485228848184298936895 10161727843272276448405343)
          ·
            refine ⟨15242591764908414672608015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10161727843272276448405343 15242591764908414672608015)
            ·
              refine ⟨22863887647362622008912023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15242591764908414672608015 22863887647362622008912023)
              ·
                refine ⟨34295831471043933013368035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22863887647362622008912023 34295831471043933013368035)
                ·
                  refine ⟨51443747206565899520052053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34295831471043933013368035 51443747206565899520052053)
                  ·
                    refine ⟨301428206288472067500305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 51443747206565899520052053 301428206288472067500305)
                    ·
                      rfl

theorem cell22_880544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_880544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880544 prefixEnd_880544 := by exact prefixLift 880544
  have htrace : WordTrace (prefixWord ++ tailWord_880544) baseStart_880544 baseEnd_880544 := by
    simpa [prefixWord, tailWord_880544, baseEnd_880544] using wordTrace_append hprefix tailTrace_880544
  have hstable : (prefixWord ++ tailWord_880544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880544).length < 2 ^ (prefixWord ++ tailWord_880544).sum := by decide
  have hdescent : baseEnd_880544 < baseStart_880544 := by decide
  rcases family_descends (prefixWord ++ tailWord_880544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880591 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 5]
def baseStart_880591 : Nat := 118140960795 + 880591 * 2 ^ 59
def prefixEnd_880591 : Nat := 4983230072969 + 3 ^ 40 * 880591 * 2
def baseEnd_880591 : Nat := 100481431782993203858387

theorem tailTrace_880591 : CollatzResearch.WordTrace tailWord_880591 prefixEnd_880591 100481431782993203858387 := by
  unfold tailWord_880591
  simp only [CollatzResearch.WordTrace]
  refine ⟨32117792352776674814513627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21411861568517783209675751 32117792352776674814513627)
  ·
    refine ⟨48176688529165012221770441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32117792352776674814513627 48176688529165012221770441)
    ·
      refine ⟨36132516396873759166327831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48176688529165012221770441 36132516396873759166327831)
      ·
        refine ⟨54198774595310638749491747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36132516396873759166327831 54198774595310638749491747)
        ·
          refine ⟨81298161892965958124237621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54198774595310638749491747 81298161892965958124237621)
          ·
            refine ⟨7621702677465558574147277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81298161892965958124237621 7621702677465558574147277)
            ·
              refine ⟨2858138504049584465305229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7621702677465558574147277 2858138504049584465305229)
              ·
                refine ⟨1071801939018594174489461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2858138504049584465305229 1071801939018594174489461)
                ·
                  refine ⟨100481431782993203858387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071801939018594174489461 100481431782993203858387)
                  ·
                    rfl

theorem cell22_880591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 5].length) (baseStart_880591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880591 prefixEnd_880591 := by exact prefixLift 880591
  have htrace : WordTrace (prefixWord ++ tailWord_880591) baseStart_880591 baseEnd_880591 := by
    simpa [prefixWord, tailWord_880591, baseEnd_880591] using wordTrace_append hprefix tailTrace_880591
  have hstable : (prefixWord ++ tailWord_880591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880591).length < 2 ^ (prefixWord ++ tailWord_880591).sum := by decide
  have hdescent : baseEnd_880591 < baseStart_880591 := by decide
  rcases family_descends (prefixWord ++ tailWord_880591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880636 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_880636 : Nat := 118140960795 + 880636 * 2 ^ 59
def prefixEnd_880636 : Nat := 4983230072969 + 3 ^ 40 * 880636 * 2
def baseEnd_880636 : Nat := 100486566589538164733341

theorem tailTrace_880636 : CollatzResearch.WordTrace tailWord_880636 prefixEnd_880636 100486566589538164733341 := by
  unfold tailWord_880636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059716818806823749950881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21412955758409098333267841 16059716818806823749950881)
  ·
    refine ⟨12044787614105117812463161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16059716818806823749950881 12044787614105117812463161)
    ·
      refine ⟨9033590710578838359347371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12044787614105117812463161 9033590710578838359347371)
      ·
        refine ⟨13550386065868257539021057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033590710578838359347371 13550386065868257539021057)
        ·
          refine ⟨10162789549401193154265793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13550386065868257539021057 10162789549401193154265793)
          ·
            refine ⟨7622092162050894865699345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10162789549401193154265793 7622092162050894865699345)
            ·
              refine ⟨5716569121538171149274509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7622092162050894865699345 5716569121538171149274509)
              ·
                refine ⟨2143713420576814180977941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5716569121538171149274509 2143713420576814180977941)
                ·
                  refine ⟨100486566589538164733341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2143713420576814180977941 100486566589538164733341)
                  ·
                    rfl

theorem cell22_880636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_880636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880636 prefixEnd_880636 := by exact prefixLift 880636
  have htrace : WordTrace (prefixWord ++ tailWord_880636) baseStart_880636 baseEnd_880636 := by
    simpa [prefixWord, tailWord_880636, baseEnd_880636] using wordTrace_append hprefix tailTrace_880636
  have hstable : (prefixWord ++ tailWord_880636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880636).length < 2 ^ (prefixWord ++ tailWord_880636).sum := by decide
  have hdescent : baseEnd_880636 < baseStart_880636 := by decide
  rcases family_descends (prefixWord ++ tailWord_880636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880646 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_880646 : Nat := 118140960795 + 880646 * 2 ^ 59
def prefixEnd_880646 : Nat := 4983230072969 + 3 ^ 40 * 880646 * 2
def baseEnd_880646 : Nat := 301463122972977801449993

theorem tailTrace_880646 : CollatzResearch.WordTrace tailWord_880646 prefixEnd_880646 301463122972977801449993 := by
  unfold tailWord_880646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003743698986794350242681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21413198911718279471843861 1003743698986794350242681)
  ·
    refine ⟨752807774240095762682011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1003743698986794350242681 752807774240095762682011)
    ·
      refine ⟨1129211661360143644023017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752807774240095762682011 1129211661360143644023017)
      ·
        refine ⟨846908746020107733017263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1129211661360143644023017 846908746020107733017263)
        ·
          refine ⟨1270363119030161599525895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846908746020107733017263 1270363119030161599525895)
          ·
            refine ⟨1905544678545242399288843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270363119030161599525895 1905544678545242399288843)
            ·
              refine ⟨2858317017817863598933265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905544678545242399288843 2858317017817863598933265)
              ·
                refine ⟨2143737763363397699199949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858317017817863598933265 2143737763363397699199949)
                ·
                  refine ⟨803901661261274137199981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2143737763363397699199949 803901661261274137199981)
                  ·
                    refine ⟨301463122972977801449993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803901661261274137199981 301463122972977801449993)
                    ·
                      rfl

theorem cell22_880646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_880646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880646 prefixEnd_880646 := by exact prefixLift 880646
  have htrace : WordTrace (prefixWord ++ tailWord_880646) baseStart_880646 baseEnd_880646 := by
    simpa [prefixWord, tailWord_880646, baseEnd_880646] using wordTrace_append hprefix tailTrace_880646
  have hstable : (prefixWord ++ tailWord_880646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880646).length < 2 ^ (prefixWord ++ tailWord_880646).sum := by decide
  have hdescent : baseEnd_880646 < baseStart_880646 := by decide
  rcases family_descends (prefixWord ++ tailWord_880646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880668 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_880668 : Nat := 118140960795 + 880668 * 2 ^ 59
def prefixEnd_880668 : Nat := 4983230072969 + 3 ^ 40 * 880668 * 2
def baseEnd_880668 : Nat := 301470654022577077399925

theorem tailTrace_880668 : CollatzResearch.WordTrace tailWord_880668 prefixEnd_880668 301470654022577077399925 := by
  unfold tailWord_880668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060300386748858482533329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21413733848998477976711105 16060300386748858482533329)
  ·
    refine ⟨12045225290061643861899997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16060300386748858482533329 12045225290061643861899997)
    ·
      refine ⟨4516959483773116448212499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12045225290061643861899997 4516959483773116448212499)
      ·
        refine ⟨6775439225659674672318749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516959483773116448212499 6775439225659674672318749)
        ·
          refine ⟨2540789709622378002119531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6775439225659674672318749 2540789709622378002119531)
          ·
            refine ⟨3811184564433567003179297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540789709622378002119531 3811184564433567003179297)
            ·
              refine ⟨2858388423325175252384473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3811184564433567003179297 2858388423325175252384473)
              ·
                refine ⟨2143791317493881439288355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858388423325175252384473 2143791317493881439288355)
                ·
                  refine ⟨3215686976240822158932533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143791317493881439288355 3215686976240822158932533)
                  ·
                    refine ⟨301470654022577077399925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3215686976240822158932533 301470654022577077399925)
                    ·
                      rfl

theorem cell22_880668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_880668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880668 prefixEnd_880668 := by exact prefixLift 880668
  have htrace : WordTrace (prefixWord ++ tailWord_880668) baseStart_880668 baseEnd_880668 := by
    simpa [prefixWord, tailWord_880668, baseEnd_880668] using wordTrace_append hprefix tailTrace_880668
  have hstable : (prefixWord ++ tailWord_880668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880668).length < 2 ^ (prefixWord ++ tailWord_880668).sum := by decide
  have hdescent : baseEnd_880668 < baseStart_880668 := by decide
  rcases family_descends (prefixWord ++ tailWord_880668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880702 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_880702 : Nat := 118140960795 + 880702 * 2 ^ 59
def prefixEnd_880702 : Nat := 4983230072969 + 3 ^ 40 * 880702 * 2
def baseEnd_880702 : Nat := 301482292917412322049821

theorem tailTrace_880702 : CollatzResearch.WordTrace tailWord_880702 prefixEnd_880702 301482292917412322049821 := by
  unfold tailWord_880702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015230106921817596475545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21414560570249693847869573 4015230106921817596475545)
  ·
    refine ⟨3011422580191363197356659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4015230106921817596475545 3011422580191363197356659)
    ·
      refine ⟨4517133870287044796034989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011422580191363197356659 4517133870287044796034989)
      ·
        refine ⟨1693925201357641798513121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4517133870287044796034989 1693925201357641798513121)
        ·
          refine ⟨1270443901018231348884841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693925201357641798513121 1270443901018231348884841)
          ·
            refine ⟨952832925763673511663631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270443901018231348884841 952832925763673511663631)
            ·
              refine ⟨1429249388645510267495447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952832925763673511663631 1429249388645510267495447)
              ·
                refine ⟨2143874082968265401243171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429249388645510267495447 2143874082968265401243171)
                ·
                  refine ⟨3215811124452398101864757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143874082968265401243171 3215811124452398101864757)
                  ·
                    refine ⟨301482292917412322049821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3215811124452398101864757 301482292917412322049821)
                    ·
                      rfl

theorem cell22_880702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_880702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880702 prefixEnd_880702 := by exact prefixLift 880702
  have htrace : WordTrace (prefixWord ++ tailWord_880702) baseStart_880702 baseEnd_880702 := by
    simpa [prefixWord, tailWord_880702, baseEnd_880702] using wordTrace_append hprefix tailTrace_880702
  have hstable : (prefixWord ++ tailWord_880702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880702).length < 2 ^ (prefixWord ++ tailWord_880702).sum := by decide
  have hdescent : baseEnd_880702 < baseStart_880702 := by decide
  rcases family_descends (prefixWord ++ tailWord_880702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880713 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_880713 : Nat := 118140960795 + 880713 * 2 ^ 59
def prefixEnd_880713 : Nat := 4983230072969 + 3 ^ 40 * 880713 * 2
def baseEnd_880713 : Nat := 301486058442211960024787

theorem tailTrace_880713 : CollatzResearch.WordTrace tailWord_880713 prefixEnd_880713 301486058442211960024787 := by
  unfold tailWord_880713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32122242058334689650454793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21414828038889793100303195 32122242058334689650454793)
  ·
    refine ⟨24091681543751017237841095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32122242058334689650454793 24091681543751017237841095)
    ·
      refine ⟨36137522315626525856761643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24091681543751017237841095 36137522315626525856761643)
      ·
        refine ⟨54206283473439788785142465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36137522315626525856761643 54206283473439788785142465)
        ·
          refine ⟨40654712605079841588856849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54206283473439788785142465 40654712605079841588856849)
          ·
            refine ⟨30491034453809881191642637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40654712605079841588856849 30491034453809881191642637)
            ·
              refine ⟨11434137920178705446865989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30491034453809881191642637 11434137920178705446865989)
              ·
                refine ⟨2143900860033507271287373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11434137920178705446865989 2143900860033507271287373)
                ·
                  refine ⟨803962822512565226732765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2143900860033507271287373 803962822512565226732765)
                  ·
                    refine ⟨301486058442211960024787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 803962822512565226732765 301486058442211960024787)
                    ·
                      rfl

theorem cell22_880713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_880713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880713 prefixEnd_880713 := by exact prefixLift 880713
  have htrace : WordTrace (prefixWord ++ tailWord_880713) baseStart_880713 baseEnd_880713 := by
    simpa [prefixWord, tailWord_880713, baseEnd_880713] using wordTrace_append hprefix tailTrace_880713
  have hstable : (prefixWord ++ tailWord_880713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880713).length < 2 ^ (prefixWord ++ tailWord_880713).sum := by decide
  have hdescent : baseEnd_880713 < baseStart_880713 := by decide
  rcases family_descends (prefixWord ++ tailWord_880713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880734 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_880734 : Nat := 118140960795 + 880734 * 2 ^ 59
def prefixEnd_880734 : Nat := 4983230072969 + 3 ^ 40 * 880734 * 2
def baseEnd_880734 : Nat := 301493247171374905249723

theorem tailTrace_880734 : CollatzResearch.WordTrace tailWord_880734 prefixEnd_880734 301493247171374905249723 := by
  unfold tailWord_880734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015375998907326279621157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21415338660839073491312837 4015375998907326279621157)
  ·
    refine ⟨752882999795123677428967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4015375998907326279621157 752882999795123677428967)
    ·
      refine ⟨1129324499692685516143451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752882999795123677428967 1129324499692685516143451)
      ·
        refine ⟨1693986749539028274215177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129324499692685516143451 1693986749539028274215177)
        ·
          refine ⟨1270490062154271205661383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693986749539028274215177 1270490062154271205661383)
          ·
            refine ⟨1905735093231406808492075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270490062154271205661383 1905735093231406808492075)
            ·
              refine ⟨2858602639847110212738113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905735093231406808492075 2858602639847110212738113)
              ·
                refine ⟨2143951979885332659553585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858602639847110212738113 2143951979885332659553585)
                ·
                  refine ⟨1607963984913999494665189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2143951979885332659553585 1607963984913999494665189)
                  ·
                    refine ⟨301493247171374905249723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1607963984913999494665189 301493247171374905249723)
                    ·
                      rfl

theorem cell22_880734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_880734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880734 prefixEnd_880734 := by exact prefixLift 880734
  have htrace : WordTrace (prefixWord ++ tailWord_880734) baseStart_880734 baseEnd_880734 := by
    simpa [prefixWord, tailWord_880734, baseEnd_880734] using wordTrace_append hprefix tailTrace_880734
  have hstable : (prefixWord ++ tailWord_880734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880734).length < 2 ^ (prefixWord ++ tailWord_880734).sum := by decide
  have hdescent : baseEnd_880734 < baseStart_880734 := by decide
  rcases family_descends (prefixWord ++ tailWord_880734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880743 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 5]
def baseStart_880743 : Nat := 118140960795 + 880743 * 2 ^ 59
def prefixEnd_880743 : Nat := 4983230072969 + 3 ^ 40 * 880743 * 2
def baseEnd_880743 : Nat := 100498776018433960591565

theorem tailTrace_880743 : CollatzResearch.WordTrace tailWord_880743 prefixEnd_880743 100498776018433960591565 := by
  unfold tailWord_880743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32123336248226004774046883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21415557498817336516031255 32123336248226004774046883)
  ·
    refine ⟨48185004372339007161070325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32123336248226004774046883 48185004372339007161070325)
    ·
      refine ⟨4517344159906781921350343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48185004372339007161070325 4517344159906781921350343)
      ·
        refine ⟨6776016239860172882025515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517344159906781921350343 6776016239860172882025515)
        ·
          refine ⟨10164024359790259323038273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776016239860172882025515 10164024359790259323038273)
          ·
            refine ⟨7623018269842694492278705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10164024359790259323038273 7623018269842694492278705)
            ·
              refine ⟨5717263702382020869209029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623018269842694492278705 5717263702382020869209029)
              ·
                refine ⟨1071986944196628912976693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5717263702382020869209029 1071986944196628912976693)
                ·
                  refine ⟨100498776018433960591565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071986944196628912976693 100498776018433960591565)
                  ·
                    rfl

theorem cell22_880743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 5].length) (baseStart_880743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880743 prefixEnd_880743 := by exact prefixLift 880743
  have htrace : WordTrace (prefixWord ++ tailWord_880743) baseStart_880743 baseEnd_880743 := by
    simpa [prefixWord, tailWord_880743, baseEnd_880743] using wordTrace_append hprefix tailTrace_880743
  have hstable : (prefixWord ++ tailWord_880743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880743).length < 2 ^ (prefixWord ++ tailWord_880743).sum := by decide
  have hdescent : baseEnd_880743 < baseStart_880743 := by decide
  rcases family_descends (prefixWord ++ tailWord_880743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880798 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_880798 : Nat := 118140960795 + 880798 * 2 ^ 59
def prefixEnd_880798 : Nat := 4983230072969 + 3 ^ 40 * 880798 * 2
def baseEnd_880798 : Nat := 301515155679300071649527

theorem tailTrace_880798 : CollatzResearch.WordTrace tailWord_880798 prefixEnd_880798 301515155679300071649527 := by
  unfold tailWord_880798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015667782878343645912381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21416894842017832778199365 4015667782878343645912381)
  ·
    refine ⟨1505875418579378867217143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4015667782878343645912381 1505875418579378867217143)
    ·
      refine ⟨2258813127869068300825715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505875418579378867217143 2258813127869068300825715)
      ·
        refine ⟨3388219691803602451238573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258813127869068300825715 3388219691803602451238573)
        ·
          refine ⟨1270582384426350919214465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3388219691803602451238573 1270582384426350919214465)
          ·
            refine ⟨952936788319763189410849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270582384426350919214465 952936788319763189410849)
            ·
              refine ⟨714702591239822392058137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952936788319763189410849 714702591239822392058137)
              ·
                refine ⟨536026943429866794043603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714702591239822392058137 536026943429866794043603)
                ·
                  refine ⟨804040415144800191065405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536026943429866794043603 804040415144800191065405)
                  ·
                    refine ⟨301515155679300071649527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804040415144800191065405 301515155679300071649527)
                    ·
                      rfl

theorem cell22_880798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_880798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880798 prefixEnd_880798 := by exact prefixLift 880798
  have htrace : WordTrace (prefixWord ++ tailWord_880798) baseStart_880798 baseEnd_880798 := by
    simpa [prefixWord, tailWord_880798, baseEnd_880798] using wordTrace_append hprefix tailTrace_880798
  have hstable : (prefixWord ++ tailWord_880798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880798).length < 2 ^ (prefixWord ++ tailWord_880798).sum := by decide
  have hdescent : baseEnd_880798 < baseStart_880798 := by decide
  rcases family_descends (prefixWord ++ tailWord_880798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880805 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 4]
def baseStart_880805 : Nat := 118140960795 + 880805 * 2 ^ 59
def prefixEnd_880805 : Nat := 4983230072969 + 3 ^ 40 * 880805 * 2
def baseEnd_880805 : Nat := 100505850640784795574835

theorem tailTrace_880805 : CollatzResearch.WordTrace tailWord_880805 prefixEnd_880805 100505850640784795574835 := by
  unfold tailWord_880805
  simp only [CollatzResearch.WordTrace]
  refine ⟨32125597574001389362803869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21417065049334259575202579 32125597574001389362803869)
  ·
    refine ⟨12047099090250521011051451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32125597574001389362803869 12047099090250521011051451)
    ·
      refine ⟨18070648635375781516577177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12047099090250521011051451 18070648635375781516577177)
      ·
        refine ⟨13552986476531836137432883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18070648635375781516577177 13552986476531836137432883)
        ·
          refine ⟨20329479714797754206149325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13552986476531836137432883 20329479714797754206149325)
          ·
            refine ⟨7623554893049157827305997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20329479714797754206149325 7623554893049157827305997)
            ·
              refine ⟨2858833084893434185239749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7623554893049157827305997 2858833084893434185239749)
              ·
                refine ⟨536031203417518909732453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2858833084893434185239749 536031203417518909732453)
                ·
                  refine ⟨100505850640784795574835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536031203417518909732453 100505850640784795574835)
                  ·
                    rfl

theorem cell22_880805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_880805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880805 prefixEnd_880805 := by exact prefixLift 880805
  have htrace : WordTrace (prefixWord ++ tailWord_880805) baseStart_880805 baseEnd_880805 := by
    simpa [prefixWord, tailWord_880805, baseEnd_880805] using wordTrace_append hprefix tailTrace_880805
  have hstable : (prefixWord ++ tailWord_880805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880805).length < 2 ^ (prefixWord ++ tailWord_880805).sum := by decide
  have hdescent : baseEnd_880805 < baseStart_880805 := by decide
  rcases family_descends (prefixWord ++ tailWord_880805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880818 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_880818 : Nat := 118140960795 + 880818 * 2 ^ 59
def prefixEnd_880818 : Nat := 4983230072969 + 3 ^ 40 * 880818 * 2
def baseEnd_880818 : Nat := 301522002088026686149465

theorem tailTrace_880818 : CollatzResearch.WordTrace tailWord_880818 prefixEnd_880818 301522002088026686149465 := by
  unfold tailWord_880818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031517930738573145756777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21417381148636195055351405 8031517930738573145756777)
  ·
    refine ⟨6023638448053929859317583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8031517930738573145756777 6023638448053929859317583)
    ·
      refine ⟨9035457672080894788976375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023638448053929859317583 9035457672080894788976375)
      ·
        refine ⟨13553186508121342183464563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035457672080894788976375 13553186508121342183464563)
        ·
          refine ⟨20329779762182013275196845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553186508121342183464563 20329779762182013275196845)
          ·
            refine ⟨7623667410818254978198817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20329779762182013275196845 7623667410818254978198817)
            ·
              refine ⟨5717750558113691233649113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623667410818254978198817 5717750558113691233649113)
              ·
                refine ⟨4288312918585268425236835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717750558113691233649113 4288312918585268425236835)
                ·
                  refine ⟨6432469377877902637855253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288312918585268425236835 6432469377877902637855253)
                  ·
                    refine ⟨301522002088026686149465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6432469377877902637855253 301522002088026686149465)
                    ·
                      rfl

theorem cell22_880818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_880818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880818 prefixEnd_880818 := by exact prefixLift 880818
  have htrace : WordTrace (prefixWord ++ tailWord_880818) baseStart_880818 baseEnd_880818 := by
    simpa [prefixWord, tailWord_880818, baseEnd_880818] using wordTrace_append hprefix tailTrace_880818
  have hstable : (prefixWord ++ tailWord_880818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880818).length < 2 ^ (prefixWord ++ tailWord_880818).sum := by decide
  have hdescent : baseEnd_880818 < baseStart_880818 := by decide
  rcases family_descends (prefixWord ++ tailWord_880818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880854 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_880854 : Nat := 118140960795 + 880854 * 2 ^ 59
def prefixEnd_880854 : Nat := 4983230072969 + 3 ^ 40 * 880854 * 2
def baseEnd_880854 : Nat := 301534325623734592249355

theorem tailTrace_880854 : CollatzResearch.WordTrace tailWord_880854 prefixEnd_880854 301534325623734592249355 := by
  unfold tailWord_880854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007961546926491920708601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21418256500549247154225077 2007961546926491920708601)
  ·
    refine ⟨1505971160194868940531451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2007961546926491920708601 1505971160194868940531451)
    ·
      refine ⟨2258956740292303410797177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505971160194868940531451 2258956740292303410797177)
      ·
        refine ⟨1694217555219227558097883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258956740292303410797177 1694217555219227558097883)
        ·
          refine ⟨2541326332828841337146825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694217555219227558097883 2541326332828841337146825)
          ·
            refine ⟨1905994749621631002860119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541326332828841337146825 1905994749621631002860119)
            ·
              refine ⟨2858992124432446504290179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905994749621631002860119 2858992124432446504290179)
              ·
                refine ⟨4288488186648669756435269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858992124432446504290179 4288488186648669756435269)
                ·
                  refine ⟨804091534996625579331613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4288488186648669756435269 804091534996625579331613)
                  ·
                    refine ⟨301534325623734592249355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804091534996625579331613 301534325623734592249355)
                    ·
                      rfl

theorem cell22_880854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_880854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880854 prefixEnd_880854 := by exact prefixLift 880854
  have htrace : WordTrace (prefixWord ++ tailWord_880854) baseStart_880854 baseEnd_880854 := by
    simpa [prefixWord, tailWord_880854, baseEnd_880854] using wordTrace_append hprefix tailTrace_880854
  have hstable : (prefixWord ++ tailWord_880854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880854).length < 2 ^ (prefixWord ++ tailWord_880854).sum := by decide
  have hdescent : baseEnd_880854 < baseStart_880854 := by decide
  rcases family_descends (prefixWord ++ tailWord_880854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880882 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_880882 : Nat := 118140960795 + 880882 * 2 ^ 59
def prefixEnd_880882 : Nat := 4983230072969 + 3 ^ 40 * 880882 * 2
def baseEnd_880882 : Nat := 301543910595951852549269

theorem tailTrace_880882 : CollatzResearch.WordTrace tailWord_880882 prefixEnd_880882 301543910595951852549269 := by
  unfold tailWord_880882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032101498680607878339225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21418937329814954342237933 8032101498680607878339225)
  ·
    refine ⟨6024076124010455908754419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8032101498680607878339225 6024076124010455908754419)
    ·
      refine ⟨9036114186015683863131629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6024076124010455908754419 9036114186015683863131629)
      ·
        refine ⟨3388542819755881448674361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9036114186015683863131629 3388542819755881448674361)
        ·
          refine ⟨2541407114816911086505771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388542819755881448674361 2541407114816911086505771)
          ·
            refine ⟨3812110672225366629758657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541407114816911086505771 3812110672225366629758657)
            ·
              refine ⟨2859083004169024972318993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812110672225366629758657 2859083004169024972318993)
              ·
                refine ⟨2144312253126768729239245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859083004169024972318993 2144312253126768729239245)
                ·
                  refine ⟨804117094922538273464717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2144312253126768729239245 804117094922538273464717)
                  ·
                    refine ⟨301543910595951852549269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804117094922538273464717 301543910595951852549269)
                    ·
                      rfl

theorem cell22_880882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_880882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880882 prefixEnd_880882 := by exact prefixLift 880882
  have htrace : WordTrace (prefixWord ++ tailWord_880882) baseStart_880882 baseEnd_880882 := by
    simpa [prefixWord, tailWord_880882, baseEnd_880882] using wordTrace_append hprefix tailTrace_880882
  have hstable : (prefixWord ++ tailWord_880882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880882).length < 2 ^ (prefixWord ++ tailWord_880882).sum := by decide
  have hdescent : baseEnd_880882 < baseStart_880882 := by decide
  rcases family_descends (prefixWord ++ tailWord_880882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880893 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_880893 : Nat := 118140960795 + 880893 * 2 ^ 59
def prefixEnd_880893 : Nat := 4983230072969 + 3 ^ 40 * 880893 * 2
def baseEnd_880893 : Nat := 301547676120751490524235

theorem tailTrace_880893 : CollatzResearch.WordTrace tailWord_880893 prefixEnd_880893 301547676120751490524235 := by
  unfold tailWord_880893
  simp only [CollatzResearch.WordTrace]
  refine ⟨32128807197682580392007333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21419204798455053594671555 32128807197682580392007333)
  ·
    refine ⟨6024151349565483823501375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32128807197682580392007333 6024151349565483823501375)
    ·
      refine ⟨9036227024348225735252063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6024151349565483823501375 9036227024348225735252063)
      ·
        refine ⟨13554340536522338602878095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036227024348225735252063 13554340536522338602878095)
        ·
          refine ⟨20331510804783507904317143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554340536522338602878095 20331510804783507904317143)
          ·
            refine ⟨30497266207175261856475715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20331510804783507904317143 30497266207175261856475715)
            ·
              refine ⟨45745899310762892784713573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30497266207175261856475715 45745899310762892784713573)
              ·
                refine ⟨8577356120768042397133795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45745899310762892784713573 8577356120768042397133795)
                ·
                  refine ⟨12866034181152063595700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577356120768042397133795 12866034181152063595700693)
                  ·
                    refine ⟨301547676120751490524235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12866034181152063595700693 301547676120751490524235)
                    ·
                      rfl

theorem cell22_880893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_880893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_880893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_880893 prefixEnd_880893 := by exact prefixLift 880893
  have htrace : WordTrace (prefixWord ++ tailWord_880893) baseStart_880893 baseEnd_880893 := by
    simpa [prefixWord, tailWord_880893, baseEnd_880893] using wordTrace_append hprefix tailTrace_880893
  have hstable : (prefixWord ++ tailWord_880893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880893).length < 2 ^ (prefixWord ++ tailWord_880893).sum := by decide
  have hdescent : baseEnd_880893 < baseStart_880893 := by decide
  rcases family_descends (prefixWord ++ tailWord_880893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881004 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_881004 : Nat := 118140960795 + 881004 * 2 ^ 59
def prefixEnd_881004 : Nat := 4983230072969 + 3 ^ 40 * 881004 * 2
def baseEnd_881004 : Nat := 301585673689184200998895

theorem tailTrace_881004 : CollatzResearch.WordTrace tailWord_881004 prefixEnd_881004 301585673689184200998895 := by
  unfold tailWord_881004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16066427850140223174649033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21421903800186964232865377 16066427850140223174649033)
  ·
    refine ⟨12049820887605167380986775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16066427850140223174649033 12049820887605167380986775)
    ·
      refine ⟨18074731331407751071480163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12049820887605167380986775 18074731331407751071480163)
      ·
        refine ⟨27112096997111626607220245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18074731331407751071480163 27112096997111626607220245)
        ·
          refine ⟨1270879546739607497213449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27112096997111626607220245 1270879546739607497213449)
          ·
            refine ⟨953159660054705622910087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270879546739607497213449 953159660054705622910087)
            ·
              refine ⟨1429739490082058434365131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953159660054705622910087 1429739490082058434365131)
              ·
                refine ⟨2144609235123087651547697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429739490082058434365131 2144609235123087651547697)
                ·
                  refine ⟨1608456926342315738660773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2144609235123087651547697 1608456926342315738660773)
                  ·
                    refine ⟨301585673689184200998895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1608456926342315738660773 301585673689184200998895)
                    ·
                      rfl

theorem cell22_881004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_881004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881004 prefixEnd_881004 := by exact prefixLift 881004
  have htrace : WordTrace (prefixWord ++ tailWord_881004) baseStart_881004 baseEnd_881004 := by
    simpa [prefixWord, tailWord_881004, baseEnd_881004] using wordTrace_append hprefix tailTrace_881004
  have hstable : (prefixWord ++ tailWord_881004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881004).length < 2 ^ (prefixWord ++ tailWord_881004).sum := by decide
  have hdescent : baseEnd_881004 < baseStart_881004 := by decide
  rcases family_descends (prefixWord ++ tailWord_881004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881105 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_881105 : Nat := 118140960795 + 881105 * 2 ^ 59
def prefixEnd_881105 : Nat := 4983230072969 + 3 ^ 40 * 881105 * 2
def baseEnd_881105 : Nat := 301620248053253604223585

theorem tailTrace_881105 : CollatzResearch.WordTrace tailWord_881105 prefixEnd_881105 301620248053253604223585 := by
  unfold tailWord_881105
  simp only [CollatzResearch.WordTrace]
  refine ⟨32136539472914540598724769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21424359648609693732483179 32136539472914540598724769)
  ·
    refine ⟨24102404604685905449043577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32136539472914540598724769 24102404604685905449043577)
    ·
      refine ⟨18076803453514429086782683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24102404604685905449043577 18076803453514429086782683)
      ·
        refine ⟨27115205180271643630174025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18076803453514429086782683 27115205180271643630174025)
        ·
          refine ⟨20336403885203732722630519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27115205180271643630174025 20336403885203732722630519)
          ·
            refine ⟨30504605827805599083945779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20336403885203732722630519 30504605827805599083945779)
            ·
              refine ⟨45756908741708398625918669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30504605827805599083945779 45756908741708398625918669)
              ·
                refine ⟨17158840778140649484719501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45756908741708398625918669 17158840778140649484719501)
                ·
                  refine ⟨6434565291802743556769813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17158840778140649484719501 6434565291802743556769813)
                  ·
                    refine ⟨301620248053253604223585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6434565291802743556769813 301620248053253604223585)
                    ·
                      rfl

theorem cell22_881105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_881105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881105 prefixEnd_881105 := by exact prefixLift 881105
  have htrace : WordTrace (prefixWord ++ tailWord_881105) baseStart_881105 baseEnd_881105 := by
    simpa [prefixWord, tailWord_881105, baseEnd_881105] using wordTrace_append hprefix tailTrace_881105
  have hstable : (prefixWord ++ tailWord_881105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881105).length < 2 ^ (prefixWord ++ tailWord_881105).sum := by decide
  have hdescent : baseEnd_881105 < baseStart_881105 := by decide
  rcases family_descends (prefixWord ++ tailWord_881105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881120 : List Nat := [2, 1, 1, 3, 1, 1, 3, 10]
def baseStart_881120 : Nat := 118140960795 + 881120 * 2 ^ 59
def prefixEnd_881120 : Nat := 4983230072969 + 3 ^ 40 * 881120 * 2
def baseEnd_881120 : Nat := 33513931428866507233171

theorem tailTrace_881120 : CollatzResearch.WordTrace tailWord_881120 prefixEnd_881120 33513931428866507233171 := by
  unfold tailWord_881120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16068543283930099080260407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21424724378573465440347209 16068543283930099080260407)
  ·
    refine ⟨24102814925895148620390611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16068543283930099080260407 24102814925895148620390611)
    ·
      refine ⟨36154222388842722930585917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24102814925895148620390611 36154222388842722930585917)
      ·
        refine ⟨13557833395816021098969719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36154222388842722930585917 13557833395816021098969719)
        ·
          refine ⟨20336750093724031648454579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13557833395816021098969719 20336750093724031648454579)
          ·
            refine ⟨30505125140586047472681869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20336750093724031648454579 30505125140586047472681869)
            ·
              refine ⟨11439421927719767802255701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30505125140586047472681869 11439421927719767802255701)
              ·
                refine ⟨33513931428866507233171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11439421927719767802255701 33513931428866507233171)
                ·
                  rfl

theorem cell22_881120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_881120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881120 prefixEnd_881120 := by exact prefixLift 881120
  have htrace : WordTrace (prefixWord ++ tailWord_881120) baseStart_881120 baseEnd_881120 := by
    simpa [prefixWord, tailWord_881120, baseEnd_881120] using wordTrace_append hprefix tailTrace_881120
  have hstable : (prefixWord ++ tailWord_881120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881120).length < 2 ^ (prefixWord ++ tailWord_881120).sum := by decide
  have hdescent : baseEnd_881120 < baseStart_881120 := by decide
  rcases family_descends (prefixWord ++ tailWord_881120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881152 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_881152 : Nat := 118140960795 + 881152 * 2 ^ 59
def prefixEnd_881152 : Nat := 4983230072969 + 3 ^ 40 * 881152 * 2
def baseEnd_881152 : Nat := 301636337113761148298441

theorem tailTrace_881152 : CollatzResearch.WordTrace tailWord_881152 prefixEnd_881152 301636337113761148298441 := by
  unfold tailWord_881152
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069126851872133812842855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21425502469162845083790473 16069126851872133812842855)
  ·
    refine ⟨24103690277808200719264283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16069126851872133812842855 24103690277808200719264283)
    ·
      refine ⟨36155535416712301078896425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24103690277808200719264283 36155535416712301078896425)
      ·
        refine ⟨27116651562534225809172319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36155535416712301078896425 27116651562534225809172319)
        ·
          refine ⟨40674977343801338713758479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27116651562534225809172319 40674977343801338713758479)
          ·
            refine ⟨61012466015702008070637719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40674977343801338713758479 61012466015702008070637719)
            ·
              refine ⟨91518699023553012105956579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61012466015702008070637719 91518699023553012105956579)
              ·
                refine ⟨137278048535329518158934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91518699023553012105956579 137278048535329518158934869)
                ·
                  refine ⟨804363565636696395462509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 137278048535329518158934869 804363565636696395462509)
                  ·
                    refine ⟨301636337113761148298441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804363565636696395462509 301636337113761148298441)
                    ·
                      rfl

theorem cell22_881152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_881152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881152 prefixEnd_881152 := by exact prefixLift 881152
  have htrace : WordTrace (prefixWord ++ tailWord_881152) baseStart_881152 baseEnd_881152 := by
    simpa [prefixWord, tailWord_881152, baseEnd_881152] using wordTrace_append hprefix tailTrace_881152
  have hstable : (prefixWord ++ tailWord_881152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881152).length < 2 ^ (prefixWord ++ tailWord_881152).sum := by decide
  have hdescent : baseEnd_881152 < baseStart_881152 := by decide
  rcases family_descends (prefixWord ++ tailWord_881152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881158 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_881158 : Nat := 118140960795 + 881158 * 2 ^ 59
def prefixEnd_881158 : Nat := 4983230072969 + 3 ^ 40 * 881158 * 2
def baseEnd_881158 : Nat := 301638391036379132648423

theorem tailTrace_881158 : CollatzResearch.WordTrace tailWord_881158 prefixEnd_881158 301638391036379132648423 := by
  unfold tailWord_881158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004327266928829082825129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21425648361148353766936085 1004327266928829082825129)
  ·
    refine ⟨753245450196621812118847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1004327266928829082825129 753245450196621812118847)
    ·
      refine ⟨1129868175294932718178271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753245450196621812118847 1129868175294932718178271)
      ·
        refine ⟨1694802262942399077267407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129868175294932718178271 1694802262942399077267407)
        ·
          refine ⟨2542203394413598615901111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694802262942399077267407 2542203394413598615901111)
          ·
            refine ⟨3813305091620397923851667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542203394413598615901111 3813305091620397923851667)
            ·
              refine ⟨5719957637430596885777501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813305091620397923851667 5719957637430596885777501)
              ·
                refine ⟨2144984114036473832166563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5719957637430596885777501 2144984114036473832166563)
                ·
                  refine ⟨3217476171054710748249845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144984114036473832166563 3217476171054710748249845)
                  ·
                    refine ⟨301638391036379132648423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3217476171054710748249845 301638391036379132648423)
                    ·
                      rfl

theorem cell22_881158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_881158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881158 prefixEnd_881158 := by exact prefixLift 881158
  have htrace : WordTrace (prefixWord ++ tailWord_881158) baseStart_881158 baseEnd_881158 := by
    simpa [prefixWord, tailWord_881158, baseEnd_881158] using wordTrace_append hprefix tailTrace_881158
  have hstable : (prefixWord ++ tailWord_881158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881158).length < 2 ^ (prefixWord ++ tailWord_881158).sum := by decide
  have hdescent : baseEnd_881158 < baseStart_881158 := by decide
  rcases family_descends (prefixWord ++ tailWord_881158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881227 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 6]
def baseStart_881227 : Nat := 118140960795 + 881227 * 2 ^ 59
def prefixEnd_881227 : Nat := 4983230072969 + 3 ^ 40 * 881227 * 2
def baseEnd_881227 : Nat := 100554003715495317557737

theorem tailTrace_881227 : CollatzResearch.WordTrace tailWord_881227 prefixEnd_881227 100554003715495317557737 := by
  unfold tailWord_881227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32140989178472555434665935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21427326118981703623110623 32140989178472555434665935)
  ·
    refine ⟨48211483767708833151998903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32140989178472555434665935 48211483767708833151998903)
    ·
      refine ⟨72317225651563249727998355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48211483767708833151998903 72317225651563249727998355)
      ·
        refine ⟨108475838477344874591997533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72317225651563249727998355 108475838477344874591997533)
        ·
          refine ⟨40678439429004327971999075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108475838477344874591997533 40678439429004327971999075)
          ·
            refine ⟨61017659143506491957998613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40678439429004327971999075 61017659143506491957998613)
            ·
              refine ⟨2860202772351866810531185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61017659143506491957998613 2860202772351866810531185)
              ·
                refine ⟨2145152079263900107898389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860202772351866810531185 2145152079263900107898389)
                ·
                  refine ⟨100554003715495317557737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2145152079263900107898389 100554003715495317557737)
                  ·
                    rfl

theorem cell22_881227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_881227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881227 prefixEnd_881227 := by exact prefixLift 881227
  have htrace : WordTrace (prefixWord ++ tailWord_881227) baseStart_881227 baseEnd_881227 := by
    simpa [prefixWord, tailWord_881227, baseEnd_881227] using wordTrace_append hprefix tailTrace_881227
  have hstable : (prefixWord ++ tailWord_881227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881227).length < 2 ^ (prefixWord ++ tailWord_881227).sum := by decide
  have hdescent : baseEnd_881227 < baseStart_881227 := by decide
  rcases family_descends (prefixWord ++ tailWord_881227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881261 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 6]
def baseStart_881261 : Nat := 118140960795 + 881261 * 2 ^ 59
def prefixEnd_881261 : Nat := 4983230072969 + 3 ^ 40 * 881261 * 2
def baseEnd_881261 : Nat := 100557883347107065774369

theorem tailTrace_881261 : CollatzResearch.WordTrace tailWord_881261 prefixEnd_881261 100557883347107065774369 := by
  unfold tailWord_881261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142229260349379241403637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21428152840232919494269091 32142229260349379241403637)
  ·
    refine ⟨3013333993157754303881591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32142229260349379241403637 3013333993157754303881591)
    ·
      refine ⟨4520000989736631455822387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3013333993157754303881591 4520000989736631455822387)
      ·
        refine ⟨6780001484604947183733581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520000989736631455822387 6780001484604947183733581)
        ·
          refine ⟨2542500556726855193900093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6780001484604947183733581 2542500556726855193900093)
          ·
            refine ⟨953437708772570697712535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2542500556726855193900093 953437708772570697712535)
            ·
              refine ⟨1430156563158856046568803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953437708772570697712535 1430156563158856046568803)
              ·
                refine ⟨2145234844738284069853205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430156563158856046568803 2145234844738284069853205)
                ·
                  refine ⟨100557883347107065774369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2145234844738284069853205 100557883347107065774369)
                  ·
                    rfl

theorem cell22_881261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_881261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881261 prefixEnd_881261 := by exact prefixLift 881261
  have htrace : WordTrace (prefixWord ++ tailWord_881261) baseStart_881261 baseEnd_881261 := by
    simpa [prefixWord, tailWord_881261, baseEnd_881261] using wordTrace_append hprefix tailTrace_881261
  have hstable : (prefixWord ++ tailWord_881261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881261).length < 2 ^ (prefixWord ++ tailWord_881261).sum := by decide
  have hdescent : baseEnd_881261 < baseStart_881261 := by decide
  rcases family_descends (prefixWord ++ tailWord_881261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881306 : List Nat := [3, 1, 1, 6, 2, 9]
def baseStart_881306 : Nat := 118140960795 + 881306 * 2 ^ 59
def prefixEnd_881306 : Nat := 4983230072969 + 3 ^ 40 * 881306 * 2
def baseEnd_881306 : Nat := 3724556227913038024049

theorem tailTrace_881306 : CollatzResearch.WordTrace tailWord_881306 prefixEnd_881306 3724556227913038024049 := by
  unfold tailWord_881306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035967636296587981697943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21429247030124234617861181 8035967636296587981697943)
  ·
    refine ⟨12053951454444881972546915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8035967636296587981697943 12053951454444881972546915)
    ·
      refine ⟨18080927181667322958820373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12053951454444881972546915 18080927181667322958820373)
      ·
        refine ⟨847543461640655763694705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18080927181667322958820373 847543461640655763694705)
        ·
          refine ⟨635657596230491822771029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847543461640655763694705 635657596230491822771029)
          ·
            refine ⟨3724556227913038024049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 635657596230491822771029 3724556227913038024049)
            ·
              rfl

theorem cell22_881306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 9].length) (baseStart_881306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881306 prefixEnd_881306 := by exact prefixLift 881306
  have htrace : WordTrace (prefixWord ++ tailWord_881306) baseStart_881306 baseEnd_881306 := by
    simpa [prefixWord, tailWord_881306, baseEnd_881306] using wordTrace_append hprefix tailTrace_881306
  have hstable : (prefixWord ++ tailWord_881306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881306).length < 2 ^ (prefixWord ++ tailWord_881306).sum := by decide
  have hdescent : baseEnd_881306 < baseStart_881306 := by decide
  rcases family_descends (prefixWord ++ tailWord_881306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881398 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_881398 : Nat := 118140960795 + 881398 * 2 ^ 59
def prefixEnd_881398 : Nat := 4983230072969 + 3 ^ 40 * 881398 * 2
def baseEnd_881398 : Nat := 301720547941098506647687

theorem tailTrace_881398 : CollatzResearch.WordTrace tailWord_881398 prefixEnd_881398 301720547941098506647687 := by
  unfold tailWord_881398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009201628803315727446303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21431484040568701092760565 2009201628803315727446303)
  ·
    refine ⟨3013802443204973591169455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2009201628803315727446303 3013802443204973591169455)
    ·
      refine ⟨4520703664807460386754183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3013802443204973591169455 4520703664807460386754183)
      ·
        refine ⟨6781055497211190580131275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4520703664807460386754183 6781055497211190580131275)
        ·
          refine ⟨10171583245816785870196913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781055497211190580131275 10171583245816785870196913)
          ·
            refine ⟨7628687434362589402647685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10171583245816785870196913 7628687434362589402647685)
            ·
              refine ⟨1430378893942985512996441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7628687434362589402647685 1430378893942985512996441)
              ·
                refine ⟨1072784170457239134747331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430378893942985512996441 1072784170457239134747331)
                ·
                  refine ⟨1609176255685858702120997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072784170457239134747331 1609176255685858702120997)
                  ·
                    refine ⟨301720547941098506647687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609176255685858702120997 301720547941098506647687)
                    ·
                      rfl

theorem cell22_881398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_881398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881398 prefixEnd_881398 := by exact prefixLift 881398
  have htrace : WordTrace (prefixWord ++ tailWord_881398) baseStart_881398 baseEnd_881398 := by
    simpa [prefixWord, tailWord_881398, baseEnd_881398] using wordTrace_append hprefix tailTrace_881398
  have hstable : (prefixWord ++ tailWord_881398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881398).length < 2 ^ (prefixWord ++ tailWord_881398).sum := by decide
  have hdescent : baseEnd_881398 < baseStart_881398 := by decide
  rcases family_descends (prefixWord ++ tailWord_881398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881456 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_881456 : Nat := 118140960795 + 881456 * 2 ^ 59
def prefixEnd_881456 : Nat := 4983230072969 + 3 ^ 40 * 881456 * 2
def baseEnd_881456 : Nat := 301740402526405688697509

theorem tailTrace_881456 : CollatzResearch.WordTrace tailWord_881456 prefixEnd_881456 301740402526405688697509 := by
  unfold tailWord_881456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074670747321463772376111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21432894329761951696501481 16074670747321463772376111)
  ·
    refine ⟨24112006120982195658564167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16074670747321463772376111 24112006120982195658564167)
    ·
      refine ⟨36168009181473293487846251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24112006120982195658564167 36168009181473293487846251)
      ·
        refine ⟨54252013772209940231769377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36168009181473293487846251 54252013772209940231769377)
        ·
          refine ⟨40689010329157455173827033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54252013772209940231769377 40689010329157455173827033)
          ·
            refine ⟨30516757746868091380370275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40689010329157455173827033 30516757746868091380370275)
            ·
              refine ⟨45775136620302137070555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30516757746868091380370275 45775136620302137070555413)
              ·
                refine ⟨2145709529076662675182285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45775136620302137070555413 2145709529076662675182285)
                ·
                  refine ⟨804641073403748503193357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2145709529076662675182285 804641073403748503193357)
                  ·
                    refine ⟨301740402526405688697509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804641073403748503193357 301740402526405688697509)
                    ·
                      rfl

theorem cell22_881456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_881456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881456 prefixEnd_881456 := by exact prefixLift 881456
  have htrace : WordTrace (prefixWord ++ tailWord_881456) baseStart_881456 baseEnd_881456 := by
    simpa [prefixWord, tailWord_881456, baseEnd_881456] using wordTrace_append hprefix tailTrace_881456
  have hstable : (prefixWord ++ tailWord_881456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881456).length < 2 ^ (prefixWord ++ tailWord_881456).sum := by decide
  have hdescent : baseEnd_881456 < baseStart_881456 := by decide
  rcases family_descends (prefixWord ++ tailWord_881456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881460 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_881460 : Nat := 118140960795 + 881460 * 2 ^ 59
def prefixEnd_881460 : Nat := 4983230072969 + 3 ^ 40 * 881460 * 2
def baseEnd_881460 : Nat := 301741771808151011597497

theorem tailTrace_881460 : CollatzResearch.WordTrace tailWord_881460 prefixEnd_881460 301741771808151011597497 := by
  unfold tailWord_881460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074743693314218113948917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21432991591085624151931889 16074743693314218113948917)
  ·
    refine ⟨1507007221248207948182711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16074743693314218113948917 1507007221248207948182711)
    ·
      refine ⟨2260510831872311922274067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507007221248207948182711 2260510831872311922274067)
      ·
        refine ⟨3390766247808467883411101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260510831872311922274067 3390766247808467883411101)
        ·
          refine ⟨1271537342928175456279163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3390766247808467883411101 1271537342928175456279163)
          ·
            refine ⟨1907306014392263184418745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271537342928175456279163 1907306014392263184418745)
            ·
              refine ⟨1430479510794197388314059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907306014392263184418745 1430479510794197388314059)
              ·
                refine ⟨2145719266191296082471089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430479510794197388314059 2145719266191296082471089)
                ·
                  refine ⟨1609289449643472061853317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145719266191296082471089 1609289449643472061853317)
                  ·
                    refine ⟨301741771808151011597497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609289449643472061853317 301741771808151011597497)
                    ·
                      rfl

theorem cell22_881460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_881460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881460 prefixEnd_881460 := by exact prefixLift 881460
  have htrace : WordTrace (prefixWord ++ tailWord_881460) baseStart_881460 baseEnd_881460 := by
    simpa [prefixWord, tailWord_881460, baseEnd_881460] using wordTrace_append hprefix tailTrace_881460
  have hstable : (prefixWord ++ tailWord_881460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881460).length < 2 ^ (prefixWord ++ tailWord_881460).sum := by decide
  have hdescent : baseEnd_881460 < baseStart_881460 := by decide
  rcases family_descends (prefixWord ++ tailWord_881460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881490 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_881490 : Nat := 118140960795 + 881490 * 2 ^ 59
def prefixEnd_881490 : Nat := 4983230072969 + 3 ^ 40 * 881490 * 2
def baseEnd_881490 : Nat := 301752041421240933347405

theorem tailTrace_881490 : CollatzResearch.WordTrace tailWord_881490 prefixEnd_881490 301752041421240933347405 := by
  unfold tailWord_881490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037645394129937837872481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21433721051013167567659949 8037645394129937837872481)
  ·
    refine ⟨6028234045597453378404361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8037645394129937837872481 6028234045597453378404361)
    ·
      refine ⟨4521175534198090033803271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6028234045597453378404361 4521175534198090033803271)
      ·
        refine ⟨6781763301297135050704907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521175534198090033803271 6781763301297135050704907)
        ·
          refine ⟨10172644951945702576057361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781763301297135050704907 10172644951945702576057361)
          ·
            refine ⟨7629483713959276932043021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10172644951945702576057361 7629483713959276932043021)
            ·
              refine ⟨2861056392734728849516133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7629483713959276932043021 2861056392734728849516133)
              ·
                refine ⟨536448073637761659284275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2861056392734728849516133 536448073637761659284275)
                ·
                  refine ⟨804672110456642488926413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536448073637761659284275 804672110456642488926413)
                  ·
                    refine ⟨301752041421240933347405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 804672110456642488926413 301752041421240933347405)
                    ·
                      rfl

theorem cell22_881490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_881490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881490 prefixEnd_881490 := by exact prefixLift 881490
  have htrace : WordTrace (prefixWord ++ tailWord_881490) baseStart_881490 baseEnd_881490 := by
    simpa [prefixWord, tailWord_881490, baseEnd_881490] using wordTrace_append hprefix tailTrace_881490
  have hstable : (prefixWord ++ tailWord_881490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881490).length < 2 ^ (prefixWord ++ tailWord_881490).sum := by decide
  have hdescent : baseEnd_881490 < baseStart_881490 := by decide
  rcases family_descends (prefixWord ++ tailWord_881490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881516 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_881516 : Nat := 118140960795 + 881516 * 2 ^ 59
def prefixEnd_881516 : Nat := 4983230072969 + 3 ^ 40 * 881516 * 2
def baseEnd_881516 : Nat := 301760941752585532197325

theorem tailTrace_881516 : CollatzResearch.WordTrace tailWord_881516 prefixEnd_881516 301760941752585532197325 := by
  unfold tailWord_881516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075764937212778895968201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21434353249617038527957601 16075764937212778895968201)
  ·
    refine ⟨12056823702909584171976151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16075764937212778895968201 12056823702909584171976151)
    ·
      refine ⟨18085235554364376257964227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12056823702909584171976151 18085235554364376257964227)
      ·
        refine ⟨27127853331546564386946341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18085235554364376257964227 27127853331546564386946341)
        ·
          refine ⟨5086472499664980822552439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27127853331546564386946341 5086472499664980822552439)
          ·
            refine ⟨7629708749497471233828659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086472499664980822552439 7629708749497471233828659)
            ·
              refine ⟨11444563124246206850742989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7629708749497471233828659 11444563124246206850742989)
              ·
                refine ⟨4291711171592327569028621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11444563124246206850742989 4291711171592327569028621)
                ·
                  refine ⟨1609391689347122838385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4291711171592327569028621 1609391689347122838385733)
                  ·
                    refine ⟨301760941752585532197325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609391689347122838385733 301760941752585532197325)
                    ·
                      rfl

theorem cell22_881516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_881516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881516 prefixEnd_881516 := by exact prefixLift 881516
  have htrace : WordTrace (prefixWord ++ tailWord_881516) baseStart_881516 baseEnd_881516 := by
    simpa [prefixWord, tailWord_881516, baseEnd_881516] using wordTrace_append hprefix tailTrace_881516
  have hstable : (prefixWord ++ tailWord_881516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881516).length < 2 ^ (prefixWord ++ tailWord_881516).sum := by decide
  have hdescent : baseEnd_881516 < baseStart_881516 := by decide
  rcases family_descends (prefixWord ++ tailWord_881516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881548 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_881548 : Nat := 118140960795 + 881548 * 2 ^ 59
def prefixEnd_881548 : Nat := 4983230072969 + 3 ^ 40 * 881548 * 2
def baseEnd_881548 : Nat := 100590632002182705132409

theorem tailTrace_881548 : CollatzResearch.WordTrace tailWord_881548 prefixEnd_881548 100590632002182705132409 := by
  unfold tailWord_881548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16076348505154813628550649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21435131340206418171400865 16076348505154813628550649)
  ·
    refine ⟨12057261378866110221412987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16076348505154813628550649 12057261378866110221412987)
    ·
      refine ⟨18085892068299165332119481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12057261378866110221412987 18085892068299165332119481)
      ·
        refine ⟨13564419051224373999089611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18085892068299165332119481 13564419051224373999089611)
        ·
          refine ⟨20346628576836560998634417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13564419051224373999089611 20346628576836560998634417)
          ·
            refine ⟨15259971432627420748975813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20346628576836560998634417 15259971432627420748975813)
            ·
              refine ⟨2861244643617641390432965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15259971432627420748975813 2861244643617641390432965)
              ·
                refine ⟨536483370678307760706181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2861244643617641390432965 536483370678307760706181)
                ·
                  refine ⟨100590632002182705132409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536483370678307760706181 100590632002182705132409)
                  ·
                    rfl

theorem cell22_881548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_881548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881548 prefixEnd_881548 := by exact prefixLift 881548
  have htrace : WordTrace (prefixWord ++ tailWord_881548) baseStart_881548 baseEnd_881548 := by
    simpa [prefixWord, tailWord_881548, baseEnd_881548] using wordTrace_append hprefix tailTrace_881548
  have hstable : (prefixWord ++ tailWord_881548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881548).length < 2 ^ (prefixWord ++ tailWord_881548).sum := by decide
  have hdescent : baseEnd_881548 < baseStart_881548 := by decide
  rcases family_descends (prefixWord ++ tailWord_881548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881636 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_881636 : Nat := 118140960795 + 881636 * 2 ^ 59
def prefixEnd_881636 : Nat := 4983230072969 + 3 ^ 40 * 881636 * 2
def baseEnd_881636 : Nat := 301802020204945219196957

theorem tailTrace_881636 : CollatzResearch.WordTrace tailWord_881636 prefixEnd_881636 301802020204945219196957 := by
  unfold tailWord_881636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16077953316995409143152381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21437271089327212190869841 16077953316995409143152381)
  ·
    refine ⟨6029232493873278428682143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16077953316995409143152381 6029232493873278428682143)
    ·
      refine ⟨9043848740809917643023215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029232493873278428682143 9043848740809917643023215)
      ·
        refine ⟨13565773111214876464534823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9043848740809917643023215 13565773111214876464534823)
        ·
          refine ⟨20348659666822314696802235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13565773111214876464534823 20348659666822314696802235)
          ·
            refine ⟨30522989500233472045203353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20348659666822314696802235 30522989500233472045203353)
            ·
              refine ⟨22892242125175104033902515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30522989500233472045203353 22892242125175104033902515)
              ·
                refine ⟨34338363187762656050853773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22892242125175104033902515 34338363187762656050853773)
                ·
                  refine ⟨12876886195410996019070165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34338363187762656050853773 12876886195410996019070165)
                  ·
                    refine ⟨301802020204945219196957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12876886195410996019070165 301802020204945219196957)
                    ·
                      rfl

theorem cell22_881636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_881636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881636 prefixEnd_881636 := by exact prefixLift 881636
  have htrace : WordTrace (prefixWord ++ tailWord_881636) baseStart_881636 baseEnd_881636 := by
    simpa [prefixWord, tailWord_881636, baseEnd_881636] using wordTrace_append hprefix tailTrace_881636
  have hstable : (prefixWord ++ tailWord_881636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881636).length < 2 ^ (prefixWord ++ tailWord_881636).sum := by decide
  have hdescent : baseEnd_881636 < baseStart_881636 := by decide
  rcases family_descends (prefixWord ++ tailWord_881636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881713 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_881713 : Nat := 118140960795 + 881713 * 2 ^ 59
def prefixEnd_881713 : Nat := 4983230072969 + 3 ^ 40 * 881713 * 2
def baseEnd_881713 : Nat := 301828378878542685021721

theorem tailTrace_881713 : CollatzResearch.WordTrace tailWord_881713 prefixEnd_881713 301828378878542685021721 := by
  unfold tailWord_881713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32158715054711860436857793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21439143369807906957905195 32158715054711860436857793)
  ·
    refine ⟨24119036291033895327643345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32158715054711860436857793 24119036291033895327643345)
    ·
      refine ⟨18089277218275421495732509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24119036291033895327643345 18089277218275421495732509)
      ·
        refine ⟨6783478956853283060899691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18089277218275421495732509 6783478956853283060899691)
        ·
          refine ⟨10175218435279924591349537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783478956853283060899691 10175218435279924591349537)
          ·
            refine ⟨7631413826459943443512153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175218435279924591349537 7631413826459943443512153)
            ·
              refine ⟨5723560369844957582634115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7631413826459943443512153 5723560369844957582634115)
              ·
                refine ⟨8585340554767436373951173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5723560369844957582634115 8585340554767436373951173)
                ·
                  refine ⟨1609751354018894320115845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8585340554767436373951173 1609751354018894320115845)
                  ·
                    refine ⟨301828378878542685021721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1609751354018894320115845 301828378878542685021721)
                    ·
                      rfl

theorem cell22_881713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_881713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881713 prefixEnd_881713 := by exact prefixLift 881713
  have htrace : WordTrace (prefixWord ++ tailWord_881713) baseStart_881713 baseEnd_881713 := by
    simpa [prefixWord, tailWord_881713, baseEnd_881713] using wordTrace_append hprefix tailTrace_881713
  have hstable : (prefixWord ++ tailWord_881713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881713).length < 2 ^ (prefixWord ++ tailWord_881713).sum := by decide
  have hdescent : baseEnd_881713 < baseStart_881713 := by decide
  rcases family_descends (prefixWord ++ tailWord_881713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881788 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_881788 : Nat := 118140960795 + 881788 * 2 ^ 59
def prefixEnd_881788 : Nat := 4983230072969 + 3 ^ 40 * 881788 * 2
def baseEnd_881788 : Nat := 301854052911267489396491

theorem tailTrace_881788 : CollatzResearch.WordTrace tailWord_881788 prefixEnd_881788 301854052911267489396491 := by
  unfold tailWord_881788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080725264720074122919009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21440967019626765497225345 16080725264720074122919009)
  ·
    refine ⟨12060543948540055592189257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16080725264720074122919009 12060543948540055592189257)
    ·
      refine ⟨9045407961405041694141943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12060543948540055592189257 9045407961405041694141943)
      ·
        refine ⟨13568111942107562541212915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045407961405041694141943 13568111942107562541212915)
        ·
          refine ⟨20352167913161343811819373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13568111942107562541212915 20352167913161343811819373)
          ·
            refine ⟨7632062967435503929432265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20352167913161343811819373 7632062967435503929432265)
            ·
              refine ⟨5724047225576627947074199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7632062967435503929432265 5724047225576627947074199)
              ·
                refine ⟨8586070838364941920611299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724047225576627947074199 8586070838364941920611299)
                ·
                  refine ⟨12879106257547412880916949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8586070838364941920611299 12879106257547412880916949)
                  ·
                    refine ⟨301854052911267489396491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12879106257547412880916949 301854052911267489396491)
                    ·
                      rfl

theorem cell22_881788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_881788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881788 prefixEnd_881788 := by exact prefixLift 881788
  have htrace : WordTrace (prefixWord ++ tailWord_881788) baseStart_881788 baseEnd_881788 := by
    simpa [prefixWord, tailWord_881788, baseEnd_881788] using wordTrace_append hprefix tailTrace_881788
  have hstable : (prefixWord ++ tailWord_881788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881788).length < 2 ^ (prefixWord ++ tailWord_881788).sum := by decide
  have hdescent : baseEnd_881788 < baseStart_881788 := by decide
  rcases family_descends (prefixWord ++ tailWord_881788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881850 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_881850 : Nat := 118140960795 + 881850 * 2 ^ 59
def prefixEnd_881850 : Nat := 4983230072969 + 3 ^ 40 * 881850 * 2
def baseEnd_881850 : Nat := 301875276778319994346301

theorem tailTrace_881850 : CollatzResearch.WordTrace tailWord_881850 prefixEnd_881850 301875276778319994346301 := by
  unfold tailWord_881850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8040927963803883208648751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21442474570143688556396669 8040927963803883208648751)
  ·
    refine ⟨12061391945705824812973127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8040927963803883208648751 12061391945705824812973127)
    ·
      refine ⟨18092087918558737219459691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12061391945705824812973127 18092087918558737219459691)
      ·
        refine ⟨27138131877838105829189537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092087918558737219459691 27138131877838105829189537)
        ·
          refine ⟨20353598908378579371892153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27138131877838105829189537 20353598908378579371892153)
          ·
            refine ⟨15265199181283934528919115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20353598908378579371892153 15265199181283934528919115)
            ·
              refine ⟨22897798771925901793378673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15265199181283934528919115 22897798771925901793378673)
              ·
                refine ⟨17173349078944426345034005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22897798771925901793378673 17173349078944426345034005)
                ·
                  refine ⟨805000738075519984923469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17173349078944426345034005 805000738075519984923469)
                  ·
                    refine ⟨301875276778319994346301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805000738075519984923469 301875276778319994346301)
                    ·
                      rfl

theorem cell22_881850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_881850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881850 prefixEnd_881850 := by exact prefixLift 881850
  have htrace : WordTrace (prefixWord ++ tailWord_881850) baseStart_881850 baseEnd_881850 := by
    simpa [prefixWord, tailWord_881850, baseEnd_881850] using wordTrace_append hprefix tailTrace_881850
  have hstable : (prefixWord ++ tailWord_881850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881850).length < 2 ^ (prefixWord ++ tailWord_881850).sum := by decide
  have hdescent : baseEnd_881850 < baseStart_881850 := by decide
  rcases family_descends (prefixWord ++ tailWord_881850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881863 : List Nat := [1, 1, 4, 1, 1, 1, 1, 12]
def baseStart_881863 : Nat := 118140960795 + 881863 * 2 ^ 59
def prefixEnd_881863 : Nat := 4983230072969 + 3 ^ 40 * 881863 * 2
def baseEnd_881863 : Nat := 33542191882665810419029

theorem tailTrace_881863 : CollatzResearch.WordTrace tailWord_881863 prefixEnd_881863 33542191882665810419029 := by
  unfold tailWord_881863
  simp only [CollatzResearch.WordTrace]
  refine ⟨32164186004168436054818243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21442790669445624036545495 32164186004168436054818243)
  ·
    refine ⟨48246279006252654082227365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32164186004168436054818243 48246279006252654082227365)
    ·
      refine ⟨9046177313672372640417631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48246279006252654082227365 9046177313672372640417631)
      ·
        refine ⟨13569265970508558960626447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046177313672372640417631 13569265970508558960626447)
        ·
          refine ⟨20353898955762838440939671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13569265970508558960626447 20353898955762838440939671)
          ·
            refine ⟨30530848433644257661409507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20353898955762838440939671 30530848433644257661409507)
            ·
              refine ⟨45796272650466386492114261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30530848433644257661409507 45796272650466386492114261)
              ·
                refine ⟨33542191882665810419029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 45796272650466386492114261 33542191882665810419029)
                ·
                  rfl

theorem cell22_881863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 12].length) (baseStart_881863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881863 prefixEnd_881863 := by exact prefixLift 881863
  have htrace : WordTrace (prefixWord ++ tailWord_881863) baseStart_881863 baseEnd_881863 := by
    simpa [prefixWord, tailWord_881863, baseEnd_881863] using wordTrace_append hprefix tailTrace_881863
  have hstable : (prefixWord ++ tailWord_881863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881863).length < 2 ^ (prefixWord ++ tailWord_881863).sum := by decide
  have hdescent : baseEnd_881863 < baseStart_881863 := by decide
  rcases family_descends (prefixWord ++ tailWord_881863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881880 : List Nat := [2, 1, 2, 2, 5, 1, 9]
def baseStart_881880 : Nat := 118140960795 + 881880 * 2 ^ 59
def prefixEnd_881880 : Nat := 4983230072969 + 3 ^ 40 * 881880 * 2
def baseEnd_881880 : Nat := 11180946162644811707267

theorem tailTrace_881880 : CollatzResearch.WordTrace tailWord_881880 prefixEnd_881880 11180946162644811707267 := by
  unfold tailWord_881880
  simp only [CollatzResearch.WordTrace]
  refine ⟨16082403022553423979093547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21443204030071231972124729 16082403022553423979093547)
  ·
    refine ⟨24123604533830135968640321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16082403022553423979093547 24123604533830135968640321)
    ·
      refine ⟨18092703400372601976480241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24123604533830135968640321 18092703400372601976480241)
      ·
        refine ⟨13569527550279451482360181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18092703400372601976480241 13569527550279451482360181)
        ·
          refine ⟨1272143207838698576471267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13569527550279451482360181 1272143207838698576471267)
          ·
            refine ⟨1908214811758047864706901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272143207838698576471267 1908214811758047864706901)
            ·
              refine ⟨11180946162644811707267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1908214811758047864706901 11180946162644811707267)
              ·
                rfl

theorem cell22_881880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 9].length) (baseStart_881880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881880 prefixEnd_881880 := by exact prefixLift 881880
  have htrace : WordTrace (prefixWord ++ tailWord_881880) baseStart_881880 baseEnd_881880 := by
    simpa [prefixWord, tailWord_881880, baseEnd_881880] using wordTrace_append hprefix tailTrace_881880
  have hstable : (prefixWord ++ tailWord_881880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881880).length < 2 ^ (prefixWord ++ tailWord_881880).sum := by decide
  have hdescent : baseEnd_881880 < baseStart_881880 := by decide
  rcases family_descends (prefixWord ++ tailWord_881880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881901 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_881901 : Nat := 118140960795 + 881901 * 2 ^ 59
def prefixEnd_881901 : Nat := 4983230072969 + 3 ^ 40 * 881901 * 2
def baseEnd_881901 : Nat := 301892735120572861321145

theorem tailTrace_881901 : CollatzResearch.WordTrace tailWord_881901 prefixEnd_881901 301892735120572861321145 := by
  unfold tailWord_881901
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165571978030768544701557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21443714652020512363134371 32165571978030768544701557)
  ·
    refine ⟨3015522372940384551065771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32165571978030768544701557 3015522372940384551065771)
    ·
      refine ⟨4523283559410576826598657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015522372940384551065771 4523283559410576826598657)
      ·
        refine ⟨3392462669557932619948993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4523283559410576826598657 3392462669557932619948993)
        ·
          refine ⟨2544347002168449464961745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3392462669557932619948993 2544347002168449464961745)
          ·
            refine ⟨1908260251626337098721309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544347002168449464961745 1908260251626337098721309)
            ·
              refine ⟨715597594359876412020491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1908260251626337098721309 715597594359876412020491)
              ·
                refine ⟨1073396391539814618030737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715597594359876412020491 1073396391539814618030737)
                ·
                  refine ⟨805047293654860963523053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1073396391539814618030737 805047293654860963523053)
                  ·
                    refine ⟨301892735120572861321145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805047293654860963523053 301892735120572861321145)
                    ·
                      rfl

theorem cell22_881901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_881901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881901 prefixEnd_881901 := by exact prefixLift 881901
  have htrace : WordTrace (prefixWord ++ tailWord_881901) baseStart_881901 baseEnd_881901 := by
    simpa [prefixWord, tailWord_881901, baseEnd_881901] using wordTrace_append hprefix tailTrace_881901
  have hstable : (prefixWord ++ tailWord_881901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881901).length < 2 ^ (prefixWord ++ tailWord_881901).sum := by decide
  have hdescent : baseEnd_881901 < baseStart_881901 := by decide
  rcases family_descends (prefixWord ++ tailWord_881901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881987 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 4]
def baseStart_881987 : Nat := 118140960795 + 881987 * 2 ^ 59
def prefixEnd_881987 : Nat := 4983230072969 + 3 ^ 40 * 881987 * 2
def baseEnd_881987 : Nat := 100640724892699101223627

theorem tailTrace_881987 : CollatzResearch.WordTrace tailWord_881987 prefixEnd_881987 100640724892699101223627 := by
  unfold tailWord_881987
  simp only [CollatzResearch.WordTrace]
  refine ⟨32168708655719205232332215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21445805770479470154888143 32168708655719205232332215)
  ·
    refine ⟨48253062983578807848498323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32168708655719205232332215 48253062983578807848498323)
    ·
      refine ⟨72379594475368211772747485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48253062983578807848498323 72379594475368211772747485)
      ·
        refine ⟨27142347928263079414780307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72379594475368211772747485 27142347928263079414780307)
        ·
          refine ⟨40713521892394619122170461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27142347928263079414780307 40713521892394619122170461)
          ·
            refine ⟨15267570709647982170813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40713521892394619122170461 15267570709647982170813923)
            ·
              refine ⟨22901356064471973256220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15267570709647982170813923 22901356064471973256220885)
              ·
                refine ⟨536750532761061873192677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22901356064471973256220885 536750532761061873192677)
                ·
                  refine ⟨100640724892699101223627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536750532761061873192677 100640724892699101223627)
                  ·
                    rfl

theorem cell22_881987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 4].length) (baseStart_881987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881987 prefixEnd_881987 := by exact prefixLift 881987
  have htrace : WordTrace (prefixWord ++ tailWord_881987) baseStart_881987 baseEnd_881987 := by
    simpa [prefixWord, tailWord_881987, baseEnd_881987] using wordTrace_append hprefix tailTrace_881987
  have hstable : (prefixWord ++ tailWord_881987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881987).length < 2 ^ (prefixWord ++ tailWord_881987).sum := by decide
  have hdescent : baseEnd_881987 < baseStart_881987 := by decide
  rcases family_descends (prefixWord ++ tailWord_881987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881997 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_881997 : Nat := 118140960795 + 881997 * 2 ^ 59
def prefixEnd_881997 : Nat := 4983230072969 + 3 ^ 40 * 881997 * 2
def baseEnd_881997 : Nat := 301925597882460610920851

theorem tailTrace_881997 : CollatzResearch.WordTrace tailWord_881997 prefixEnd_881997 301925597882460610920851 := by
  unfold tailWord_881997
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169073385682976940196245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21446048923788651293464163 32169073385682976940196245)
  ·
    refine ⟨1507925314953889544071699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32169073385682976940196245 1507925314953889544071699)
    ·
      refine ⟨2261887972430834316107549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507925314953889544071699 2261887972430834316107549)
      ·
        refine ⟨848207989661562868540331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2261887972430834316107549 848207989661562868540331)
        ·
          refine ⟨1272311984492344302810497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848207989661562868540331 1272311984492344302810497)
          ·
            refine ⟨954233988369258227107873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272311984492344302810497 954233988369258227107873)
            ·
              refine ⟨715675491276943670330905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954233988369258227107873 715675491276943670330905)
              ·
                refine ⟨536756618457707752748179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715675491276943670330905 536756618457707752748179)
                ·
                  refine ⟨805134927686561629122269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536756618457707752748179 805134927686561629122269)
                  ·
                    refine ⟨301925597882460610920851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805134927686561629122269 301925597882460610920851)
                    ·
                      rfl

theorem cell22_881997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_881997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_881997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_881997 prefixEnd_881997 := by exact prefixLift 881997
  have htrace : WordTrace (prefixWord ++ tailWord_881997) baseStart_881997 baseEnd_881997 := by
    simpa [prefixWord, tailWord_881997, baseEnd_881997] using wordTrace_append hprefix tailTrace_881997
  have hstable : (prefixWord ++ tailWord_881997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881997).length < 2 ^ (prefixWord ++ tailWord_881997).sum := by decide
  have hdescent : baseEnd_881997 < baseStart_881997 := by decide
  rcases family_descends (prefixWord ++ tailWord_881997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882004 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_882004 : Nat := 118140960795 + 882004 * 2 ^ 59
def prefixEnd_882004 : Nat := 4983230072969 + 3 ^ 40 * 882004 * 2
def baseEnd_882004 : Nat := 100642664708504975331943

theorem tailTrace_882004 : CollatzResearch.WordTrace tailWord_882004 prefixEnd_882004 100642664708504975331943 := by
  unfold tailWord_882004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084664348328808567850533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21446219131105078090467377 16084664348328808567850533)
  ·
    refine ⟨3015874565311651606471975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16084664348328808567850533 3015874565311651606471975)
    ·
      refine ⟨4523811847967477409707963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015874565311651606471975 4523811847967477409707963)
      ·
        refine ⟨6785717771951216114561945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523811847967477409707963 6785717771951216114561945)
        ·
          refine ⟨5089288328963412085921459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6785717771951216114561945 5089288328963412085921459)
          ·
            refine ⟨7633932493445118128882189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5089288328963412085921459 7633932493445118128882189)
            ·
              refine ⟨2862724685041919298330821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7633932493445118128882189 2862724685041919298330821)
              ·
                refine ⟨536760878445359868437029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2862724685041919298330821 536760878445359868437029)
                ·
                  refine ⟨100642664708504975331943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536760878445359868437029 100642664708504975331943)
                  ·
                    rfl

theorem cell22_882004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_882004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882004 prefixEnd_882004 := by exact prefixLift 882004
  have htrace : WordTrace (prefixWord ++ tailWord_882004) baseStart_882004 baseEnd_882004 := by
    simpa [prefixWord, tailWord_882004, baseEnd_882004] using wordTrace_append hprefix tailTrace_882004
  have hstable : (prefixWord ++ tailWord_882004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882004).length < 2 ^ (prefixWord ++ tailWord_882004).sum := by decide
  have hdescent : baseEnd_882004 < baseStart_882004 := by decide
  rcases family_descends (prefixWord ++ tailWord_882004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882019 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 2, 3]
def baseStart_882019 : Nat := 118140960795 + 882019 * 2 ^ 59
def prefixEnd_882019 : Nat := 4983230072969 + 3 ^ 40 * 882019 * 2
def baseEnd_882019 : Nat := 301933128932059886870783

theorem tailTrace_882019 : CollatzResearch.WordTrace tailWord_882019 prefixEnd_882019 301933128932059886870783 := by
  unfold tailWord_882019
  simp only [CollatzResearch.WordTrace]
  refine ⟨32169875791603274697497111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21446583861068849798331407 32169875791603274697497111)
  ·
    refine ⟨48254813687404912046245667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32169875791603274697497111 48254813687404912046245667)
    ·
      refine ⟨72382220531107368069368501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48254813687404912046245667 72382220531107368069368501)
      ·
        refine ⟨6785833174791315756503297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72382220531107368069368501 6785833174791315756503297)
        ·
          refine ⟨5089374881093486817377473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6785833174791315756503297 5089374881093486817377473)
          ·
            refine ⟨3817031160820115113033105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089374881093486817377473 3817031160820115113033105)
            ·
              refine ⟨2862773370615086334774829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817031160820115113033105 2862773370615086334774829)
              ·
                refine ⟨1073540013980657375540561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2862773370615086334774829 1073540013980657375540561)
                ·
                  refine ⟨805155010485493031655421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1073540013980657375540561 805155010485493031655421)
                  ·
                    refine ⟨301933128932059886870783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805155010485493031655421 301933128932059886870783)
                    ·
                      rfl

theorem cell22_882019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3].length) (baseStart_882019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882019 prefixEnd_882019 := by exact prefixLift 882019
  have htrace : WordTrace (prefixWord ++ tailWord_882019) baseStart_882019 baseEnd_882019 := by
    simpa [prefixWord, tailWord_882019, baseEnd_882019] using wordTrace_append hprefix tailTrace_882019
  have hstable : (prefixWord ++ tailWord_882019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882019).length < 2 ^ (prefixWord ++ tailWord_882019).sum := by decide
  have hdescent : baseEnd_882019 < baseStart_882019 := by decide
  rcases family_descends (prefixWord ++ tailWord_882019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882032 : List Nat := [2, 1, 1, 1, 4, 2, 5, 6]
def baseStart_882032 : Nat := 118140960795 + 882032 * 2 ^ 59
def prefixEnd_882032 : Nat := 4983230072969 + 3 ^ 40 * 882032 * 2
def baseEnd_882032 : Nat := 33548619899748020699527

theorem tailTrace_882032 : CollatzResearch.WordTrace tailWord_882032 prefixEnd_882032 33548619899748020699527 := by
  unfold tailWord_882032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16085174970278088958860175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21446899960370785278480233 16085174970278088958860175)
  ·
    refine ⟨24127762455417133438290263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16085174970278088958860175 24127762455417133438290263)
    ·
      refine ⟨36191643683125700157435395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24127762455417133438290263 36191643683125700157435395)
      ·
        refine ⟨54287465524688550236153093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36191643683125700157435395 54287465524688550236153093)
        ·
          refine ⟨10178899785879103169278705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54287465524688550236153093 10178899785879103169278705)
          ·
            refine ⟨7634174839409327376959029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10178899785879103169278705 7634174839409327376959029)
            ·
              refine ⟨715703891194624441589909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7634174839409327376959029 715703891194624441589909)
              ·
                refine ⟨33548619899748020699527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 715703891194624441589909 33548619899748020699527)
                ·
                  rfl

theorem cell22_882032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_882032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882032 prefixEnd_882032 := by exact prefixLift 882032
  have htrace : WordTrace (prefixWord ++ tailWord_882032) baseStart_882032 baseEnd_882032 := by
    simpa [prefixWord, tailWord_882032, baseEnd_882032] using wordTrace_append hprefix tailTrace_882032
  have hstable : (prefixWord ++ tailWord_882032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882032).length < 2 ^ (prefixWord ++ tailWord_882032).sum := by decide
  have hdescent : baseEnd_882032 < baseStart_882032 := by decide
  rcases family_descends (prefixWord ++ tailWord_882032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882141 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_882141 : Nat := 118140960795 + 882141 * 2 ^ 59
def prefixEnd_882141 : Nat := 4983230072969 + 3 ^ 40 * 882141 * 2
def baseEnd_882141 : Nat := 301974892025292235320409

theorem tailTrace_882141 : CollatzResearch.WordTrace tailWord_882141 prefixEnd_882141 301974892025292235320409 := by
  unfold tailWord_882141
  simp only [CollatzResearch.WordTrace]
  refine ⟨32174325497161289533438277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21449550331440859688958851 32174325497161289533438277)
  ·
    refine ⟨6032686030717741787519677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32174325497161289533438277 6032686030717741787519677)
    ·
      refine ⟨2262257261519153170319879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6032686030717741787519677 2262257261519153170319879)
      ·
        refine ⟨3393385892278729755479819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262257261519153170319879 3393385892278729755479819)
        ·
          refine ⟨5090078838418094633219729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393385892278729755479819 5090078838418094633219729)
          ·
            refine ⟨3817559128813570974914797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090078838418094633219729 3817559128813570974914797)
            ·
              refine ⟨1431584673305089115593049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3817559128813570974914797 1431584673305089115593049)
              ·
                refine ⟨1073688504978816836694787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431584673305089115593049 1073688504978816836694787)
                ·
                  refine ⟨1610532757468225255042181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073688504978816836694787 1610532757468225255042181)
                  ·
                    refine ⟨301974892025292235320409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1610532757468225255042181 301974892025292235320409)
                    ·
                      rfl

theorem cell22_882141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_882141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882141 prefixEnd_882141 := by exact prefixLift 882141
  have htrace : WordTrace (prefixWord ++ tailWord_882141) baseStart_882141 baseEnd_882141 := by
    simpa [prefixWord, tailWord_882141, baseEnd_882141] using wordTrace_append hprefix tailTrace_882141
  have hstable : (prefixWord ++ tailWord_882141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882141).length < 2 ^ (prefixWord ++ tailWord_882141).sum := by decide
  have hdescent : baseEnd_882141 < baseStart_882141 := by decide
  rcases family_descends (prefixWord ++ tailWord_882141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882173 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 4]
def baseStart_882173 : Nat := 118140960795 + 882173 * 2 ^ 59
def prefixEnd_882173 : Nat := 4983230072969 + 3 ^ 40 * 882173 * 2
def baseEnd_882173 : Nat := 100661948759751606173437

theorem tailTrace_882173 : CollatzResearch.WordTrace tailWord_882173 prefixEnd_882173 100661948759751606173437 := by
  unfold tailWord_882173
  simp only [CollatzResearch.WordTrace]
  refine ⟨32175492633045358998603173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21450328422030239332402115 32175492633045358998603173)
  ·
    refine ⟨6032904868696004812238095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32175492633045358998603173 6032904868696004812238095)
    ·
      refine ⟨9049357303044007218357143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6032904868696004812238095 9049357303044007218357143)
      ·
        refine ⟨13574035954566010827535715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049357303044007218357143 13574035954566010827535715)
        ·
          refine ⟨20361053931849016241303573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574035954566010827535715 20361053931849016241303573)
          ·
            refine ⟨954424403055422636311105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20361053931849016241303573 954424403055422636311105)
            ·
              refine ⟨715818302291566977233329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954424403055422636311105 715818302291566977233329)
              ·
                refine ⟨536863726718675232924997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715818302291566977233329 536863726718675232924997)
                ·
                  refine ⟨100661948759751606173437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536863726718675232924997 100661948759751606173437)
                  ·
                    rfl

theorem cell22_882173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_882173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882173 prefixEnd_882173 := by exact prefixLift 882173
  have htrace : WordTrace (prefixWord ++ tailWord_882173) baseStart_882173 baseEnd_882173 := by
    simpa [prefixWord, tailWord_882173, baseEnd_882173] using wordTrace_append hprefix tailTrace_882173
  have hstable : (prefixWord ++ tailWord_882173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882173).length < 2 ^ (prefixWord ++ tailWord_882173).sum := by decide
  have hdescent : baseEnd_882173 < baseStart_882173 := by decide
  rcases family_descends (prefixWord ++ tailWord_882173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882229 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 7]
def baseStart_882229 : Nat := 118140960795 + 882229 * 2 ^ 59
def prefixEnd_882229 : Nat := 4983230072969 + 3 ^ 40 * 882229 * 2
def baseEnd_882229 : Nat := 100668338741229779706713

theorem tailTrace_882229 : CollatzResearch.WordTrace tailWord_882229 prefixEnd_882229 100668338741229779706713 := by
  unfold tailWord_882229
  simp only [CollatzResearch.WordTrace]
  refine ⟨32177535120842480562641741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21451690080561653708427827 32177535120842480562641741)
  ·
    refine ⟨12066575670315930210990653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32177535120842480562641741 12066575670315930210990653)
    ·
      refine ⟨4524965876368473829121495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12066575670315930210990653 4524965876368473829121495)
      ·
        refine ⟨6787448814552710743682243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4524965876368473829121495 6787448814552710743682243)
        ·
          refine ⟨10181173221829066115523365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6787448814552710743682243 10181173221829066115523365)
          ·
            refine ⟨1908969979092949896660631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10181173221829066115523365 1908969979092949896660631)
            ·
              refine ⟨2863454968639424844990947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908969979092949896660631 2863454968639424844990947)
              ·
                refine ⟨4295182452959137267486421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2863454968639424844990947 4295182452959137267486421)
                ·
                  refine ⟨100668338741229779706713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4295182452959137267486421 100668338741229779706713)
                  ·
                    rfl

theorem cell22_882229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_882229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882229 prefixEnd_882229 := by exact prefixLift 882229
  have htrace : WordTrace (prefixWord ++ tailWord_882229) baseStart_882229 baseEnd_882229 := by
    simpa [prefixWord, tailWord_882229, baseEnd_882229] using wordTrace_append hprefix tailTrace_882229
  have hstable : (prefixWord ++ tailWord_882229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882229).length < 2 ^ (prefixWord ++ tailWord_882229).sum := by decide
  have hdescent : baseEnd_882229 < baseStart_882229 := by decide
  rcases family_descends (prefixWord ++ tailWord_882229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882233 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 1, 3]
def baseStart_882233 : Nat := 118140960795 + 882233 * 2 ^ 59
def prefixEnd_882233 : Nat := 4983230072969 + 3 ^ 40 * 882233 * 2
def baseEnd_882233 : Nat := 302006385505434662020127

theorem tailTrace_882233 : CollatzResearch.WordTrace tailWord_882233 prefixEnd_882233 302006385505434662020127 := by
  unfold tailWord_882233
  simp only [CollatzResearch.WordTrace]
  refine ⟨32177681012827989245787353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21451787341885326163858235 32177681012827989245787353)
  ·
    refine ⟨24133260759620991934340515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32177681012827989245787353 24133260759620991934340515)
    ·
      refine ⟨36199891139431487901510773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24133260759620991934340515 36199891139431487901510773)
      ·
        refine ⟨3393739794321701990766635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36199891139431487901510773 3393739794321701990766635)
        ·
          refine ⟨5090609691482552986149953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393739794321701990766635 5090609691482552986149953)
          ·
            refine ⟨3817957268611914739612465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090609691482552986149953 3817957268611914739612465)
            ·
              refine ⟨2863467951458936054709349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817957268611914739612465 2863467951458936054709349)
              ·
                refine ⟨536900240898550510258003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2863467951458936054709349 536900240898550510258003)
                ·
                  refine ⟨805350361347825765387005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536900240898550510258003 805350361347825765387005)
                  ·
                    refine ⟨302006385505434662020127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805350361347825765387005 302006385505434662020127)
                    ·
                      rfl

theorem cell22_882233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_882233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882233 prefixEnd_882233 := by exact prefixLift 882233
  have htrace : WordTrace (prefixWord ++ tailWord_882233) baseStart_882233 baseEnd_882233 := by
    simpa [prefixWord, tailWord_882233, baseEnd_882233] using wordTrace_append hprefix tailTrace_882233
  have hstable : (prefixWord ++ tailWord_882233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882233).length < 2 ^ (prefixWord ++ tailWord_882233).sum := by decide
  have hdescent : baseEnd_882233 < baseStart_882233 := by decide
  rcases family_descends (prefixWord ++ tailWord_882233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882276 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_882276 : Nat := 118140960795 + 882276 * 2 ^ 59
def prefixEnd_882276 : Nat := 4983230072969 + 3 ^ 40 * 882276 * 2
def baseEnd_882276 : Nat := 302021105284196883194995

theorem tailTrace_882276 : CollatzResearch.WordTrace tailWord_882276 prefixEnd_882276 302021105284196883194995 := by
  unfold tailWord_882276
  simp only [CollatzResearch.WordTrace]
  refine ⟨16089624675836103794801341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21452832901114805059735121 16089624675836103794801341)
  ·
    refine ⟨6033609253438538923050503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16089624675836103794801341 6033609253438538923050503)
    ·
      refine ⟨9050413880157808384575755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033609253438538923050503 9050413880157808384575755)
      ·
        refine ⟨13575620820236712576863633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050413880157808384575755 13575620820236712576863633)
        ·
          refine ⟨10181715615177534432647725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13575620820236712576863633 10181715615177534432647725)
          ·
            refine ⟨3818143355691575412242897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10181715615177534432647725 3818143355691575412242897)
            ·
              refine ⟨2863607516768681559182173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818143355691575412242897 2863607516768681559182173)
              ·
                refine ⟨1073852818788255584693315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2863607516768681559182173 1073852818788255584693315)
                ·
                  refine ⟨1610779228182383377039973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1073852818788255584693315 1610779228182383377039973)
                  ·
                    refine ⟨302021105284196883194995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1610779228182383377039973 302021105284196883194995)
                    ·
                      rfl

theorem cell22_882276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_882276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882276 prefixEnd_882276 := by exact prefixLift 882276
  have htrace : WordTrace (prefixWord ++ tailWord_882276) baseStart_882276 baseEnd_882276 := by
    simpa [prefixWord, tailWord_882276, baseEnd_882276] using wordTrace_append hprefix tailTrace_882276
  have hstable : (prefixWord ++ tailWord_882276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882276).length < 2 ^ (prefixWord ++ tailWord_882276).sum := by decide
  have hdescent : baseEnd_882276 < baseStart_882276 := by decide
  rcases family_descends (prefixWord ++ tailWord_882276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882304 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_882304 : Nat := 118140960795 + 882304 * 2 ^ 59
def prefixEnd_882304 : Nat := 4983230072969 + 3 ^ 40 * 882304 * 2
def baseEnd_882304 : Nat := 302030690256414143494909

theorem tailTrace_882304 : CollatzResearch.WordTrace tailWord_882304 prefixEnd_882304 302030690256414143494909 := by
  unfold tailWord_882304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090135297785384185810983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21453513730380512247747977 16090135297785384185810983)
  ·
    refine ⟨24135202946678076278716475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16090135297785384185810983 24135202946678076278716475)
    ·
      refine ⟨36202804420017114418074713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24135202946678076278716475 36202804420017114418074713)
      ·
        refine ⟨27152103315012835813556035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36202804420017114418074713 27152103315012835813556035)
        ·
          refine ⟨40728154972519253720334053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27152103315012835813556035 40728154972519253720334053)
          ·
            refine ⟨7636529057347360072562635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40728154972519253720334053 7636529057347360072562635)
            ·
              refine ⟨11454793586021040108843953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636529057347360072562635 11454793586021040108843953)
              ·
                refine ⟨8591095189515780081632965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11454793586021040108843953 8591095189515780081632965)
                ·
                  refine ⟨1610830348034208765306181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8591095189515780081632965 1610830348034208765306181)
                  ·
                    refine ⟨302030690256414143494909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1610830348034208765306181 302030690256414143494909)
                    ·
                      rfl

theorem cell22_882304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_882304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882304 prefixEnd_882304 := by exact prefixLift 882304
  have htrace : WordTrace (prefixWord ++ tailWord_882304) baseStart_882304 baseEnd_882304 := by
    simpa [prefixWord, tailWord_882304, baseEnd_882304] using wordTrace_append hprefix tailTrace_882304
  have hstable : (prefixWord ++ tailWord_882304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882304).length < 2 ^ (prefixWord ++ tailWord_882304).sum := by decide
  have hdescent : baseEnd_882304 < baseStart_882304 := by decide
  rcases family_descends (prefixWord ++ tailWord_882304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882351 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 3, 3]
def baseStart_882351 : Nat := 118140960795 + 882351 * 2 ^ 59
def prefixEnd_882351 : Nat := 4983230072969 + 3 ^ 40 * 882351 * 2
def baseEnd_882351 : Nat := 302046779316921687569765

theorem tailTrace_882351 : CollatzResearch.WordTrace tailWord_882351 prefixEnd_882351 302046779316921687569765 := by
  unfold tailWord_882351
  simp only [CollatzResearch.WordTrace]
  refine ⟨32181984826400495398582907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21454656550933663599055271 32181984826400495398582907)
  ·
    refine ⟨48272977239600743097874361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32181984826400495398582907 48272977239600743097874361)
    ·
      refine ⟨36204732929700557323405771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48272977239600743097874361 36204732929700557323405771)
      ·
        refine ⟨54307099394550835985108657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36204732929700557323405771 54307099394550835985108657)
        ·
          refine ⟨40730324545913126988831493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54307099394550835985108657 40730324545913126988831493)
          ·
            refine ⟨7636935852358711310405905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40730324545913126988831493 7636935852358711310405905)
            ·
              refine ⟨5727701889269033482804429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636935852358711310405905 5727701889269033482804429)
              ·
                refine ⟨2147888208475887556051661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5727701889269033482804429 2147888208475887556051661)
                ·
                  refine ⟨805458078178457833519373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2147888208475887556051661 805458078178457833519373)
                  ·
                    refine ⟨302046779316921687569765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805458078178457833519373 302046779316921687569765)
                    ·
                      rfl

theorem cell22_882351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_882351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882351 prefixEnd_882351 := by exact prefixLift 882351
  have htrace : WordTrace (prefixWord ++ tailWord_882351) baseStart_882351 baseEnd_882351 := by
    simpa [prefixWord, tailWord_882351, baseEnd_882351] using wordTrace_append hprefix tailTrace_882351
  have hstable : (prefixWord ++ tailWord_882351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882351).length < 2 ^ (prefixWord ++ tailWord_882351).sum := by decide
  have hdescent : baseEnd_882351 < baseStart_882351 := by decide
  rcases family_descends (prefixWord ++ tailWord_882351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882385 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 1, 3]
def baseStart_882385 : Nat := 118140960795 + 882385 * 2 ^ 59
def prefixEnd_882385 : Nat := 4983230072969 + 3 ^ 40 * 882385 * 2
def baseEnd_882385 : Nat := 302058418211756932219661

theorem tailTrace_882385 : CollatzResearch.WordTrace tailWord_882385 prefixEnd_882385 302058418211756932219661 := by
  unfold tailWord_882385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183224908277319205320609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21455483272184879470213739 32183224908277319205320609)
  ·
    refine ⟨24137418681207989403990457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32183224908277319205320609 24137418681207989403990457)
    ·
      refine ⟨18103064010905992052992843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24137418681207989403990457 18103064010905992052992843)
      ·
        refine ⟨27154596016358988079489265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18103064010905992052992843 27154596016358988079489265)
        ·
          refine ⟨20365947012269241059616949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27154596016358988079489265 20365947012269241059616949)
          ·
            refine ⟨1909307532400241349339089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20365947012269241059616949 1909307532400241349339089)
            ·
              refine ⟨1431980649300181012004317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909307532400241349339089 1431980649300181012004317)
              ·
                refine ⟨536992743487567879501619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431980649300181012004317 536992743487567879501619)
                ·
                  refine ⟨805489115231351819252429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536992743487567879501619 805489115231351819252429)
                  ·
                    refine ⟨302058418211756932219661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805489115231351819252429 302058418211756932219661)
                    ·
                      rfl

theorem cell22_882385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_882385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882385 prefixEnd_882385 := by exact prefixLift 882385
  have htrace : WordTrace (prefixWord ++ tailWord_882385) baseStart_882385 baseEnd_882385 := by
    simpa [prefixWord, tailWord_882385, baseEnd_882385] using wordTrace_append hprefix tailTrace_882385
  have hstable : (prefixWord ++ tailWord_882385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882385).length < 2 ^ (prefixWord ++ tailWord_882385).sum := by decide
  have hdescent : baseEnd_882385 < baseStart_882385 := by decide
  rcases family_descends (prefixWord ++ tailWord_882385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882428 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_882428 : Nat := 118140960795 + 882428 * 2 ^ 59
def prefixEnd_882428 : Nat := 4983230072969 + 3 ^ 40 * 882428 * 2
def baseEnd_882428 : Nat := 302073137990519153394529

theorem tailTrace_882428 : CollatzResearch.WordTrace tailWord_882428 prefixEnd_882428 302073137990519153394529 := by
  unfold tailWord_882428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092396623560768774567969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21456528831414358366090625 16092396623560768774567969)
  ·
    refine ⟨12069297467670576580925977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16092396623560768774567969 12069297467670576580925977)
    ·
      refine ⟨9051973100752932435694483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12069297467670576580925977 9051973100752932435694483)
      ·
        refine ⟨13577959651129398653541725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9051973100752932435694483 13577959651129398653541725)
        ·
          refine ⟨5091734869173524495078147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13577959651129398653541725 5091734869173524495078147)
          ·
            refine ⟨7637602303760286742617221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5091734869173524495078147 7637602303760286742617221)
            ·
              refine ⟨1432050431955053764240729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7637602303760286742617221 1432050431955053764240729)
              ·
                refine ⟨1074037823966290323180547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432050431955053764240729 1074037823966290323180547)
                ·
                  refine ⟨1611056735949435484770821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1074037823966290323180547 1611056735949435484770821)
                  ·
                    refine ⟨302073137990519153394529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1611056735949435484770821 302073137990519153394529)
                    ·
                      rfl

theorem cell22_882428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_882428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882428 prefixEnd_882428 := by exact prefixLift 882428
  have htrace : WordTrace (prefixWord ++ tailWord_882428) baseStart_882428 baseEnd_882428 := by
    simpa [prefixWord, tailWord_882428, baseEnd_882428] using wordTrace_append hprefix tailTrace_882428
  have hstable : (prefixWord ++ tailWord_882428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882428).length < 2 ^ (prefixWord ++ tailWord_882428).sum := by decide
  have hdescent : baseEnd_882428 < baseStart_882428 := by decide
  rcases family_descends (prefixWord ++ tailWord_882428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882443 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 4]
def baseStart_882443 : Nat := 118140960795 + 882443 * 2 ^ 59
def prefixEnd_882443 : Nat := 4983230072969 + 3 ^ 40 * 882443 * 2
def baseEnd_882443 : Nat := 100692757599021371423161

theorem tailTrace_882443 : CollatzResearch.WordTrace tailWord_882443 prefixEnd_882443 100692757599021371423161 := by
  unfold tailWord_882443
  simp only [CollatzResearch.WordTrace]
  refine ⟨32185340342067195110931983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21456893561378130073954655 32185340342067195110931983)
  ·
    refine ⟨48278010513100792666397975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32185340342067195110931983 48278010513100792666397975)
    ·
      refine ⟨72417015769651188999596963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48278010513100792666397975 72417015769651188999596963)
      ·
        refine ⟨108625523654476783499395445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72417015769651188999596963 108625523654476783499395445)
        ·
          refine ⟨10183642842607198453068323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108625523654476783499395445 10183642842607198453068323)
          ·
            refine ⟨15275464263910797679602485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183642842607198453068323 15275464263910797679602485)
            ·
              refine ⟨1432074774741637282462733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15275464263910797679602485 1432074774741637282462733)
              ·
                refine ⟨537028040528113980923525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432074774741637282462733 537028040528113980923525)
                ·
                  refine ⟨100692757599021371423161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537028040528113980923525 100692757599021371423161)
                  ·
                    rfl

theorem cell22_882443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 4].length) (baseStart_882443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882443 prefixEnd_882443 := by exact prefixLift 882443
  have htrace : WordTrace (prefixWord ++ tailWord_882443) baseStart_882443 baseEnd_882443 := by
    simpa [prefixWord, tailWord_882443, baseEnd_882443] using wordTrace_append hprefix tailTrace_882443
  have hstable : (prefixWord ++ tailWord_882443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882443).length < 2 ^ (prefixWord ++ tailWord_882443).sum := by decide
  have hdescent : baseEnd_882443 < baseStart_882443 := by decide
  rcases family_descends (prefixWord ++ tailWord_882443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882456 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_882456 : Nat := 118140960795 + 882456 * 2 ^ 59
def prefixEnd_882456 : Nat := 4983230072969 + 3 ^ 40 * 882456 * 2
def baseEnd_882456 : Nat := 302082722962736413694443

theorem tailTrace_882456 : CollatzResearch.WordTrace tailWord_882456 prefixEnd_882456 302082722962736413694443 := by
  unfold tailWord_882456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092907245510049165577611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21457209660680065554103481 16092907245510049165577611)
  ·
    refine ⟨24139360868265073748366417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16092907245510049165577611 24139360868265073748366417)
    ·
      refine ⟨18104520651198805311274813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24139360868265073748366417 18104520651198805311274813)
      ·
        refine ⟨6789195244199551991728055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18104520651198805311274813 6789195244199551991728055)
        ·
          refine ⟨10183792866299327987592083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789195244199551991728055 10183792866299327987592083)
          ·
            refine ⟨15275689299448991981388125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10183792866299327987592083 15275689299448991981388125)
            ·
              refine ⟨5728383487293371993020547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15275689299448991981388125 5728383487293371993020547)
              ·
                refine ⟨8592575230940057989530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728383487293371993020547 8592575230940057989530821)
                ·
                  refine ⟨1611107855801260873037029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8592575230940057989530821 1611107855801260873037029)
                  ·
                    refine ⟨302082722962736413694443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1611107855801260873037029 302082722962736413694443)
                    ·
                      rfl

theorem cell22_882456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_882456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882456 prefixEnd_882456 := by exact prefixLift 882456
  have htrace : WordTrace (prefixWord ++ tailWord_882456) baseStart_882456 baseEnd_882456 := by
    simpa [prefixWord, tailWord_882456, baseEnd_882456] using wordTrace_append hprefix tailTrace_882456
  have hstable : (prefixWord ++ tailWord_882456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882456).length < 2 ^ (prefixWord ++ tailWord_882456).sum := by decide
  have hdescent : baseEnd_882456 < baseStart_882456 := by decide
  rcases family_descends (prefixWord ++ tailWord_882456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882458 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_882458 : Nat := 118140960795 + 882458 * 2 ^ 59
def prefixEnd_882458 : Nat := 4983230072969 + 3 ^ 40 * 882458 * 2
def baseEnd_882458 : Nat := 302083407603609075144437

theorem tailTrace_882458 : CollatzResearch.WordTrace tailWord_882458 prefixEnd_882458 302083407603609075144437 := by
  unfold tailWord_882458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046471859253213168182007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21457258291341901781818685 8046471859253213168182007)
  ·
    refine ⟨12069707788879819752273011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046471859253213168182007 12069707788879819752273011)
    ·
      refine ⟨18104561683319729628409517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069707788879819752273011 18104561683319729628409517)
      ·
        refine ⟨6789210631244898610653569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18104561683319729628409517 6789210631244898610653569)
        ·
          refine ⟨5091907973433673957990177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6789210631244898610653569 5091907973433673957990177)
          ·
            refine ⟨3818930980075255468492633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5091907973433673957990177 3818930980075255468492633)
            ·
              refine ⟨2864198235056441601369475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818930980075255468492633 2864198235056441601369475)
              ·
                refine ⟨4296297352584662402054213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864198235056441601369475 4296297352584662402054213)
                ·
                  refine ⟨805555753609624200385165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4296297352584662402054213 805555753609624200385165)
                  ·
                    refine ⟨302083407603609075144437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805555753609624200385165 302083407603609075144437)
                    ·
                      rfl

theorem cell22_882458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_882458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882458 prefixEnd_882458 := by exact prefixLift 882458
  have htrace : WordTrace (prefixWord ++ tailWord_882458) baseStart_882458 baseEnd_882458 := by
    simpa [prefixWord, tailWord_882458, baseEnd_882458] using wordTrace_append hprefix tailTrace_882458
  have hstable : (prefixWord ++ tailWord_882458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882458).length < 2 ^ (prefixWord ++ tailWord_882458).sum := by decide
  have hdescent : baseEnd_882458 < baseStart_882458 := by decide
  rcases family_descends (prefixWord ++ tailWord_882458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882460 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_882460 : Nat := 118140960795 + 882460 * 2 ^ 59
def prefixEnd_882460 : Nat := 4983230072969 + 3 ^ 40 * 882460 * 2
def baseEnd_882460 : Nat := 100694697414827245531477

theorem tailTrace_882460 : CollatzResearch.WordTrace tailWord_882460 prefixEnd_882460 100694697414827245531477 := by
  unfold tailWord_882460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092980191502803507150417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21457306922003738009533889 16092980191502803507150417)
  ·
    refine ⟨12069735143627102630362813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16092980191502803507150417 12069735143627102630362813)
    ·
      refine ⟨4526150678860163486386055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12069735143627102630362813 4526150678860163486386055)
      ·
        refine ⟨6789226018290245229579083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526150678860163486386055 6789226018290245229579083)
        ·
          refine ⟨10183839027435367844368625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789226018290245229579083 10183839027435367844368625)
          ·
            refine ⟨7637879270576525883276469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10183839027435367844368625 7637879270576525883276469)
            ·
              refine ⟨716051181616549301557169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7637879270576525883276469 716051181616549301557169)
              ·
                refine ⟨537038386212411976167877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716051181616549301557169 537038386212411976167877)
                ·
                  refine ⟨100694697414827245531477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537038386212411976167877 100694697414827245531477)
                  ·
                    rfl

theorem cell22_882460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_882460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882460 prefixEnd_882460 := by exact prefixLift 882460
  have htrace : WordTrace (prefixWord ++ tailWord_882460) baseStart_882460 baseEnd_882460 := by
    simpa [prefixWord, tailWord_882460, baseEnd_882460] using wordTrace_append hprefix tailTrace_882460
  have hstable : (prefixWord ++ tailWord_882460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882460).length < 2 ^ (prefixWord ++ tailWord_882460).sum := by decide
  have hdescent : baseEnd_882460 < baseStart_882460 := by decide
  rcases family_descends (prefixWord ++ tailWord_882460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882567 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 5]
def baseStart_882567 : Nat := 118140960795 + 882567 * 2 ^ 59
def prefixEnd_882567 : Nat := 4983230072969 + 3 ^ 40 * 882567 * 2
def baseEnd_882567 : Nat := 100706906843723041389701

theorem tailTrace_882567 : CollatzResearch.WordTrace tailWord_882567 prefixEnd_882567 100706906843723041389701 := by
  unfold tailWord_882567
  simp only [CollatzResearch.WordTrace]
  refine ⟨32189862993617964288445955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21459908662411976192297303 32189862993617964288445955)
  ·
    refine ⟨48284794490426946432668933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32189862993617964288445955 48284794490426946432668933)
    ·
      refine ⟨9053398966955052456125425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48284794490426946432668933 9053398966955052456125425)
      ·
        refine ⟨6790049225216289342094069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9053398966955052456125425 6790049225216289342094069)
        ·
          refine ⟨636567114864027125821319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6790049225216289342094069 636567114864027125821319)
          ·
            refine ⟨954850672296040688731979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636567114864027125821319 954850672296040688731979)
            ·
              refine ⟨1432276008444061033097969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954850672296040688731979 1432276008444061033097969)
              ·
                refine ⟨1074207006333045774823477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432276008444061033097969 1074207006333045774823477)
                ·
                  refine ⟨100706906843723041389701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074207006333045774823477 100706906843723041389701)
                  ·
                    rfl

theorem cell22_882567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 5].length) (baseStart_882567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882567 prefixEnd_882567 := by exact prefixLift 882567
  have htrace : WordTrace (prefixWord ++ tailWord_882567) baseStart_882567 baseEnd_882567 := by
    simpa [prefixWord, tailWord_882567, baseEnd_882567] using wordTrace_append hprefix tailTrace_882567
  have hstable : (prefixWord ++ tailWord_882567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882567).length < 2 ^ (prefixWord ++ tailWord_882567).sum := by decide
  have hdescent : baseEnd_882567 < baseStart_882567 := by decide
  rcases family_descends (prefixWord ++ tailWord_882567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882576 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_882576 : Nat := 118140960795 + 882576 * 2 ^ 59
def prefixEnd_882576 : Nat := 4983230072969 + 3 ^ 40 * 882576 * 2
def baseEnd_882576 : Nat := 302123801415096100694075

theorem tailTrace_882576 : CollatzResearch.WordTrace tailWord_882576 prefixEnd_882576 302123801415096100694075 := by
  unfold tailWord_882576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095095625292679412761791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21460127500390239217015721 16095095625292679412761791)
  ·
    refine ⟨24142643437939019119142687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16095095625292679412761791 24142643437939019119142687)
    ·
      refine ⟨36213965156908528678714031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24142643437939019119142687 36213965156908528678714031)
      ·
        refine ⟨54320947735362793018071047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36213965156908528678714031 54320947735362793018071047)
        ·
          refine ⟨81481421603044189527106571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54320947735362793018071047 81481421603044189527106571)
          ·
            refine ⟨122222132404566284290659857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81481421603044189527106571 122222132404566284290659857)
            ·
              refine ⟨91666599303424713217994893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122222132404566284290659857 91666599303424713217994893)
              ·
                refine ⟨34374974738784267456748085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91666599303424713217994893 34374974738784267456748085)
                ·
                  refine ⟨3222653881761025074070133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34374974738784267456748085 3222653881761025074070133)
                  ·
                    refine ⟨302123801415096100694075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3222653881761025074070133 302123801415096100694075)
                    ·
                      rfl

theorem cell22_882576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_882576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882576 prefixEnd_882576 := by exact prefixLift 882576
  have htrace : WordTrace (prefixWord ++ tailWord_882576) baseStart_882576 baseEnd_882576 := by
    simpa [prefixWord, tailWord_882576, baseEnd_882576] using wordTrace_append hprefix tailTrace_882576
  have hstable : (prefixWord ++ tailWord_882576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882576).length < 2 ^ (prefixWord ++ tailWord_882576).sum := by decide
  have hdescent : baseEnd_882576 < baseStart_882576 := by decide
  rcases family_descends (prefixWord ++ tailWord_882576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882775 : List Nat := [1, 1, 3, 2, 2, 1, 6, 6]
def baseStart_882775 : Nat := 118140960795 + 882775 * 2 ^ 59
def prefixEnd_882775 : Nat := 4983230072969 + 3 ^ 40 * 882775 * 2
def baseEnd_882775 : Nat := 33576880353547323885385

theorem tailTrace_882775 : CollatzResearch.WordTrace tailWord_882775 prefixEnd_882775 33576880353547323885385 := by
  unfold tailWord_882775
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197449376864415812017779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464966251242943874678519 32197449376864415812017779)
  ·
    refine ⟨48296174065296623718026669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32197449376864415812017779 48296174065296623718026669)
    ·
      refine ⟨18111065274486233894260001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48296174065296623718026669 18111065274486233894260001)
      ·
        refine ⟨13583298955864675420695001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18111065274486233894260001 13583298955864675420695001)
        ·
          refine ⟨10187474216898506565521251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13583298955864675420695001 10187474216898506565521251)
          ·
            refine ⟨15281211325347759848281877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187474216898506565521251 15281211325347759848281877)
            ·
              refine ⟨716306780875676242888213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15281211325347759848281877 716306780875676242888213)
              ·
                refine ⟨33576880353547323885385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 716306780875676242888213 33576880353547323885385)
                ·
                  rfl

theorem cell22_882775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 6].length) (baseStart_882775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882775 prefixEnd_882775 := by exact prefixLift 882775
  have htrace : WordTrace (prefixWord ++ tailWord_882775) baseStart_882775 baseEnd_882775 := by
    simpa [prefixWord, tailWord_882775, baseEnd_882775] using wordTrace_append hprefix tailTrace_882775
  have hstable : (prefixWord ++ tailWord_882775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882775).length < 2 ^ (prefixWord ++ tailWord_882775).sum := by decide
  have hdescent : baseEnd_882775 < baseStart_882775 := by decide
  rcases family_descends (prefixWord ++ tailWord_882775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882781 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 4]
def baseStart_882781 : Nat := 118140960795 + 882781 * 2 ^ 59
def prefixEnd_882781 : Nat := 4983230072969 + 3 ^ 40 * 882781 * 2
def baseEnd_882781 : Nat := 100731325701514633106149

theorem tailTrace_882781 : CollatzResearch.WordTrace tailWord_882781 prefixEnd_882781 100731325701514633106149 := by
  unfold tailWord_882781
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197668214842678836736197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21465112143228452557824131 32197668214842678836736197)
  ·
    refine ⟨6037062790283002281888037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32197668214842678836736197 6037062790283002281888037)
    ·
      refine ⟨1131949273178062927854007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6037062790283002281888037 1131949273178062927854007)
      ·
        refine ⟨1697923909767094391781011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131949273178062927854007 1697923909767094391781011)
        ·
          refine ⟨2546885864650641587671517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697923909767094391781011 2546885864650641587671517)
          ·
            refine ⟨955082199243990595376819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2546885864650641587671517 955082199243990595376819)
            ·
              refine ⟨1432623298865985893065229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955082199243990595376819 1432623298865985893065229)
              ·
                refine ⟨537233737074744709899461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432623298865985893065229 537233737074744709899461)
                ·
                  refine ⟨100731325701514633106149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537233737074744709899461 100731325701514633106149)
                  ·
                    rfl

theorem cell22_882781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_882781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882781 prefixEnd_882781 := by exact prefixLift 882781
  have htrace : WordTrace (prefixWord ++ tailWord_882781) baseStart_882781 baseEnd_882781 := by
    simpa [prefixWord, tailWord_882781, baseEnd_882781] using wordTrace_append hprefix tailTrace_882781
  have hstable : (prefixWord ++ tailWord_882781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882781).length < 2 ^ (prefixWord ++ tailWord_882781).sum := by decide
  have hdescent : baseEnd_882781 < baseStart_882781 := by decide
  rcases family_descends (prefixWord ++ tailWord_882781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882807 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 3, 3]
def baseStart_882807 : Nat := 118140960795 + 882807 * 2 ^ 59
def prefixEnd_882807 : Nat := 4983230072969 + 3 ^ 40 * 882807 * 2
def baseEnd_882807 : Nat := 302202877435888498168367

theorem tailTrace_882807 : CollatzResearch.WordTrace tailWord_882807 prefixEnd_882807 302202877435888498168367 := by
  unfold tailWord_882807
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198616512748485277182675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21465744341832323518121783 32198616512748485277182675)
  ·
    refine ⟨48297924769122727915774013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32198616512748485277182675 48297924769122727915774013)
    ·
      refine ⟨18111721788421022968415255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48297924769122727915774013 18111721788421022968415255)
      ·
        refine ⟨27167582682631534452622883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18111721788421022968415255 27167582682631534452622883)
        ·
          refine ⟨40751374023947301678934325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27167582682631534452622883 40751374023947301678934325)
          ·
            refine ⟨3820441314745059532400093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40751374023947301678934325 3820441314745059532400093)
            ·
              refine ⟨1432665493029397324650035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3820441314745059532400093 1432665493029397324650035)
              ·
                refine ⟨2148998239544095986975053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432665493029397324650035 2148998239544095986975053)
                ·
                  refine ⟨805874339829035995115645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2148998239544095986975053 805874339829035995115645)
                  ·
                    refine ⟨302202877435888498168367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805874339829035995115645 302202877435888498168367)
                    ·
                      rfl

theorem cell22_882807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_882807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882807 prefixEnd_882807 := by exact prefixLift 882807
  have htrace : WordTrace (prefixWord ++ tailWord_882807) baseStart_882807 baseEnd_882807 := by
    simpa [prefixWord, tailWord_882807, baseEnd_882807] using wordTrace_append hprefix tailTrace_882807
  have hstable : (prefixWord ++ tailWord_882807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882807).length < 2 ^ (prefixWord ++ tailWord_882807).sum := by decide
  have hdescent : baseEnd_882807 < baseStart_882807 := by decide
  rcases family_descends (prefixWord ++ tailWord_882807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882858 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_882858 : Nat := 118140960795 + 882858 * 2 ^ 59
def prefixEnd_882858 : Nat := 4983230072969 + 3 ^ 40 * 882858 * 2
def baseEnd_882858 : Nat := 302220335778141365143211

theorem tailTrace_882858 : CollatzResearch.WordTrace tailWord_882858 prefixEnd_882858 302220335778141365143211 := by
  unfold tailWord_882858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050119158890930246822307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21466984423709147324859485 8050119158890930246822307)
  ·
    refine ⟨12075178738336395370233461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050119158890930246822307 12075178738336395370233461)
    ·
      refine ⟨1132048006719037065959387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12075178738336395370233461 1132048006719037065959387)
      ·
        refine ⟨1698072010078555598939081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132048006719037065959387 1698072010078555598939081)
        ·
          refine ⟨1273554007558916699204311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698072010078555598939081 1273554007558916699204311)
          ·
            refine ⟨1910331011338375048806467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273554007558916699204311 1910331011338375048806467)
            ·
              refine ⟨2865496517007562573209701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910331011338375048806467 2865496517007562573209701)
              ·
                refine ⟨537280596938917982476819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2865496517007562573209701 537280596938917982476819)
                ·
                  refine ⟨805920895408376973715229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537280596938917982476819 805920895408376973715229)
                  ·
                    refine ⟨302220335778141365143211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 805920895408376973715229 302220335778141365143211)
                    ·
                      rfl

theorem cell22_882858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_882858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882858 prefixEnd_882858 := by exact prefixLift 882858
  have htrace : WordTrace (prefixWord ++ tailWord_882858) baseStart_882858 baseEnd_882858 := by
    simpa [prefixWord, tailWord_882858, baseEnd_882858] using wordTrace_append hprefix tailTrace_882858
  have hstable : (prefixWord ++ tailWord_882858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882858).length < 2 ^ (prefixWord ++ tailWord_882858).sum := by decide
  have hdescent : baseEnd_882858 < baseStart_882858 := by decide
  rcases family_descends (prefixWord ++ tailWord_882858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882869 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_882869 : Nat := 118140960795 + 882869 * 2 ^ 59
def prefixEnd_882869 : Nat := 4983230072969 + 3 ^ 40 * 882869 * 2
def baseEnd_882869 : Nat := 302224101302941003118177

theorem tailTrace_882869 : CollatzResearch.WordTrace tailWord_882869 prefixEnd_882869 302224101302941003118177 := by
  unfold tailWord_882869
  simp only [CollatzResearch.WordTrace]
  refine ⟨32200877838523869865939661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21467251892349246577293107 32200877838523869865939661)
  ·
    refine ⟨12075329189446451199727373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32200877838523869865939661 12075329189446451199727373)
    ·
      refine ⟨4528248446042419199897765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12075329189446451199727373 4528248446042419199897765)
      ·
        refine ⟨849046583632953599980831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4528248446042419199897765 849046583632953599980831)
        ·
          refine ⟨1273569875449430399971247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849046583632953599980831 1273569875449430399971247)
          ·
            refine ⟨1910354813174145599956871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273569875449430399971247 1910354813174145599956871)
            ·
              refine ⟨2865532219761218399935307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910354813174145599956871 2865532219761218399935307)
              ·
                refine ⟨4298298329641827599902961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865532219761218399935307 4298298329641827599902961)
                ·
                  refine ⟨3223723747231370699927221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4298298329641827599902961 3223723747231370699927221)
                  ·
                    refine ⟨302224101302941003118177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3223723747231370699927221 302224101302941003118177)
                    ·
                      rfl

theorem cell22_882869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_882869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882869 prefixEnd_882869 := by exact prefixLift 882869
  have htrace : WordTrace (prefixWord ++ tailWord_882869) baseStart_882869 baseEnd_882869 := by
    simpa [prefixWord, tailWord_882869, baseEnd_882869] using wordTrace_append hprefix tailTrace_882869
  have hstable : (prefixWord ++ tailWord_882869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882869).length < 2 ^ (prefixWord ++ tailWord_882869).sum := by decide
  have hdescent : baseEnd_882869 < baseStart_882869 := by decide
  rcases family_descends (prefixWord ++ tailWord_882869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882895 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_882895 : Nat := 118140960795 + 882895 * 2 ^ 59
def prefixEnd_882895 : Nat := 4983230072969 + 3 ^ 40 * 882895 * 2
def baseEnd_882895 : Nat := 302233001634285601968097

theorem tailTrace_882895 : CollatzResearch.WordTrace tailWord_882895 prefixEnd_882895 302233001634285601968097 := by
  unfold tailWord_882895
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201826136429676306386139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21467884090953117537590759 32201826136429676306386139)
  ·
    refine ⟨48302739204644514459579209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32201826136429676306386139 48302739204644514459579209)
    ·
      refine ⟨36227054403483385844684407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48302739204644514459579209 36227054403483385844684407)
      ·
        refine ⟨54340581605225078767026611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36227054403483385844684407 54340581605225078767026611)
        ·
          refine ⟨81510872407837618150539917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54340581605225078767026611 81510872407837618150539917)
          ·
            refine ⟨30566577152939106806452469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81510872407837618150539917 30566577152939106806452469)
            ·
              refine ⟨2865616608088041263104919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30566577152939106806452469 2865616608088041263104919)
              ·
                refine ⟨4298424912132061894657379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865616608088041263104919 4298424912132061894657379)
                ·
                  refine ⟨6447637368198092841986069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298424912132061894657379 6447637368198092841986069)
                  ·
                    refine ⟨302233001634285601968097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6447637368198092841986069 302233001634285601968097)
                    ·
                      rfl

theorem cell22_882895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_882895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882895 prefixEnd_882895 := by exact prefixLift 882895
  have htrace : WordTrace (prefixWord ++ tailWord_882895) baseStart_882895 baseEnd_882895 := by
    simpa [prefixWord, tailWord_882895, baseEnd_882895] using wordTrace_append hprefix tailTrace_882895
  have hstable : (prefixWord ++ tailWord_882895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882895).length < 2 ^ (prefixWord ++ tailWord_882895).sum := by decide
  have hdescent : baseEnd_882895 < baseStart_882895 := by decide
  rcases family_descends (prefixWord ++ tailWord_882895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882942 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_882942 : Nat := 118140960795 + 882942 * 2 ^ 59
def prefixEnd_882942 : Nat := 4983230072969 + 3 ^ 40 * 882942 * 2
def baseEnd_882942 : Nat := 302249090694793146042953

theorem tailTrace_882942 : CollatzResearch.WordTrace tailWord_882942 prefixEnd_882942 302249090694793146042953 := by
  unfold tailWord_882942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025442545907425416668385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21469026911506268888898053 4025442545907425416668385)
  ·
    refine ⟨3019081909430569062501289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4025442545907425416668385 3019081909430569062501289)
    ·
      refine ⟨2264311432072926796875967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3019081909430569062501289 2264311432072926796875967)
      ·
        refine ⟨3396467148109390195313951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264311432072926796875967 3396467148109390195313951)
        ·
          refine ⟨5094700722164085292970927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396467148109390195313951 5094700722164085292970927)
          ·
            refine ⟨7642051083246127939456391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094700722164085292970927 7642051083246127939456391)
            ·
              refine ⟨11463076624869191909184587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7642051083246127939456391 11463076624869191909184587)
              ·
                refine ⟨17194614937303787863776881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11463076624869191909184587 17194614937303787863776881)
                ·
                  refine ⟨12895961202977840897832661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17194614937303787863776881 12895961202977840897832661)
                  ·
                    refine ⟨302249090694793146042953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12895961202977840897832661 302249090694793146042953)
                    ·
                      rfl

theorem cell22_882942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_882942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882942 prefixEnd_882942 := by exact prefixLift 882942
  have htrace : WordTrace (prefixWord ++ tailWord_882942) baseStart_882942 baseEnd_882942 := by
    simpa [prefixWord, tailWord_882942, baseEnd_882942] using wordTrace_append hprefix tailTrace_882942
  have hstable : (prefixWord ++ tailWord_882942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882942).length < 2 ^ (prefixWord ++ tailWord_882942).sum := by decide
  have hdescent : baseEnd_882942 < baseStart_882942 := by decide
  rcases family_descends (prefixWord ++ tailWord_882942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882955 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 9]
def baseStart_882955 : Nat := 118140960795 + 882955 * 2 ^ 59
def prefixEnd_882955 : Nat := 4983230072969 + 3 ^ 40 * 882955 * 2
def baseEnd_882955 : Nat := 100751180286821815155971

theorem tailTrace_882955 : CollatzResearch.WordTrace tailWord_882955 prefixEnd_882955 100751180286821815155971 := by
  unfold tailWord_882955
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204014516212306553570319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21469343010808204369046879 32204014516212306553570319)
  ·
    refine ⟨48306021774318459830355479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32204014516212306553570319 48306021774318459830355479)
    ·
      refine ⟨72459032661477689745533219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48306021774318459830355479 72459032661477689745533219)
      ·
        refine ⟨108688548992216534618299829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72459032661477689745533219 108688548992216534618299829)
        ·
          refine ⟨10189551468020300120465609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108688548992216534618299829 10189551468020300120465609)
          ·
            refine ⟨7642163601015225090349207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10189551468020300120465609 7642163601015225090349207)
            ·
              refine ⟨11463245401522837635523811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7642163601015225090349207 11463245401522837635523811)
              ·
                refine ⟨17194868102284256453285717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11463245401522837635523811 17194868102284256453285717)
                ·
                  refine ⟨100751180286821815155971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17194868102284256453285717 100751180286821815155971)
                  ·
                    rfl

theorem cell22_882955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_882955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882955 prefixEnd_882955 := by exact prefixLift 882955
  have htrace : WordTrace (prefixWord ++ tailWord_882955) baseStart_882955 baseEnd_882955 := by
    simpa [prefixWord, tailWord_882955, baseEnd_882955] using wordTrace_append hprefix tailTrace_882955
  have hstable : (prefixWord ++ tailWord_882955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882955).length < 2 ^ (prefixWord ++ tailWord_882955).sum := by decide
  have hdescent : baseEnd_882955 < baseStart_882955 := by decide
  rcases family_descends (prefixWord ++ tailWord_882955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882972 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_882972 : Nat := 118140960795 + 882972 * 2 ^ 59
def prefixEnd_882972 : Nat := 4983230072969 + 3 ^ 40 * 882972 * 2
def baseEnd_882972 : Nat := 100753120102627689264287

theorem tailTrace_882972 : CollatzResearch.WordTrace tailWord_882972 prefixEnd_882972 100753120102627689264287 := by
  unfold tailWord_882972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102317278575359228469585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21469756371433812304626113 16102317278575359228469585)
  ·
    refine ⟨12076737958931519421352189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16102317278575359228469585 12076737958931519421352189)
    ·
      refine ⟨4528776734599319783007071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12076737958931519421352189 4528776734599319783007071)
      ·
        refine ⟨6793165101898979674510607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528776734599319783007071 6793165101898979674510607)
        ·
          refine ⟨10189747652848469511765911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793165101898979674510607 10189747652848469511765911)
          ·
            refine ⟨15284621479272704267648867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189747652848469511765911 15284621479272704267648867)
            ·
              refine ⟨22926932218909056401473301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284621479272704267648867 22926932218909056401473301)
              ·
                refine ⟨1074699947761362018819061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22926932218909056401473301 1074699947761362018819061)
                ·
                  refine ⟨100753120102627689264287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074699947761362018819061 100753120102627689264287)
                  ·
                    rfl

theorem cell22_882972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_882972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882972 prefixEnd_882972 := by exact prefixLift 882972
  have htrace : WordTrace (prefixWord ++ tailWord_882972) baseStart_882972 baseEnd_882972 := by
    simpa [prefixWord, tailWord_882972, baseEnd_882972] using wordTrace_append hprefix tailTrace_882972
  have hstable : (prefixWord ++ tailWord_882972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882972).length < 2 ^ (prefixWord ++ tailWord_882972).sum := by decide
  have hdescent : baseEnd_882972 < baseStart_882972 := by decide
  rcases family_descends (prefixWord ++ tailWord_882972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882976 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_882976 : Nat := 118140960795 + 882976 * 2 ^ 59
def prefixEnd_882976 : Nat := 4983230072969 + 3 ^ 40 * 882976 * 2
def baseEnd_882976 : Nat := 302260729589628390692849

theorem tailTrace_882976 : CollatzResearch.WordTrace tailWord_882976 prefixEnd_882976 302260729589628390692849 := by
  unfold tailWord_882976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102390224568113570042391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21469853632757484760056521 16102390224568113570042391)
  ·
    refine ⟨24153585336852170355063587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16102390224568113570042391 24153585336852170355063587)
    ·
      refine ⟨36230378005278255532595381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24153585336852170355063587 36230378005278255532595381)
      ·
        refine ⟨3396597937994836456180817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36230378005278255532595381 3396597937994836456180817)
        ·
          refine ⟨2547448453496127342135613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3396597937994836456180817 2547448453496127342135613)
          ·
            refine ⟨955293170061047753300855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2547448453496127342135613 955293170061047753300855)
            ·
              refine ⟨1432939755091571629951283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955293170061047753300855 1432939755091571629951283)
              ·
                refine ⟨2149409632637357444926925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432939755091571629951283 2149409632637357444926925)
                ·
                  refine ⟨806028612239009041847597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2149409632637357444926925 806028612239009041847597)
                  ·
                    refine ⟨302260729589628390692849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806028612239009041847597 302260729589628390692849)
                    ·
                      rfl

theorem cell22_882976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_882976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_882976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_882976 prefixEnd_882976 := by exact prefixLift 882976
  have htrace : WordTrace (prefixWord ++ tailWord_882976) baseStart_882976 baseEnd_882976 := by
    simpa [prefixWord, tailWord_882976, baseEnd_882976] using wordTrace_append hprefix tailTrace_882976
  have hstable : (prefixWord ++ tailWord_882976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882976).length < 2 ^ (prefixWord ++ tailWord_882976).sum := by decide
  have hdescent : baseEnd_882976 < baseStart_882976 := by decide
  rcases family_descends (prefixWord ++ tailWord_882976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883049 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_883049 : Nat := 118140960795 + 883049 * 2 ^ 59
def prefixEnd_883049 : Nat := 4983230072969 + 3 ^ 40 * 883049 * 2
def baseEnd_883049 : Nat := 302285718981480533617625

theorem tailTrace_883049 : CollatzResearch.WordTrace tailWord_883049 prefixEnd_883049 302285718981480533617625 := by
  unfold tailWord_883049
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207442977871760607492201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21471628651914507071661467 32207442977871760607492201)
  ·
    refine ⟨24155582233403820455619151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32207442977871760607492201 24155582233403820455619151)
    ·
      refine ⟨36233373350105730683428727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24155582233403820455619151 36233373350105730683428727)
      ·
        refine ⟨54350060025158596025143091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36233373350105730683428727 54350060025158596025143091)
        ·
          refine ⟨81525090037737894037714637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54350060025158596025143091 81525090037737894037714637)
          ·
            refine ⟨30571908764151710264142989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81525090037737894037714637 30571908764151710264142989)
            ·
              refine ⟨11464465786556891349053621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30571908764151710264142989 11464465786556891349053621)
              ·
                refine ⟨1074793667489708563973777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11464465786556891349053621 1074793667489708563973777)
                ·
                  refine ⟨806095250617281422980333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1074793667489708563973777 806095250617281422980333)
                  ·
                    refine ⟨302285718981480533617625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806095250617281422980333 302285718981480533617625)
                    ·
                      rfl

theorem cell22_883049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_883049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883049 prefixEnd_883049 := by exact prefixLift 883049
  have htrace : WordTrace (prefixWord ++ tailWord_883049) baseStart_883049 baseEnd_883049 := by
    simpa [prefixWord, tailWord_883049, baseEnd_883049] using wordTrace_append hprefix tailTrace_883049
  have hstable : (prefixWord ++ tailWord_883049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883049).length < 2 ^ (prefixWord ++ tailWord_883049).sum := by decide
  have hdescent : baseEnd_883049 < baseStart_883049 := by decide
  rcases family_descends (prefixWord ++ tailWord_883049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883111 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 3, 3]
def baseStart_883111 : Nat := 118140960795 + 883111 * 2 ^ 59
def prefixEnd_883111 : Nat := 4983230072969 + 3 ^ 40 * 883111 * 2
def baseEnd_883111 : Nat := 302306942848533038567435

theorem tailTrace_883111 : CollatzResearch.WordTrace tailWord_883111 prefixEnd_883111 302306942848533038567435 := by
  unfold tailWord_883111
  simp only [CollatzResearch.WordTrace]
  refine ⟨32209704303647145196249187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21473136202431430130832791 32209704303647145196249187)
  ·
    refine ⟨48314556455470717794373781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32209704303647145196249187 48314556455470717794373781)
    ·
      refine ⟨2264744833850189896611271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48314556455470717794373781 2264744833850189896611271)
      ·
        refine ⟨3397117250775284844916907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264744833850189896611271 3397117250775284844916907)
        ·
          refine ⟨5095675876162927267375361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397117250775284844916907 5095675876162927267375361)
          ·
            refine ⟨3821756907122195450531521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095675876162927267375361 3821756907122195450531521)
            ·
              refine ⟨2866317680341646587898641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821756907122195450531521 2866317680341646587898641)
              ·
                refine ⟨2149738260256234940923981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866317680341646587898641 2149738260256234940923981)
                ·
                  refine ⟨806151847596088102846493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2149738260256234940923981 806151847596088102846493)
                  ·
                    refine ⟨302306942848533038567435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806151847596088102846493 302306942848533038567435)
                    ·
                      rfl

theorem cell22_883111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_883111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883111 prefixEnd_883111 := by exact prefixLift 883111
  have htrace : WordTrace (prefixWord ++ tailWord_883111) baseStart_883111 baseEnd_883111 := by
    simpa [prefixWord, tailWord_883111, baseEnd_883111] using wordTrace_append hprefix tailTrace_883111
  have hstable : (prefixWord ++ tailWord_883111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883111).length < 2 ^ (prefixWord ++ tailWord_883111).sum := by decide
  have hdescent : baseEnd_883111 < baseStart_883111 := by decide
  rcases family_descends (prefixWord ++ tailWord_883111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883171 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 3, 4]
def baseStart_883171 : Nat := 118140960795 + 883171 * 2 ^ 59
def prefixEnd_883171 : Nat := 4983230072969 + 3 ^ 40 * 883171 * 2
def baseEnd_883171 : Nat := 302327482074712882067251

theorem tailTrace_883171 : CollatzResearch.WordTrace tailWord_883171 prefixEnd_883171 302327482074712882067251 := by
  unfold tailWord_883171
  simp only [CollatzResearch.WordTrace]
  refine ⟨32211892683429775443433367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21474595122286516962288911 32211892683429775443433367)
  ·
    refine ⟨48317839025144663165150051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32211892683429775443433367 48317839025144663165150051)
    ·
      refine ⟨72476758537716994747725077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48317839025144663165150051 72476758537716994747725077)
      ·
        refine ⟨3397348056455484128799613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72476758537716994747725077 3397348056455484128799613)
        ·
          refine ⟨1274005521170806548299855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3397348056455484128799613 1274005521170806548299855)
          ·
            refine ⟨1911008281756209822449783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274005521170806548299855 1911008281756209822449783)
            ·
              refine ⟨2866512422634314733674675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911008281756209822449783 2866512422634314733674675)
              ·
                refine ⟨4299768633951472100512013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866512422634314733674675 4299768633951472100512013)
                ·
                  refine ⟨1612413237731802037692005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4299768633951472100512013 1612413237731802037692005)
                  ·
                    refine ⟨302327482074712882067251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612413237731802037692005 302327482074712882067251)
                    ·
                      rfl

theorem cell22_883171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_883171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883171 prefixEnd_883171 := by exact prefixLift 883171
  have htrace : WordTrace (prefixWord ++ tailWord_883171) baseStart_883171 baseEnd_883171 := by
    simpa [prefixWord, tailWord_883171, baseEnd_883171] using wordTrace_append hprefix tailTrace_883171
  have hstable : (prefixWord ++ tailWord_883171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883171).length < 2 ^ (prefixWord ++ tailWord_883171).sum := by decide
  have hdescent : baseEnd_883171 < baseStart_883171 := by decide
  rcases family_descends (prefixWord ++ tailWord_883171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883184 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_883184 : Nat := 118140960795 + 883184 * 2 ^ 59
def prefixEnd_883184 : Nat := 4983230072969 + 3 ^ 40 * 883184 * 2
def baseEnd_883184 : Nat := 302331932240385181492211

theorem tailTrace_883184 : CollatzResearch.WordTrace tailWord_883184 prefixEnd_883184 302331932240385181492211 := by
  unfold tailWord_883184
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106183416191339331828303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21474911221588452442437737 16106183416191339331828303)
  ·
    refine ⟨24159275124287008997742455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16106183416191339331828303 24159275124287008997742455)
    ·
      refine ⟨36238912686430513496613683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24159275124287008997742455 36238912686430513496613683)
      ·
        refine ⟨54358369029645770244920525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36238912686430513496613683 54358369029645770244920525)
        ·
          refine ⟨20384388386117163841845197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54358369029645770244920525 20384388386117163841845197)
          ·
            refine ⟨7644145644793936440691949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20384388386117163841845197 7644145644793936440691949)
            ·
              refine ⟨2866554616797726165259481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7644145644793936440691949 2866554616797726165259481)
              ·
                refine ⟨2149915962598294623944611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866554616797726165259481 2149915962598294623944611)
                ·
                  refine ⟨3224873943897441935916917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149915962598294623944611 3224873943897441935916917)
                  ·
                    refine ⟨302331932240385181492211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3224873943897441935916917 302331932240385181492211)
                    ·
                      rfl

theorem cell22_883184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_883184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883184 prefixEnd_883184 := by exact prefixLift 883184
  have htrace : WordTrace (prefixWord ++ tailWord_883184) baseStart_883184 baseEnd_883184 := by
    simpa [prefixWord, tailWord_883184, baseEnd_883184] using wordTrace_append hprefix tailTrace_883184
  have hstable : (prefixWord ++ tailWord_883184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883184).length < 2 ^ (prefixWord ++ tailWord_883184).sum := by decide
  have hdescent : baseEnd_883184 < baseStart_883184 := by decide
  rcases family_descends (prefixWord ++ tailWord_883184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883199 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_883199 : Nat := 118140960795 + 883199 * 2 ^ 59
def prefixEnd_883199 : Nat := 4983230072969 + 3 ^ 40 * 883199 * 2
def baseEnd_883199 : Nat := 302337067046930142367165

theorem tailTrace_883199 : CollatzResearch.WordTrace tailWord_883199 prefixEnd_883199 302337067046930142367165 := by
  unfold tailWord_883199
  simp only [CollatzResearch.WordTrace]
  refine ⟨32212913927328336225452651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21475275951552224150301767 32212913927328336225452651)
  ·
    refine ⟨48319370890992504338178977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32212913927328336225452651 48319370890992504338178977)
    ·
      refine ⟨36239528168244378253634233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48319370890992504338178977 36239528168244378253634233)
      ·
        refine ⟨27179646126183283690225675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36239528168244378253634233 27179646126183283690225675)
        ·
          refine ⟨40769469189274925535338513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27179646126183283690225675 40769469189274925535338513)
          ·
            refine ⟨30577101891956194151503885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40769469189274925535338513 30577101891956194151503885)
            ·
              refine ⟨11466413209483572806813957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30577101891956194151503885 11466413209483572806813957)
              ·
                refine ⟨2149952476778169901277617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11466413209483572806813957 2149952476778169901277617)
                ·
                  refine ⟨1612464357583627425958213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2149952476778169901277617 1612464357583627425958213)
                  ·
                    refine ⟨302337067046930142367165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612464357583627425958213 302337067046930142367165)
                    ·
                      rfl

theorem cell22_883199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_883199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883199 prefixEnd_883199 := by exact prefixLift 883199
  have htrace : WordTrace (prefixWord ++ tailWord_883199) baseStart_883199 baseEnd_883199 := by
    simpa [prefixWord, tailWord_883199, baseEnd_883199] using wordTrace_append hprefix tailTrace_883199
  have hstable : (prefixWord ++ tailWord_883199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883199).length < 2 ^ (prefixWord ++ tailWord_883199).sum := by decide
  have hdescent : baseEnd_883199 < baseStart_883199 := by decide
  rcases family_descends (prefixWord ++ tailWord_883199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883239 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 1, 4]
def baseStart_883239 : Nat := 118140960795 + 883239 * 2 ^ 59
def prefixEnd_883239 : Nat := 4983230072969 + 3 ^ 40 * 883239 * 2
def baseEnd_883239 : Nat := 302350759864383371367043

theorem tailTrace_883239 : CollatzResearch.WordTrace tailWord_883239 prefixEnd_883239 302350759864383371367043 := by
  unfold tailWord_883239
  simp only [CollatzResearch.WordTrace]
  refine ⟨32214372847183423056908771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21476248564788948704605847 32214372847183423056908771)
  ·
    refine ⟨48321559270775134585363157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32214372847183423056908771 48321559270775134585363157)
    ·
      refine ⟨1132536545408792216844449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48321559270775134585363157 1132536545408792216844449)
      ·
        refine ⟨849402409056594162633337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1132536545408792216844449 849402409056594162633337)
        ·
          refine ⟨637051806792445621975003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849402409056594162633337 637051806792445621975003)
          ·
            refine ⟨955577710188668432962505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637051806792445621975003 955577710188668432962505)
            ·
              refine ⟨716683282641501324721879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955577710188668432962505 716683282641501324721879)
              ·
                refine ⟨1075024923962251987082819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716683282641501324721879 1075024923962251987082819)
                ·
                  refine ⟨1612537385943377980624229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075024923962251987082819 1612537385943377980624229)
                  ·
                    refine ⟨302350759864383371367043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1612537385943377980624229 302350759864383371367043)
                    ·
                      rfl

theorem cell22_883239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_883239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883239 prefixEnd_883239 := by exact prefixLift 883239
  have htrace : WordTrace (prefixWord ++ tailWord_883239) baseStart_883239 baseEnd_883239 := by
    simpa [prefixWord, tailWord_883239, baseEnd_883239] using wordTrace_append hprefix tailTrace_883239
  have hstable : (prefixWord ++ tailWord_883239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883239).length < 2 ^ (prefixWord ++ tailWord_883239).sum := by decide
  have hdescent : baseEnd_883239 < baseStart_883239 := by decide
  rcases family_descends (prefixWord ++ tailWord_883239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883263 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 1, 3]
def baseStart_883263 : Nat := 118140960795 + 883263 * 2 ^ 59
def prefixEnd_883263 : Nat := 4983230072969 + 3 ^ 40 * 883263 * 2
def baseEnd_883263 : Nat := 302358975554855308766969

theorem tailTrace_883263 : CollatzResearch.WordTrace tailWord_883263 prefixEnd_883263 302358975554855308766969 := by
  unfold tailWord_883263
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215248199096475155782443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21476832132730983437188295 32215248199096475155782443)
  ·
    refine ⟨48322872298644712733673665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32215248199096475155782443 48322872298644712733673665)
    ·
      refine ⟨36242154223983534550255249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48322872298644712733673665 36242154223983534550255249)
      ·
        refine ⟨27181615667987650912691437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36242154223983534550255249 27181615667987650912691437)
        ·
          refine ⟨10193105875495369092259289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27181615667987650912691437 10193105875495369092259289)
          ·
            refine ⟨7644829406621526819194467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10193105875495369092259289 7644829406621526819194467)
            ·
              refine ⟨11467244109932290228791701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644829406621526819194467 11467244109932290228791701)
              ·
                refine ⟨537527067653076104474611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11467244109932290228791701 537527067653076104474611)
                ·
                  refine ⟨806290601479614156711917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537527067653076104474611 806290601479614156711917)
                  ·
                    refine ⟨302358975554855308766969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806290601479614156711917 302358975554855308766969)
                    ·
                      rfl

theorem cell22_883263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_883263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883263 prefixEnd_883263 := by exact prefixLift 883263
  have htrace : WordTrace (prefixWord ++ tailWord_883263) baseStart_883263 baseEnd_883263 := by
    simpa [prefixWord, tailWord_883263, baseEnd_883263] using wordTrace_append hprefix tailTrace_883263
  have hstable : (prefixWord ++ tailWord_883263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883263).length < 2 ^ (prefixWord ++ tailWord_883263).sum := by decide
  have hdescent : baseEnd_883263 < baseStart_883263 := by decide
  rcases family_descends (prefixWord ++ tailWord_883263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883321 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 6]
def baseStart_883321 : Nat := 118140960795 + 883321 * 2 ^ 59
def prefixEnd_883321 : Nat := 4983230072969 + 3 ^ 40 * 883321 * 2
def baseEnd_883321 : Nat := 100792943380054163605597

theorem tailTrace_883321 : CollatzResearch.WordTrace tailWord_883321 prefixEnd_883321 100792943380054163605597 := by
  unfold tailWord_883321
  simp only [CollatzResearch.WordTrace]
  refine ⟨32217363632886351061393817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21478242421924234040929211 32217363632886351061393817)
  ·
    refine ⟨24163022724664763296045363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32217363632886351061393817 24163022724664763296045363)
    ·
      refine ⟨36244534086997144944068045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24163022724664763296045363 36244534086997144944068045)
      ·
        refine ⟨13591700282623929354025517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36244534086997144944068045 13591700282623929354025517)
        ·
          refine ⟨5096887605983973507759569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13591700282623929354025517 5096887605983973507759569)
          ·
            refine ⟨3822665704487980130819677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5096887605983973507759569 3822665704487980130819677)
            ·
              refine ⟨1433499639182992549057379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3822665704487980130819677 1433499639182992549057379)
              ·
                refine ⟨2150249458774488823586069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433499639182992549057379 2150249458774488823586069)
                ·
                  refine ⟨100792943380054163605597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2150249458774488823586069 100792943380054163605597)
                  ·
                    rfl

theorem cell22_883321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_883321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883321 prefixEnd_883321 := by exact prefixLift 883321
  have htrace : WordTrace (prefixWord ++ tailWord_883321) baseStart_883321 baseEnd_883321 := by
    simpa [prefixWord, tailWord_883321, baseEnd_883321] using wordTrace_append hprefix tailTrace_883321
  have hstable : (prefixWord ++ tailWord_883321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883321).length < 2 ^ (prefixWord ++ tailWord_883321).sum := by decide
  have hdescent : baseEnd_883321 < baseStart_883321 := by decide
  rcases family_descends (prefixWord ++ tailWord_883321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883383 : List Nat := [1, 1, 3, 1, 6, 2, 1, 7]
def baseStart_883383 : Nat := 118140960795 + 883383 * 2 ^ 59
def prefixEnd_883383 : Nat := 4983230072969 + 3 ^ 40 * 883383 * 2
def baseEnd_883383 : Nat := 33600006000801666196289

theorem tailTrace_883383 : CollatzResearch.WordTrace tailWord_883383 prefixEnd_883383 33600006000801666196289 := by
  unfold tailWord_883383
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219624958661735650150803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21479749972441157100100535 32219624958661735650150803)
  ·
    refine ⟨48329437437992603475226205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32219624958661735650150803 48329437437992603475226205)
    ·
      refine ⟨18123539039247226303209827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48329437437992603475226205 18123539039247226303209827)
      ·
        refine ⟨27185308558870839454814741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18123539039247226303209827 27185308558870839454814741)
        ·
          refine ⟨1274311338697070599444441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27185308558870839454814741 1274311338697070599444441)
          ·
            refine ⟨955733504022802949583331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1274311338697070599444441 955733504022802949583331)
            ·
              refine ⟨1433600256034204424374997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955733504022802949583331 1433600256034204424374997)
              ·
                refine ⟨33600006000801666196289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1433600256034204424374997 33600006000801666196289)
                ·
                  rfl

theorem cell22_883383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 7].length) (baseStart_883383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883383 prefixEnd_883383 := by exact prefixLift 883383
  have htrace : WordTrace (prefixWord ++ tailWord_883383) baseStart_883383 baseEnd_883383 := by
    simpa [prefixWord, tailWord_883383, baseEnd_883383] using wordTrace_append hprefix tailTrace_883383
  have hstable : (prefixWord ++ tailWord_883383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883383).length < 2 ^ (prefixWord ++ tailWord_883383).sum := by decide
  have hdescent : baseEnd_883383 < baseStart_883383 := by decide
  rcases family_descends (prefixWord ++ tailWord_883383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883415 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 1, 3]
def baseStart_883415 : Nat := 118140960795 + 883415 * 2 ^ 59
def prefixEnd_883415 : Nat := 4983230072969 + 3 ^ 40 * 883415 * 2
def baseEnd_883415 : Nat := 302411008261177578966503

theorem tailTrace_883415 : CollatzResearch.WordTrace tailWord_883415 prefixEnd_883415 302411008261177578966503 := by
  unfold tailWord_883415
  simp only [CollatzResearch.WordTrace]
  refine ⟨32220792094545805115315699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21480528063030536743543799 32220792094545805115315699)
  ·
    refine ⟨48331188141818707672973549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32220792094545805115315699 48331188141818707672973549)
    ·
      refine ⟨18124195553182015377365081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48331188141818707672973549 18124195553182015377365081)
      ·
        refine ⟨13593146664886511533023811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18124195553182015377365081 13593146664886511533023811)
        ·
          refine ⟨20389719997329767299535717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593146664886511533023811 20389719997329767299535717)
          ·
            refine ⟨3823072499499331368662947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20389719997329767299535717 3823072499499331368662947)
            ·
              refine ⟨5734608749248997052994421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823072499499331368662947 5734608749248997052994421)
              ·
                refine ⟨537619570242093473718227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5734608749248997052994421 537619570242093473718227)
                ·
                  refine ⟨806429355363140210577341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537619570242093473718227 806429355363140210577341)
                  ·
                    refine ⟨302411008261177578966503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806429355363140210577341 302411008261177578966503)
                    ·
                      rfl

theorem cell22_883415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_883415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883415 prefixEnd_883415 := by exact prefixLift 883415
  have htrace : WordTrace (prefixWord ++ tailWord_883415) baseStart_883415 baseEnd_883415 := by
    simpa [prefixWord, tailWord_883415, baseEnd_883415] using wordTrace_append hprefix tailTrace_883415
  have hstable : (prefixWord ++ tailWord_883415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883415).length < 2 ^ (prefixWord ++ tailWord_883415).sum := by decide
  have hdescent : baseEnd_883415 < baseStart_883415 := by decide
  rcases family_descends (prefixWord ++ tailWord_883415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883428 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_883428 : Nat := 118140960795 + 883428 * 2 ^ 59
def prefixEnd_883428 : Nat := 4983230072969 + 3 ^ 40 * 883428 * 2
def baseEnd_883428 : Nat := 100805152808949959463821

theorem tailTrace_883428 : CollatzResearch.WordTrace tailWord_883428 prefixEnd_883428 100805152808949959463821 := by
  unfold tailWord_883428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110633121749354167769469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21480844162332472223692625 16110633121749354167769469)
  ·
    refine ⟨6041487420656007812913551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16110633121749354167769469 6041487420656007812913551)
    ·
      refine ⟨9062231130984011719370327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041487420656007812913551 9062231130984011719370327)
      ·
        refine ⟨13593346696476017579055491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062231130984011719370327 13593346696476017579055491)
        ·
          refine ⟨20390020044714026368583237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593346696476017579055491 20390020044714026368583237)
          ·
            refine ⟨3823128758383879944109357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20390020044714026368583237 3823128758383879944109357)
            ·
              refine ⟨1433673284393954979041009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3823128758383879944109357 1433673284393954979041009)
              ·
                refine ⟨1075254963295466234280757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433673284393954979041009 1075254963295466234280757)
                ·
                  refine ⟨100805152808949959463821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075254963295466234280757 100805152808949959463821)
                  ·
                    rfl

theorem cell22_883428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_883428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883428 prefixEnd_883428 := by exact prefixLift 883428
  have htrace : WordTrace (prefixWord ++ tailWord_883428) baseStart_883428 baseEnd_883428 := by
    simpa [prefixWord, tailWord_883428, baseEnd_883428] using wordTrace_append hprefix tailTrace_883428
  have hstable : (prefixWord ++ tailWord_883428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883428).length < 2 ^ (prefixWord ++ tailWord_883428).sum := by decide
  have hdescent : baseEnd_883428 < baseStart_883428 := by decide
  rcases family_descends (prefixWord ++ tailWord_883428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883471 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_883471 : Nat := 118140960795 + 883471 * 2 ^ 59
def prefixEnd_883471 : Nat := 4983230072969 + 3 ^ 40 * 883471 * 2
def baseEnd_883471 : Nat := 302430178205612099566331

theorem tailTrace_883471 : CollatzResearch.WordTrace tailWord_883471 prefixEnd_883471 302430178205612099566331 := by
  unfold tailWord_883471
  simp only [CollatzResearch.WordTrace]
  refine ⟨32222834582342926679354267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21481889721561951119569511 32222834582342926679354267)
  ·
    refine ⟨48334251873514390019031401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32222834582342926679354267 48334251873514390019031401)
    ·
      refine ⟨36250688905135792514273551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48334251873514390019031401 36250688905135792514273551)
      ·
        refine ⟨54376033357703688771410327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36250688905135792514273551 54376033357703688771410327)
        ·
          refine ⟨81564050036555533157115491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54376033357703688771410327 81564050036555533157115491)
          ·
            refine ⟨122346075054833299735673237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81564050036555533157115491 122346075054833299735673237)
            ·
              refine ⟨5734972268195310925109683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122346075054833299735673237 5734972268195310925109683)
              ·
                refine ⟨8602458402292966387664525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734972268195310925109683 8602458402292966387664525)
                ·
                  refine ⟨3225921900859862395374197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8602458402292966387664525 3225921900859862395374197)
                  ·
                    refine ⟨302430178205612099566331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3225921900859862395374197 302430178205612099566331)
                    ·
                      rfl

theorem cell22_883471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_883471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883471 prefixEnd_883471 := by exact prefixLift 883471
  have htrace : WordTrace (prefixWord ++ tailWord_883471) baseStart_883471 baseEnd_883471 := by
    simpa [prefixWord, tailWord_883471, baseEnd_883471] using wordTrace_append hprefix tailTrace_883471
  have hstable : (prefixWord ++ tailWord_883471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883471).length < 2 ^ (prefixWord ++ tailWord_883471).sum := by decide
  have hdescent : baseEnd_883471 < baseStart_883471 := by decide
  rcases family_descends (prefixWord ++ tailWord_883471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883490 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_883490 : Nat := 118140960795 + 883490 * 2 ^ 59
def prefixEnd_883490 : Nat := 4983230072969 + 3 ^ 40 * 883490 * 2
def baseEnd_883490 : Nat := 100812227431300794447091

theorem tailTrace_883490 : CollatzResearch.WordTrace tailWord_883490 prefixEnd_883490 100812227431300794447091 := by
  unfold tailWord_883490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055881892318523231073981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21482351712849395282863949 8055881892318523231073981)
  ·
    refine ⟨3020955709619446211652743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8055881892318523231073981 3020955709619446211652743)
    ·
      refine ⟨4531433564429169317479115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020955709619446211652743 4531433564429169317479115)
      ·
        refine ⟨6797150346643753976218673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531433564429169317479115 6797150346643753976218673)
        ·
          refine ⟨5097862759982815482164005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797150346643753976218673 5097862759982815482164005)
          ·
            refine ⟨955849267496777902905751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5097862759982815482164005 955849267496777902905751)
            ·
              refine ⟨1433773901245166854358627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955849267496777902905751 1433773901245166854358627)
              ·
                refine ⟨2150660851867750281537941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433773901245166854358627 2150660851867750281537941)
                ·
                  refine ⟨100812227431300794447091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2150660851867750281537941 100812227431300794447091)
                  ·
                    rfl

theorem cell22_883490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_883490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883490 prefixEnd_883490 := by exact prefixLift 883490
  have htrace : WordTrace (prefixWord ++ tailWord_883490) baseStart_883490 baseEnd_883490 := by
    simpa [prefixWord, tailWord_883490, baseEnd_883490] using wordTrace_append hprefix tailTrace_883490
  have hstable : (prefixWord ++ tailWord_883490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883490).length < 2 ^ (prefixWord ++ tailWord_883490).sum := by decide
  have hdescent : baseEnd_883490 < baseStart_883490 := by decide
  rcases family_descends (prefixWord ++ tailWord_883490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883505 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_883505 : Nat := 118140960795 + 883505 * 2 ^ 59
def prefixEnd_883505 : Nat := 4983230072969 + 3 ^ 40 * 883505 * 2
def baseEnd_883505 : Nat := 302441817100447344216227

theorem tailTrace_883505 : CollatzResearch.WordTrace tailWord_883505 prefixEnd_883505 302441817100447344216227 := by
  unfold tailWord_883505
  simp only [CollatzResearch.WordTrace]
  refine ⟨32224074664219750486091969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21482716442813166990727979 32224074664219750486091969)
  ·
    refine ⟨24168055998164812864568977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32224074664219750486091969 24168055998164812864568977)
    ·
      refine ⟨18126041998623609648426733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24168055998164812864568977 18126041998623609648426733)
      ·
        refine ⟨6797265749483853618160025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18126041998623609648426733 6797265749483853618160025)
        ·
          refine ⟨5097949312112890213620019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797265749483853618160025 5097949312112890213620019)
          ·
            refine ⟨7646923968169335320430029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097949312112890213620019 7646923968169335320430029)
            ·
              refine ⟨2867596488063500745161261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646923968169335320430029 2867596488063500745161261)
              ·
                refine ⟨1075348683023812779435473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867596488063500745161261 1075348683023812779435473)
                ·
                  refine ⟨806511512267859584576605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1075348683023812779435473 806511512267859584576605)
                  ·
                    refine ⟨302441817100447344216227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806511512267859584576605 302441817100447344216227)
                    ·
                      rfl

theorem cell22_883505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_883505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883505 prefixEnd_883505 := by exact prefixLift 883505
  have htrace : WordTrace (prefixWord ++ tailWord_883505) baseStart_883505 baseEnd_883505 := by
    simpa [prefixWord, tailWord_883505, baseEnd_883505] using wordTrace_append hprefix tailTrace_883505
  have hstable : (prefixWord ++ tailWord_883505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883505).length < 2 ^ (prefixWord ++ tailWord_883505).sum := by decide
  have hdescent : baseEnd_883505 < baseStart_883505 := by decide
  rcases family_descends (prefixWord ++ tailWord_883505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883526 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_883526 : Nat := 118140960795 + 883526 * 2 ^ 59
def prefixEnd_883526 : Nat := 4983230072969 + 3 ^ 40 * 883526 * 2
def baseEnd_883526 : Nat := 302449005829610289441163

theorem tailTrace_883526 : CollatzResearch.WordTrace tailWord_883526 prefixEnd_883526 302449005829610289441163 := by
  unfold tailWord_883526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007026268660739721018951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21483227064762447381737621 1007026268660739721018951)
  ·
    refine ⟨1510539402991109581528427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007026268660739721018951 1510539402991109581528427)
    ·
      refine ⟨2265809104486664372292641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510539402991109581528427 2265809104486664372292641)
      ·
        refine ⟨1699356828364998279219481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2265809104486664372292641 1699356828364998279219481)
        ·
          refine ⟨1274517621273748709414611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1699356828364998279219481 1274517621273748709414611)
          ·
            refine ⟨1911776431910623064121917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274517621273748709414611 1911776431910623064121917)
            ·
              refine ⟨716916161966483649045719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911776431910623064121917 716916161966483649045719)
              ·
                refine ⟨1075374242949725473568579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716916161966483649045719 1075374242949725473568579)
                ·
                  refine ⟨1613061364424588210352869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075374242949725473568579 1613061364424588210352869)
                  ·
                    refine ⟨302449005829610289441163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613061364424588210352869 302449005829610289441163)
                    ·
                      rfl

theorem cell22_883526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_883526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883526 prefixEnd_883526 := by exact prefixLift 883526
  have htrace : WordTrace (prefixWord ++ tailWord_883526) baseStart_883526 baseEnd_883526 := by
    simpa [prefixWord, tailWord_883526, baseEnd_883526] using wordTrace_append hprefix tailTrace_883526
  have hstable : (prefixWord ++ tailWord_883526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883526).length < 2 ^ (prefixWord ++ tailWord_883526).sum := by decide
  have hdescent : baseEnd_883526 < baseStart_883526 := by decide
  rcases family_descends (prefixWord ++ tailWord_883526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883531 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_883531 : Nat := 118140960795 + 883531 * 2 ^ 59
def prefixEnd_883531 : Nat := 4983230072969 + 3 ^ 40 * 883531 * 2
def baseEnd_883531 : Nat := 302450717431791943066147

theorem tailTrace_883531 : CollatzResearch.WordTrace tailWord_883531 prefixEnd_883531 302450717431791943066147 := by
  unfold tailWord_883531
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225022962125556926538447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21483348641417037951025631 32225022962125556926538447)
  ·
    refine ⟨48337534443188335389807671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32225022962125556926538447 48337534443188335389807671)
    ·
      refine ⟨72506301664782503084711507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48337534443188335389807671 72506301664782503084711507)
      ·
        refine ⟨108759452497173754627067261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72506301664782503084711507 108759452497173754627067261)
        ·
          refine ⟨40784794686440157985150223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108759452497173754627067261 40784794686440157985150223)
          ·
            refine ⟨61177192029660236977725335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40784794686440157985150223 61177192029660236977725335)
            ·
              refine ⟨91765788044490355466588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61177192029660236977725335 91765788044490355466588003)
              ·
                refine ⟨137648682066735533199882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91765788044490355466588003 137648682066735533199882005)
                ·
                  refine ⟨6452281971878228118744469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137648682066735533199882005 6452281971878228118744469)
                  ·
                    refine ⟨302450717431791943066147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6452281971878228118744469 302450717431791943066147)
                    ·
                      rfl

theorem cell22_883531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_883531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883531 prefixEnd_883531 := by exact prefixLift 883531
  have htrace : WordTrace (prefixWord ++ tailWord_883531) baseStart_883531 baseEnd_883531 := by
    simpa [prefixWord, tailWord_883531, baseEnd_883531] using wordTrace_append hprefix tailTrace_883531
  have hstable : (prefixWord ++ tailWord_883531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883531).length < 2 ^ (prefixWord ++ tailWord_883531).sum := by decide
  have hdescent : baseEnd_883531 < baseStart_883531 := by decide
  rcases family_descends (prefixWord ++ tailWord_883531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883563 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 5]
def baseStart_883563 : Nat := 118140960795 + 883563 * 2 ^ 59
def prefixEnd_883563 : Nat := 4983230072969 + 3 ^ 40 * 883563 * 2
def baseEnd_883563 : Nat := 100820557228584842088683

theorem tailTrace_883563 : CollatzResearch.WordTrace tailWord_883563 prefixEnd_883563 100820557228584842088683 := by
  unfold tailWord_883563
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226190098009626391703343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21484126732006417594468895 32226190098009626391703343)
  ·
    refine ⟨48339285147014439587555015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32226190098009626391703343 48339285147014439587555015)
    ·
      refine ⟨72508927720521659381332523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48339285147014439587555015 72508927720521659381332523)
      ·
        refine ⟨108763391580782489071998785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72508927720521659381332523 108763391580782489071998785)
        ·
          refine ⟨81572543685586866803999089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108763391580782489071998785 81572543685586866803999089)
          ·
            refine ⟨61179407764190150102999317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81572543685586866803999089 61179407764190150102999317)
            ·
              refine ⟨2867784738946413286078093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61179407764190150102999317 2867784738946413286078093)
              ·
                refine ⟨1075419277104904982279285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867784738946413286078093 1075419277104904982279285)
                ·
                  refine ⟨100820557228584842088683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075419277104904982279285 100820557228584842088683)
                  ·
                    rfl

theorem cell22_883563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 5].length) (baseStart_883563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883563 prefixEnd_883563 := by exact prefixLift 883563
  have htrace : WordTrace (prefixWord ++ tailWord_883563) baseStart_883563 baseEnd_883563 := by
    simpa [prefixWord, tailWord_883563, baseEnd_883563] using wordTrace_append hprefix tailTrace_883563
  have hstable : (prefixWord ++ tailWord_883563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883563).length < 2 ^ (prefixWord ++ tailWord_883563).sum := by decide
  have hdescent : baseEnd_883563 < baseStart_883563 := by decide
  rcases family_descends (prefixWord ++ tailWord_883563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883640 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_883640 : Nat := 118140960795 + 883640 * 2 ^ 59
def prefixEnd_883640 : Nat := 4983230072969 + 3 ^ 40 * 883640 * 2
def baseEnd_883640 : Nat := 302488030359351992090813

theorem tailTrace_883640 : CollatzResearch.WordTrace tailWord_883640 prefixEnd_883640 302488030359351992090813 := by
  unfold tailWord_883640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114499259365334271128187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21485999012487112361504249 16114499259365334271128187)
  ·
    refine ⟨24171748889048001406692281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114499259365334271128187 24171748889048001406692281)
    ·
      refine ⟨18128811666786001055019211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24171748889048001406692281 18128811666786001055019211)
      ·
        refine ⟨27193217500179001582528817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18128811666786001055019211 27193217500179001582528817)
        ·
          refine ⟨20394913125134251186896613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27193217500179001582528817 20394913125134251186896613)
          ·
            refine ⟨3824046210962672097543115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20394913125134251186896613 3824046210962672097543115)
            ·
              refine ⟨5736069316444008146314673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824046210962672097543115 5736069316444008146314673)
              ·
                refine ⟨4302051987333006109736005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736069316444008146314673 4302051987333006109736005)
                ·
                  refine ⟨806634747624938645575501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4302051987333006109736005 806634747624938645575501)
                  ·
                    refine ⟨302488030359351992090813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806634747624938645575501 302488030359351992090813)
                    ·
                      rfl

theorem cell22_883640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_883640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883640 prefixEnd_883640 := by exact prefixLift 883640
  have htrace : WordTrace (prefixWord ++ tailWord_883640) baseStart_883640 baseEnd_883640 := by
    simpa [prefixWord, tailWord_883640, baseEnd_883640] using wordTrace_append hprefix tailTrace_883640
  have hstable : (prefixWord ++ tailWord_883640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883640).length < 2 ^ (prefixWord ++ tailWord_883640).sum := by decide
  have hdescent : baseEnd_883640 < baseStart_883640 := by decide
  rcases family_descends (prefixWord ++ tailWord_883640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883674 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_883674 : Nat := 118140960795 + 883674 * 2 ^ 59
def prefixEnd_883674 : Nat := 4983230072969 + 3 ^ 40 * 883674 * 2
def baseEnd_883674 : Nat := 302499669254187236740709

theorem tailTrace_883674 : CollatzResearch.WordTrace tailWord_883674 prefixEnd_883674 302499669254187236740709 := by
  unfold tailWord_883674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057559650151873087248519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21486825733738328232662717 8057559650151873087248519)
  ·
    refine ⟨12086339475227809630872779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8057559650151873087248519 12086339475227809630872779)
    ·
      refine ⟨18129509212841714446309169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12086339475227809630872779 18129509212841714446309169)
      ·
        refine ⟨13597131909631285834731877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18129509212841714446309169 13597131909631285834731877)
        ·
          refine ⟨2549462233055866094012227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13597131909631285834731877 2549462233055866094012227)
          ·
            refine ⟨3824193349583799141018341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549462233055866094012227 3824193349583799141018341)
            ·
              refine ⟨717036253046962338940939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3824193349583799141018341 717036253046962338940939)
              ·
                refine ⟨1075554379570443508411409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717036253046962338940939 1075554379570443508411409)
                ·
                  refine ⟨806665784677832631308557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1075554379570443508411409 806665784677832631308557)
                  ·
                    refine ⟨302499669254187236740709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806665784677832631308557 302499669254187236740709)
                    ·
                      rfl

theorem cell22_883674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_883674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883674 prefixEnd_883674 := by exact prefixLift 883674
  have htrace : WordTrace (prefixWord ++ tailWord_883674) baseStart_883674 baseEnd_883674 := by
    simpa [prefixWord, tailWord_883674, baseEnd_883674] using wordTrace_append hprefix tailTrace_883674
  have hstable : (prefixWord ++ tailWord_883674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883674).length < 2 ^ (prefixWord ++ tailWord_883674).sum := by decide
  have hdescent : baseEnd_883674 < baseStart_883674 := by decide
  rcases family_descends (prefixWord ++ tailWord_883674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883719 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 1, 3]
def baseStart_883719 : Nat := 118140960795 + 883719 * 2 ^ 59
def prefixEnd_883719 : Nat := 4983230072969 + 3 ^ 40 * 883719 * 2
def baseEnd_883719 : Nat := 302515073673822119365571

theorem tailTrace_883719 : CollatzResearch.WordTrace tailWord_883719 prefixEnd_883719 302515073673822119365571 := by
  unfold tailWord_883719
  simp only [CollatzResearch.WordTrace]
  refine ⟨32231879885444465034382211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21487919923629643356254807 32231879885444465034382211)
  ·
    refine ⟨48347819828166697551573317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32231879885444465034382211 48347819828166697551573317)
    ·
      refine ⟨9065216217781255790919997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48347819828166697551573317 9065216217781255790919997)
      ·
        refine ⟨3399456081667970921594999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9065216217781255790919997 3399456081667970921594999)
        ·
          refine ⟨5099184122501956382392499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399456081667970921594999 5099184122501956382392499)
          ·
            refine ⟨7648776183752934573588749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099184122501956382392499 7648776183752934573588749)
            ·
              refine ⟨2868291068907350465095781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7648776183752934573588749 2868291068907350465095781)
              ·
                refine ⟨537804575420128212205459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2868291068907350465095781 537804575420128212205459)
                ·
                  refine ⟨806706863130192318308189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537804575420128212205459 806706863130192318308189)
                  ·
                    refine ⟨302515073673822119365571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806706863130192318308189 302515073673822119365571)
                    ·
                      rfl

theorem cell22_883719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_883719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883719 prefixEnd_883719 := by exact prefixLift 883719
  have htrace : WordTrace (prefixWord ++ tailWord_883719) baseStart_883719 baseEnd_883719 := by
    simpa [prefixWord, tailWord_883719, baseEnd_883719] using wordTrace_append hprefix tailTrace_883719
  have hstable : (prefixWord ++ tailWord_883719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883719).length < 2 ^ (prefixWord ++ tailWord_883719).sum := by decide
  have hdescent : baseEnd_883719 < baseStart_883719 := by decide
  rcases family_descends (prefixWord ++ tailWord_883719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883728 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_883728 : Nat := 118140960795 + 883728 * 2 ^ 59
def prefixEnd_883728 : Nat := 4983230072969 + 3 ^ 40 * 883728 * 2
def baseEnd_883728 : Nat := 302518154557749095890543

theorem tailTrace_883728 : CollatzResearch.WordTrace tailWord_883728 prefixEnd_883728 302518154557749095890543 := by
  unfold tailWord_883728
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116104071205929785729919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21488138761607906380973225 16116104071205929785729919)
  ·
    refine ⟨24174156106808894678594879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16116104071205929785729919 24174156106808894678594879)
    ·
      refine ⟨36261234160213342017892319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24174156106808894678594879 36261234160213342017892319)
      ·
        refine ⟨54391851240320013026838479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36261234160213342017892319 54391851240320013026838479)
        ·
          refine ⟨81587776860480019540257719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54391851240320013026838479 81587776860480019540257719)
          ·
            refine ⟨122381665290720029310386579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81587776860480019540257719 122381665290720029310386579)
            ·
              refine ⟨183572497936080043965579869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122381665290720029310386579 183572497936080043965579869)
              ·
                refine ⟨68839686726030016487092451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183572497936080043965579869 68839686726030016487092451)
                ·
                  refine ⟨103259530089045024730638677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68839686726030016487092451 103259530089045024730638677)
                  ·
                    refine ⟨302518154557749095890543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 103259530089045024730638677 302518154557749095890543)
                    ·
                      rfl

theorem cell22_883728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_883728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883728 prefixEnd_883728 := by exact prefixLift 883728
  have htrace : WordTrace (prefixWord ++ tailWord_883728) baseStart_883728 baseEnd_883728 := by
    simpa [prefixWord, tailWord_883728, baseEnd_883728] using wordTrace_append hprefix tailTrace_883728
  have hstable : (prefixWord ++ tailWord_883728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883728).length < 2 ^ (prefixWord ++ tailWord_883728).sum := by decide
  have hdescent : baseEnd_883728 < baseStart_883728 := by decide
  rcases family_descends (prefixWord ++ tailWord_883728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883762 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_883762 : Nat := 118140960795 + 883762 * 2 ^ 59
def prefixEnd_883762 : Nat := 4983230072969 + 3 ^ 40 * 883762 * 2
def baseEnd_883762 : Nat := 302529793452584340540439

theorem tailTrace_883762 : CollatzResearch.WordTrace tailWord_883762 prefixEnd_883762 302529793452584340540439 := by
  unfold tailWord_883762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058362056072170844549385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21488965482859122252131693 8058362056072170844549385)
  ·
    refine ⟨6043771542054128133412039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8058362056072170844549385 6043771542054128133412039)
    ·
      refine ⟨9065657313081192200118059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043771542054128133412039 9065657313081192200118059)
      ·
        refine ⟨13598485969621788300177089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065657313081192200118059 13598485969621788300177089)
        ·
          refine ⟨10198864477216341225132817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13598485969621788300177089 10198864477216341225132817)
          ·
            refine ⟨7649148357912255918849613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10198864477216341225132817 7649148357912255918849613)
            ·
              refine ⟨2868430634217095969568605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7649148357912255918849613 2868430634217095969568605)
              ·
                refine ⟨1075661487831410988588227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2868430634217095969568605 1075661487831410988588227)
                ·
                  refine ⟨1613492231747116482882341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075661487831410988588227 1613492231747116482882341)
                  ·
                    refine ⟨302529793452584340540439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613492231747116482882341 302529793452584340540439)
                    ·
                      rfl

theorem cell22_883762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_883762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883762 prefixEnd_883762 := by exact prefixLift 883762
  have htrace : WordTrace (prefixWord ++ tailWord_883762) baseStart_883762 baseEnd_883762 := by
    simpa [prefixWord, tailWord_883762, baseEnd_883762] using wordTrace_append hprefix tailTrace_883762
  have hstable : (prefixWord ++ tailWord_883762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883762).length < 2 ^ (prefixWord ++ tailWord_883762).sum := by decide
  have hdescent : baseEnd_883762 < baseStart_883762 := by decide
  rcases family_descends (prefixWord ++ tailWord_883762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883790 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_883790 : Nat := 118140960795 + 883790 * 2 ^ 59
def prefixEnd_883790 : Nat := 4983230072969 + 3 ^ 40 * 883790 * 2
def baseEnd_883790 : Nat := 302539378424801600840353

theorem tailTrace_883790 : CollatzResearch.WordTrace tailWord_883790 prefixEnd_883790 302539378424801600840353 := by
  unfold tailWord_883790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029308683523405520027103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21489646312124829440144549 4029308683523405520027103)
  ·
    refine ⟨6043963025285108280040655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4029308683523405520027103 6043963025285108280040655)
    ·
      refine ⟨9065944537927662420060983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043963025285108280040655 9065944537927662420060983)
      ·
        refine ⟨13598916806891493630091475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065944537927662420060983 13598916806891493630091475)
        ·
          refine ⟨20398375210337240445137213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13598916806891493630091475 20398375210337240445137213)
          ·
            refine ⟨7649390703876465166926455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20398375210337240445137213 7649390703876465166926455)
            ·
              refine ⟨11474086055814697750389683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649390703876465166926455 11474086055814697750389683)
              ·
                refine ⟨17211129083722046625584525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11474086055814697750389683 17211129083722046625584525)
                ·
                  refine ⟨6454173406395767484594197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17211129083722046625584525 6454173406395767484594197)
                  ·
                    refine ⟨302539378424801600840353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6454173406395767484594197 302539378424801600840353)
                    ·
                      rfl

theorem cell22_883790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_883790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883790 prefixEnd_883790 := by exact prefixLift 883790
  have htrace : WordTrace (prefixWord ++ tailWord_883790) baseStart_883790 baseEnd_883790 := by
    simpa [prefixWord, tailWord_883790, baseEnd_883790] using wordTrace_append hprefix tailTrace_883790
  have hstable : (prefixWord ++ tailWord_883790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883790).length < 2 ^ (prefixWord ++ tailWord_883790).sum := by decide
  have hdescent : baseEnd_883790 < baseStart_883790 := by decide
  rcases family_descends (prefixWord ++ tailWord_883790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883792 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_883792 : Nat := 118140960795 + 883792 * 2 ^ 59
def prefixEnd_883792 : Nat := 4983230072969 + 3 ^ 40 * 883792 * 2
def baseEnd_883792 : Nat := 302540063065674262290347

theorem tailTrace_883792 : CollatzResearch.WordTrace tailWord_883792 prefixEnd_883792 302540063065674262290347 := by
  unfold tailWord_883792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117271207089999250894815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21489694942786665667859753 16117271207089999250894815)
  ·
    refine ⟨24175906810634998876342223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16117271207089999250894815 24175906810634998876342223)
    ·
      refine ⟨36263860215952498314513335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24175906810634998876342223 36263860215952498314513335)
      ·
        refine ⟨54395790323928747471770003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36263860215952498314513335 54395790323928747471770003)
        ·
          refine ⟨81593685485893121207655005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54395790323928747471770003 81593685485893121207655005)
          ·
            refine ⟨30597632057209920452870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81593685485893121207655005 30597632057209920452870627)
            ·
              refine ⟨45896448085814880679305941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30597632057209920452870627 45896448085814880679305941)
              ·
                refine ⟨1075698002011286265921233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45896448085814880679305941 1075698002011286265921233)
                ·
                  refine ⟨806773501508464699440925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1075698002011286265921233 806773501508464699440925)
                  ·
                    refine ⟨302540063065674262290347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806773501508464699440925 302540063065674262290347)
                    ·
                      rfl

theorem cell22_883792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_883792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883792 prefixEnd_883792 := by exact prefixLift 883792
  have htrace : WordTrace (prefixWord ++ tailWord_883792) baseStart_883792 baseEnd_883792 := by
    simpa [prefixWord, tailWord_883792, baseEnd_883792] using wordTrace_append hprefix tailTrace_883792
  have hstable : (prefixWord ++ tailWord_883792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883792).length < 2 ^ (prefixWord ++ tailWord_883792).sum := by decide
  have hdescent : baseEnd_883792 < baseStart_883792 := by decide
  rcases family_descends (prefixWord ++ tailWord_883792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883822 : List Nat := [4, 1, 2, 2, 1, 4, 8]
def baseStart_883822 : Nat := 118140960795 + 883822 * 2 ^ 59
def prefixEnd_883822 : Nat := 4983230072969 + 3 ^ 40 * 883822 * 2
def baseEnd_883822 : Nat := 11205567876991266075565

theorem tailTrace_883822 : CollatzResearch.WordTrace tailWord_883822 prefixEnd_883822 11205567876991266075565 := by
  unfold tailWord_883822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029454575508914203172715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21490424402714209083587813 4029454575508914203172715)
  ·
    refine ⟨6044181863263371304759073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4029454575508914203172715 6044181863263371304759073)
    ·
      refine ⟨4533136397447528478569305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6044181863263371304759073 4533136397447528478569305)
      ·
        refine ⟨3399852298085646358926979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4533136397447528478569305 3399852298085646358926979)
        ·
          refine ⟨5099778447128469538390469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399852298085646358926979 5099778447128469538390469)
          ·
            refine ⟨956208458836588038448213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5099778447128469538390469 956208458836588038448213)
            ·
              refine ⟨11205567876991266075565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 956208458836588038448213 11205567876991266075565)
              ·
                rfl

theorem cell22_883822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 8].length) (baseStart_883822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883822 prefixEnd_883822 := by exact prefixLift 883822
  have htrace : WordTrace (prefixWord ++ tailWord_883822) baseStart_883822 baseEnd_883822 := by
    simpa [prefixWord, tailWord_883822, baseEnd_883822] using wordTrace_append hprefix tailTrace_883822
  have hstable : (prefixWord ++ tailWord_883822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883822).length < 2 ^ (prefixWord ++ tailWord_883822).sum := by decide
  have hdescent : baseEnd_883822 < baseStart_883822 := by decide
  rcases family_descends (prefixWord ++ tailWord_883822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883865 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_883865 : Nat := 118140960795 + 883865 * 2 ^ 59
def prefixEnd_883865 : Nat := 4983230072969 + 3 ^ 40 * 883865 * 2
def baseEnd_883865 : Nat := 302565052457526405215123

theorem tailTrace_883865 : CollatzResearch.WordTrace tailWord_883865 prefixEnd_883865 302565052457526405215123 := by
  unfold tailWord_883865
  simp only [CollatzResearch.WordTrace]
  refine ⟨32237204942915531969197049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21491469961943687979464699 32237204942915531969197049)
  ·
    refine ⟨24177903707186648976897787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32237204942915531969197049 24177903707186648976897787)
    ·
      refine ⟨36266855560779973465346681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24177903707186648976897787 36266855560779973465346681)
      ·
        refine ⟨27200141670584980099010011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36266855560779973465346681 27200141670584980099010011)
        ·
          refine ⟨40800212505877470148515017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200141670584980099010011 40800212505877470148515017)
          ·
            refine ⟨30600159379408102611386263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40800212505877470148515017 30600159379408102611386263)
            ·
              refine ⟨45900239069112153917079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30600159379408102611386263 45900239069112153917079395)
              ·
                refine ⟨68850358603668230875619093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45900239069112153917079395 68850358603668230875619093)
                ·
                  refine ⟨3227360559546948322294645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68850358603668230875619093 3227360559546948322294645)
                  ·
                    refine ⟨302565052457526405215123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3227360559546948322294645 302565052457526405215123)
                    ·
                      rfl

theorem cell22_883865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_883865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883865 prefixEnd_883865 := by exact prefixLift 883865
  have htrace : WordTrace (prefixWord ++ tailWord_883865) baseStart_883865 baseEnd_883865 := by
    simpa [prefixWord, tailWord_883865, baseEnd_883865] using wordTrace_append hprefix tailTrace_883865
  have hstable : (prefixWord ++ tailWord_883865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883865).length < 2 ^ (prefixWord ++ tailWord_883865).sum := by decide
  have hdescent : baseEnd_883865 < baseStart_883865 := by decide
  rcases family_descends (prefixWord ++ tailWord_883865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883897 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_883897 : Nat := 118140960795 + 883897 * 2 ^ 59
def prefixEnd_883897 : Nat := 4983230072969 + 3 ^ 40 * 883897 * 2
def baseEnd_883897 : Nat := 302576006711488988415025

theorem tailTrace_883897 : CollatzResearch.WordTrace tailWord_883897 prefixEnd_883897 302576006711488988415025 := by
  unfold tailWord_883897
  simp only [CollatzResearch.WordTrace]
  refine ⟨32238372078799601434361945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492248052533067622907963 32238372078799601434361945)
  ·
    refine ⟨24178779059099701075771459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32238372078799601434361945 24178779059099701075771459)
    ·
      refine ⟨36268168588649551613657189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24178779059099701075771459 36268168588649551613657189)
      ·
        refine ⟨6800281610371790927560723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36268168588649551613657189 6800281610371790927560723)
        ·
          refine ⟨10200422415557686391341085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800281610371790927560723 10200422415557686391341085)
          ·
            refine ⟨3825158405834132396752907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10200422415557686391341085 3825158405834132396752907)
            ·
              refine ⟨5737737608751198595129361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825158405834132396752907 5737737608751198595129361)
              ·
                refine ⟨4303303206563398946347021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737737608751198595129361 4303303206563398946347021)
                ·
                  refine ⟨1613738702461274604880133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4303303206563398946347021 1613738702461274604880133)
                  ·
                    refine ⟨302576006711488988415025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1613738702461274604880133 302576006711488988415025)
                    ·
                      rfl

theorem cell22_883897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_883897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883897 prefixEnd_883897 := by exact prefixLift 883897
  have htrace : WordTrace (prefixWord ++ tailWord_883897) baseStart_883897 baseEnd_883897 := by
    simpa [prefixWord, tailWord_883897, baseEnd_883897] using wordTrace_append hprefix tailTrace_883897
  have hstable : (prefixWord ++ tailWord_883897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883897).length < 2 ^ (prefixWord ++ tailWord_883897).sum := by decide
  have hdescent : baseEnd_883897 < baseStart_883897 := by decide
  rcases family_descends (prefixWord ++ tailWord_883897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883927 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_883927 : Nat := 118140960795 + 883927 * 2 ^ 59
def prefixEnd_883927 : Nat := 4983230072969 + 3 ^ 40 * 883927 * 2
def baseEnd_883927 : Nat := 302586276324578910164933

theorem tailTrace_883927 : CollatzResearch.WordTrace tailWord_883927 prefixEnd_883927 302586276324578910164933 := by
  unfold tailWord_883927
  simp only [CollatzResearch.WordTrace]
  refine ⟨32239466268690916557954035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21492977512460611038636023 32239466268690916557954035)
  ·
    refine ⟨48359199403036374836931053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32239466268690916557954035 48359199403036374836931053)
    ·
      refine ⟨18134699776138640563849145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48359199403036374836931053 18134699776138640563849145)
      ·
        refine ⟨13601024832103980422886859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18134699776138640563849145 13601024832103980422886859)
        ·
          refine ⟨20401537248155970634330289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13601024832103980422886859 20401537248155970634330289)
          ·
            refine ⟨15301152936116977975747717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20401537248155970634330289 15301152936116977975747717)
            ·
              refine ⟨2868966175521933370452697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15301152936116977975747717 2868966175521933370452697)
              ·
                refine ⟨2151724631641450027839523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868966175521933370452697 2151724631641450027839523)
                ·
                  refine ⟨3227586947462175041759285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151724631641450027839523 3227586947462175041759285)
                  ·
                    refine ⟨302586276324578910164933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3227586947462175041759285 302586276324578910164933)
                    ·
                      rfl

theorem cell22_883927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_883927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883927 prefixEnd_883927 := by exact prefixLift 883927
  have htrace : WordTrace (prefixWord ++ tailWord_883927) baseStart_883927 baseEnd_883927 := by
    simpa [prefixWord, tailWord_883927, baseEnd_883927] using wordTrace_append hprefix tailTrace_883927
  have hstable : (prefixWord ++ tailWord_883927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883927).length < 2 ^ (prefixWord ++ tailWord_883927).sum := by decide
  have hdescent : baseEnd_883927 < baseStart_883927 := by decide
  rcases family_descends (prefixWord ++ tailWord_883927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883944 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_883944 : Nat := 118140960795 + 883944 * 2 ^ 59
def prefixEnd_883944 : Nat := 4983230072969 + 3 ^ 40 * 883944 * 2
def baseEnd_883944 : Nat := 302592095771996532489881

theorem tailTrace_883944 : CollatzResearch.WordTrace tailWord_883944 prefixEnd_883944 302592095771996532489881 := by
  unfold tailWord_883944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120043154814664230661443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21493390873086218974215257 16120043154814664230661443)
  ·
    refine ⟨24180064732221996345992165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120043154814664230661443 24180064732221996345992165)
    ·
      refine ⟨4533762137291624314873531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24180064732221996345992165 4533762137291624314873531)
      ·
        refine ⟨6800643205937436472310297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533762137291624314873531 6800643205937436472310297)
        ·
          refine ⟨5100482404453077354232723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6800643205937436472310297 5100482404453077354232723)
          ·
            refine ⟨7650723606679616031349085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100482404453077354232723 7650723606679616031349085)
            ·
              refine ⟨2869021352504856011755907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7650723606679616031349085 2869021352504856011755907)
              ·
                refine ⟨4303532028757284017633861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869021352504856011755907 4303532028757284017633861)
                ·
                  refine ⟨806912255391990753306349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4303532028757284017633861 806912255391990753306349)
                  ·
                    refine ⟨302592095771996532489881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806912255391990753306349 302592095771996532489881)
                    ·
                      rfl

theorem cell22_883944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_883944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883944 prefixEnd_883944 := by exact prefixLift 883944
  have htrace : WordTrace (prefixWord ++ tailWord_883944) baseStart_883944 baseEnd_883944 := by
    simpa [prefixWord, tailWord_883944, baseEnd_883944] using wordTrace_append hprefix tailTrace_883944
  have hstable : (prefixWord ++ tailWord_883944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883944).length < 2 ^ (prefixWord ++ tailWord_883944).sum := by decide
  have hdescent : baseEnd_883944 < baseStart_883944 := by decide
  rcases family_descends (prefixWord ++ tailWord_883944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_883961 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_883961 : Nat := 118140960795 + 883961 * 2 ^ 59
def prefixEnd_883961 : Nat := 4983230072969 + 3 ^ 40 * 883961 * 2
def baseEnd_883961 : Nat := 302597915219414154814829

theorem tailTrace_883961 : CollatzResearch.WordTrace tailWord_883961 prefixEnd_883961 302597915219414154814829 := by
  unfold tailWord_883961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32240706350567740364691737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21493804233711826909794491 32240706350567740364691737)
  ·
    refine ⟨24180529762925805273518803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32240706350567740364691737 24180529762925805273518803)
    ·
      refine ⟨36270794644388707910278205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24180529762925805273518803 36270794644388707910278205)
      ·
        refine ⟨13601547991645765466354327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36270794644388707910278205 13601547991645765466354327)
        ·
          refine ⟨20402321987468648199531491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13601547991645765466354327 20402321987468648199531491)
          ·
            refine ⟨30603482981202972299297237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20402321987468648199531491 30603482981202972299297237)
            ·
              refine ⟨717269132371944663264779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30603482981202972299297237 717269132371944663264779)
              ·
                refine ⟨1075903698557916994897169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717269132371944663264779 1075903698557916994897169)
                ·
                  refine ⟨806927773918437746172877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1075903698557916994897169 806927773918437746172877)
                  ·
                    refine ⟨302597915219414154814829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 806927773918437746172877 302597915219414154814829)
                    ·
                      rfl

theorem cell22_883961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_883961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_883961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_883961 prefixEnd_883961 := by exact prefixLift 883961
  have htrace : WordTrace (prefixWord ++ tailWord_883961) baseStart_883961 baseEnd_883961 := by
    simpa [prefixWord, tailWord_883961, baseEnd_883961] using wordTrace_append hprefix tailTrace_883961
  have hstable : (prefixWord ++ tailWord_883961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_883961).length < 2 ^ (prefixWord ++ tailWord_883961).sum := by decide
  have hdescent : baseEnd_883961 < baseStart_883961 := by decide
  rcases family_descends (prefixWord ++ tailWord_883961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884019 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 5]
def baseStart_884019 : Nat := 118140960795 + 884019 * 2 ^ 59
def prefixEnd_884019 : Nat := 4983230072969 + 3 ^ 40 * 884019 * 2
def baseEnd_884019 : Nat := 100872589934907112288217

theorem tailTrace_884019 : CollatzResearch.WordTrace tailWord_884019 prefixEnd_884019 100872589934907112288217 := by
  unfold tailWord_884019
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242821784357616270303111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21495214522905077513535407 32242821784357616270303111)
  ·
    refine ⟨48364232676536424405454667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32242821784357616270303111 48364232676536424405454667)
    ·
      refine ⟨72546349014804636608182001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48364232676536424405454667 72546349014804636608182001)
      ·
        refine ⟨54409761761103477456136501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72546349014804636608182001 54409761761103477456136501)
        ·
          refine ⟨5100915165103451011512797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54409761761103477456136501 5100915165103451011512797)
          ·
            refine ⟨1912843186913794129317299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5100915165103451011512797 1912843186913794129317299)
            ·
              refine ⟨2869264780370691193975949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1912843186913794129317299 2869264780370691193975949)
              ·
                refine ⟨1075974292639009197740981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869264780370691193975949 1075974292639009197740981)
                ·
                  refine ⟨100872589934907112288217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075974292639009197740981 100872589934907112288217)
                  ·
                    rfl

theorem cell22_884019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 5].length) (baseStart_884019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884019 prefixEnd_884019 := by exact prefixLift 884019
  have htrace : WordTrace (prefixWord ++ tailWord_884019) baseStart_884019 baseEnd_884019 := by
    simpa [prefixWord, tailWord_884019, baseEnd_884019] using wordTrace_append hprefix tailTrace_884019
  have hstable : (prefixWord ++ tailWord_884019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884019).length < 2 ^ (prefixWord ++ tailWord_884019).sum := by decide
  have hdescent : baseEnd_884019 < baseStart_884019 := by decide
  rcases family_descends (prefixWord ++ tailWord_884019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884079 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 1, 5]
def baseStart_884079 : Nat := 118140960795 + 884079 * 2 ^ 59
def prefixEnd_884079 : Nat := 4983230072969 + 3 ^ 40 * 884079 * 2
def baseEnd_884079 : Nat := 302638309030901180364467

theorem tailTrace_884079 : CollatzResearch.WordTrace tailWord_884079 prefixEnd_884079 302638309030901180364467 := by
  unfold tailWord_884079
  simp only [CollatzResearch.WordTrace]
  refine ⟨32245010164140246517487291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21496673442760164344991527 32245010164140246517487291)
  ·
    refine ⟨48367515246210369776230937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32245010164140246517487291 48367515246210369776230937)
    ·
      refine ⟨36275636434657777332173203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48367515246210369776230937 36275636434657777332173203)
      ·
        refine ⟨54413454651986665998259805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36275636434657777332173203 54413454651986665998259805)
        ·
          refine ⟨20405045494494999749347427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54413454651986665998259805 20405045494494999749347427)
          ·
            refine ⟨30607568241742499624021141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405045494494999749347427 30607568241742499624021141)
            ·
              refine ⟨1434729761331679669875991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30607568241742499624021141 1434729761331679669875991)
              ·
                refine ⟨2152094641997519504813987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434729761331679669875991 2152094641997519504813987)
                ·
                  refine ⟨3228141962996279257220981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152094641997519504813987 3228141962996279257220981)
                  ·
                    refine ⟨302638309030901180364467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3228141962996279257220981 302638309030901180364467)
                    ·
                      rfl

theorem cell22_884079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_884079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884079 prefixEnd_884079 := by exact prefixLift 884079
  have htrace : WordTrace (prefixWord ++ tailWord_884079) baseStart_884079 baseEnd_884079 := by
    simpa [prefixWord, tailWord_884079, baseEnd_884079] using wordTrace_append hprefix tailTrace_884079
  have hstable : (prefixWord ++ tailWord_884079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884079).length < 2 ^ (prefixWord ++ tailWord_884079).sum := by decide
  have hdescent : baseEnd_884079 < baseStart_884079 := by decide
  rcases family_descends (prefixWord ++ tailWord_884079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884130 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_884130 : Nat := 118140960795 + 884130 * 2 ^ 59
def prefixEnd_884130 : Nat := 4983230072969 + 3 ^ 40 * 884130 * 2
def baseEnd_884130 : Nat := 302655767373154047339311

theorem tailTrace_884130 : CollatzResearch.WordTrace tailWord_884130 prefixEnd_884130 302655767373154047339311 := by
  unfold tailWord_884130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061717571738870556898461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21497913524636988151729229 8061717571738870556898461)
  ·
    refine ⟨3023144089402076458836923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8061717571738870556898461 3023144089402076458836923)
    ·
      refine ⟨4534716134103114688255385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023144089402076458836923 4534716134103114688255385)
      ·
        refine ⟨3401037100577336016191539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534716134103114688255385 3401037100577336016191539)
        ·
          refine ⟨5101555650866004024287309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401037100577336016191539 5101555650866004024287309)
          ·
            refine ⟨1913083369074751509107741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5101555650866004024287309 1913083369074751509107741)
            ·
              refine ⟨717406263403031815915403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1913083369074751509107741 717406263403031815915403)
              ·
                refine ⟨1076109395104547723873105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717406263403031815915403 1076109395104547723873105)
                ·
                  refine ⟨807082046328410792904829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076109395104547723873105 807082046328410792904829)
                  ·
                    refine ⟨302655767373154047339311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807082046328410792904829 302655767373154047339311)
                    ·
                      rfl

theorem cell22_884130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_884130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884130 prefixEnd_884130 := by exact prefixLift 884130
  have htrace : WordTrace (prefixWord ++ tailWord_884130) baseStart_884130 baseEnd_884130 := by
    simpa [prefixWord, tailWord_884130, baseEnd_884130] using wordTrace_append hprefix tailTrace_884130
  have hstable : (prefixWord ++ tailWord_884130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884130).length < 2 ^ (prefixWord ++ tailWord_884130).sum := by decide
  have hdescent : baseEnd_884130 < baseStart_884130 := by decide
  rcases family_descends (prefixWord ++ tailWord_884130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884218 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_884218 : Nat := 118140960795 + 884218 * 2 ^ 59
def prefixEnd_884218 : Nat := 4983230072969 + 3 ^ 40 * 884218 * 2
def baseEnd_884218 : Nat := 302685891571551151139041

theorem tailTrace_884218 : CollatzResearch.WordTrace tailWord_884218 prefixEnd_884218 302685891571551151139041 := by
  unfold tailWord_884218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062519977659168314199327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21500053273757782171198205 8062519977659168314199327)
  ·
    refine ⟨12093779966488752471298991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062519977659168314199327 12093779966488752471298991)
    ·
      refine ⟨18140669949733128706948487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093779966488752471298991 18140669949733128706948487)
      ·
        refine ⟨27211004924599693060422731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140669949733128706948487 27211004924599693060422731)
        ·
          refine ⟨40816507386899539590634097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211004924599693060422731 40816507386899539590634097)
          ·
            refine ⟨30612380540174654692975573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40816507386899539590634097 30612380540174654692975573)
            ·
              refine ⟨717477668910343469366615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30612380540174654692975573 717477668910343469366615)
              ·
                refine ⟨1076216503365515204049923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717477668910343469366615 1076216503365515204049923)
                ·
                  refine ⟨1614324755048272806074885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076216503365515204049923 1614324755048272806074885)
                  ·
                    refine ⟨302685891571551151139041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1614324755048272806074885 302685891571551151139041)
                    ·
                      rfl

theorem cell22_884218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_884218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884218 prefixEnd_884218 := by exact prefixLift 884218
  have htrace : WordTrace (prefixWord ++ tailWord_884218) baseStart_884218 baseEnd_884218 := by
    simpa [prefixWord, tailWord_884218, baseEnd_884218] using wordTrace_append hprefix tailTrace_884218
  have hstable : (prefixWord ++ tailWord_884218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884218).length < 2 ^ (prefixWord ++ tailWord_884218).sum := by decide
  have hdescent : baseEnd_884218 < baseStart_884218 := by decide
  rcases family_descends (prefixWord ++ tailWord_884218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884229 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_884229 : Nat := 118140960795 + 884229 * 2 ^ 59
def prefixEnd_884229 : Nat := 4983230072969 + 3 ^ 40 * 884229 * 2
def baseEnd_884229 : Nat := 302689657096350789114007

theorem tailTrace_884229 : CollatzResearch.WordTrace tailWord_884229 prefixEnd_884229 302689657096350789114007 := by
  unfold tailWord_884229
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250481113596822135447741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21500320742397881423631827 32250481113596822135447741)
  ·
    refine ⟨12093930417598808300792903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32250481113596822135447741 12093930417598808300792903)
    ·
      refine ⟨18140895626398212451189355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093930417598808300792903 18140895626398212451189355)
      ·
        refine ⟨27211343439597318676784033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140895626398212451189355 27211343439597318676784033)
        ·
          refine ⟨20408507579697989007588025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27211343439597318676784033 20408507579697989007588025)
          ·
            refine ⟨15306380684773491755691019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20408507579697989007588025 15306380684773491755691019)
            ·
              refine ⟨22959571027160237633536529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15306380684773491755691019 22959571027160237633536529)
              ·
                refine ⟨17219678270370178225152397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22959571027160237633536529 17219678270370178225152397)
                ·
                  refine ⟨6457379351388816834432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17219678270370178225152397 6457379351388816834432149)
                  ·
                    refine ⟨302689657096350789114007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6457379351388816834432149 302689657096350789114007)
                    ·
                      rfl

theorem cell22_884229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_884229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884229 prefixEnd_884229 := by exact prefixLift 884229
  have htrace : WordTrace (prefixWord ++ tailWord_884229) baseStart_884229 baseEnd_884229 := by
    simpa [prefixWord, tailWord_884229, baseEnd_884229] using wordTrace_append hprefix tailTrace_884229
  have hstable : (prefixWord ++ tailWord_884229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884229).length < 2 ^ (prefixWord ++ tailWord_884229).sum := by decide
  have hdescent : baseEnd_884229 < baseStart_884229 := by decide
  rcases family_descends (prefixWord ++ tailWord_884229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884248 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_884248 : Nat := 118140960795 + 884248 * 2 ^ 59
def prefixEnd_884248 : Nat := 4983230072969 + 3 ^ 40 * 884248 * 2
def baseEnd_884248 : Nat := 302696161184641072888949

theorem tailTrace_884248 : CollatzResearch.WordTrace tailWord_884248 prefixEnd_884248 302696161184641072888949 := by
  unfold tailWord_884248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16125587050263994190194699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21500782733685325586926265 16125587050263994190194699)
  ·
    refine ⟨24188380575395991285292049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16125587050263994190194699 24188380575395991285292049)
    ·
      refine ⟨18141285431546993463969037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24188380575395991285292049 18141285431546993463969037)
      ·
        refine ⟨6802982036830122548988389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18141285431546993463969037 6802982036830122548988389)
        ·
          refine ⟨1275559131905647977935323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6802982036830122548988389 1275559131905647977935323)
          ·
            refine ⟨1913338697858471966902985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275559131905647977935323 1913338697858471966902985)
            ·
              refine ⟨1435004023393853975177239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913338697858471966902985 1435004023393853975177239)
              ·
                refine ⟨2152506035090780962765859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435004023393853975177239 2152506035090780962765859)
                ·
                  refine ⟨3228759052636171444148789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152506035090780962765859 3228759052636171444148789)
                  ·
                    refine ⟨302696161184641072888949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3228759052636171444148789 302696161184641072888949)
                    ·
                      rfl

theorem cell22_884248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_884248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884248 prefixEnd_884248 := by exact prefixLift 884248
  have htrace : WordTrace (prefixWord ++ tailWord_884248) baseStart_884248 baseEnd_884248 := by
    simpa [prefixWord, tailWord_884248, baseEnd_884248] using wordTrace_append hprefix tailTrace_884248
  have hstable : (prefixWord ++ tailWord_884248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884248).length < 2 ^ (prefixWord ++ tailWord_884248).sum := by decide
  have hdescent : baseEnd_884248 < baseStart_884248 := by decide
  rcases family_descends (prefixWord ++ tailWord_884248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884278 : List Nat := [5, 1, 2, 1, 3, 1, 9]
def baseStart_884278 : Nat := 118140960795 + 884278 * 2 ^ 59
def prefixEnd_884278 : Nat := 4983230072969 + 3 ^ 40 * 884278 * 2
def baseEnd_884278 : Nat := 11211349288804851653291

theorem tailTrace_884278 : CollatzResearch.WordTrace tailWord_884278 prefixEnd_884278 11211349288804851653291 := by
  unfold tailWord_884278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015766768151206468998843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21501512193612869002654325 2015766768151206468998843)
  ·
    refine ⟨3023650152226809703498265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015766768151206468998843 3023650152226809703498265)
    ·
      refine ⟨2267737614170107277623699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3023650152226809703498265 2267737614170107277623699)
      ·
        refine ⟨3401606421255160916435549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267737614170107277623699 3401606421255160916435549)
        ·
          refine ⟨1275602407970685343663331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3401606421255160916435549 1275602407970685343663331)
          ·
            refine ⟨1913403611956028015494997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275602407970685343663331 1913403611956028015494997)
            ·
              refine ⟨11211349288804851653291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1913403611956028015494997 11211349288804851653291)
              ·
                rfl

theorem cell22_884278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 9].length) (baseStart_884278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884278 prefixEnd_884278 := by exact prefixLift 884278
  have htrace : WordTrace (prefixWord ++ tailWord_884278) baseStart_884278 baseEnd_884278 := by
    simpa [prefixWord, tailWord_884278, baseEnd_884278] using wordTrace_append hprefix tailTrace_884278
  have hstable : (prefixWord ++ tailWord_884278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884278).length < 2 ^ (prefixWord ++ tailWord_884278).sum := by decide
  have hdescent : baseEnd_884278 < baseStart_884278 := by decide
  rcases family_descends (prefixWord ++ tailWord_884278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884293 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_884293 : Nat := 118140960795 + 884293 * 2 ^ 59
def prefixEnd_884293 : Nat := 4983230072969 + 3 ^ 40 * 884293 * 2
def baseEnd_884293 : Nat := 302711565604275955513811

theorem tailTrace_884293 : CollatzResearch.WordTrace tailWord_884293 prefixEnd_884293 302711565604275955513811 := by
  unfold tailWord_884293
  simp only [CollatzResearch.WordTrace]
  refine ⟨32252815385364961065777533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21501876923576640710518355 32252815385364961065777533)
  ·
    refine ⟨12094805769511860399666575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32252815385364961065777533 12094805769511860399666575)
    ·
      refine ⟨18142208654267790599499863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12094805769511860399666575 18142208654267790599499863)
      ·
        refine ⟨27213312981401685899249795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18142208654267790599499863 27213312981401685899249795)
        ·
          refine ⟨40819969472102528848874693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27213312981401685899249795 40819969472102528848874693)
          ·
            refine ⟨7653744276019224159164005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40819969472102528848874693 7653744276019224159164005)
            ·
              refine ⟨1435077051753604529843251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7653744276019224159164005 1435077051753604529843251)
              ·
                refine ⟨2152615577630406794764877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435077051753604529843251 2152615577630406794764877)
                ·
                  refine ⟨807230841611402548036829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2152615577630406794764877 807230841611402548036829)
                  ·
                    refine ⟨302711565604275955513811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807230841611402548036829 302711565604275955513811)
                    ·
                      rfl

theorem cell22_884293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_884293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884293 prefixEnd_884293 := by exact prefixLift 884293
  have htrace : WordTrace (prefixWord ++ tailWord_884293) baseStart_884293 baseEnd_884293 := by
    simpa [prefixWord, tailWord_884293, baseEnd_884293] using wordTrace_append hprefix tailTrace_884293
  have hstable : (prefixWord ++ tailWord_884293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884293).length < 2 ^ (prefixWord ++ tailWord_884293).sum := by decide
  have hdescent : baseEnd_884293 < baseStart_884293 := by decide
  rcases family_descends (prefixWord ++ tailWord_884293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884370 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_884370 : Nat := 118140960795 + 884370 * 2 ^ 59
def prefixEnd_884370 : Nat := 4983230072969 + 3 ^ 40 * 884370 * 2
def baseEnd_884370 : Nat := 302737924277873421338575

theorem tailTrace_884370 : CollatzResearch.WordTrace tailWord_884370 prefixEnd_884370 302737924277873421338575 := by
  unfold tailWord_884370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063905951521500804082641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21503749204057335477553709 8063905951521500804082641)
  ·
    refine ⟨6047929463641125603061981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8063905951521500804082641 6047929463641125603061981)
    ·
      refine ⟨2267973548865422101148243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6047929463641125603061981 2267973548865422101148243)
      ·
        refine ⟨3401960323298133151722365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2267973548865422101148243 3401960323298133151722365)
        ·
          refine ⟨1275735121236799931895887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3401960323298133151722365 1275735121236799931895887)
          ·
            refine ⟨1913602681855199897843831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275735121236799931895887 1913602681855199897843831)
            ·
              refine ⟨2870404022782799846765747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913602681855199897843831 2870404022782799846765747)
              ·
                refine ⟨4305606034174199770148621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870404022782799846765747 4305606034174199770148621)
                ·
                  refine ⟨1614602262815324913805733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4305606034174199770148621 1614602262815324913805733)
                  ·
                    refine ⟨302737924277873421338575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1614602262815324913805733 302737924277873421338575)
                    ·
                      rfl

theorem cell22_884370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_884370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884370 prefixEnd_884370 := by exact prefixLift 884370
  have htrace : WordTrace (prefixWord ++ tailWord_884370) baseStart_884370 baseEnd_884370 := by
    simpa [prefixWord, tailWord_884370, baseEnd_884370] using wordTrace_append hprefix tailTrace_884370
  have hstable : (prefixWord ++ tailWord_884370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884370).length < 2 ^ (prefixWord ++ tailWord_884370).sum := by decide
  have hdescent : baseEnd_884370 < baseStart_884370 := by decide
  rcases family_descends (prefixWord ++ tailWord_884370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884438 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_884438 : Nat := 118140960795 + 884438 * 2 ^ 59
def prefixEnd_884438 : Nat := 4983230072969 + 3 ^ 40 * 884438 * 2
def baseEnd_884438 : Nat := 302761202067543910638367

theorem tailTrace_884438 : CollatzResearch.WordTrace tailWord_884438 prefixEnd_884438 302761202067543910638367 := by
  unfold tailWord_884438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016131498114978176862873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21505402646559767219870645 2016131498114978176862873)
  ·
    refine ⟨1512098623586233632647155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2016131498114978176862873 1512098623586233632647155)
    ·
      refine ⟨2268147935379350448970733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512098623586233632647155 2268147935379350448970733)
      ·
        refine ⟨850555475767256418364025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2268147935379350448970733 850555475767256418364025)
        ·
          refine ⟨637916606825442313773019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850555475767256418364025 637916606825442313773019)
          ·
            refine ⟨956874910238163470659529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637916606825442313773019 956874910238163470659529)
            ·
              refine ⟨717656182678622602994647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956874910238163470659529 717656182678622602994647)
              ·
                refine ⟨1076484274017933904491971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717656182678622602994647 1076484274017933904491971)
                ·
                  refine ⟨1614726411026900856737957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076484274017933904491971 1614726411026900856737957)
                  ·
                    refine ⟨302761202067543910638367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1614726411026900856737957 302761202067543910638367)
                    ·
                      rfl

theorem cell22_884438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_884438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884438 prefixEnd_884438 := by exact prefixLift 884438
  have htrace : WordTrace (prefixWord ++ tailWord_884438) baseStart_884438 baseEnd_884438 := by
    simpa [prefixWord, tailWord_884438, baseEnd_884438] using wordTrace_append hprefix tailTrace_884438
  have hstable : (prefixWord ++ tailWord_884438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884438).length < 2 ^ (prefixWord ++ tailWord_884438).sum := by decide
  have hdescent : baseEnd_884438 < baseStart_884438 := by decide
  rcases family_descends (prefixWord ++ tailWord_884438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884462 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_884462 : Nat := 118140960795 + 884462 * 2 ^ 59
def prefixEnd_884462 : Nat := 4983230072969 + 3 ^ 40 * 884462 * 2
def baseEnd_884462 : Nat := 302769417758015848038293

theorem tailTrace_884462 : CollatzResearch.WordTrace tailWord_884462 prefixEnd_884462 302769417758015848038293 := by
  unfold tailWord_884462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032372415219087866084955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21505986214501801952453093 4032372415219087866084955)
  ·
    refine ⟨6048558622828631799127433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032372415219087866084955 6048558622828631799127433)
    ·
      refine ⟨4536418967121473849345575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6048558622828631799127433 4536418967121473849345575)
      ·
        refine ⟨6804628450682210774018363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536418967121473849345575 6804628450682210774018363)
        ·
          refine ⟨10206942676023316161027545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804628450682210774018363 10206942676023316161027545)
          ·
            refine ⟨7655207007017487120770659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10206942676023316161027545 7655207007017487120770659)
            ·
              refine ⟨11482810510526230681155989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655207007017487120770659 11482810510526230681155989)
              ·
                refine ⟨538256742680917063179187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11482810510526230681155989 538256742680917063179187)
                ·
                  refine ⟨807385114021375594768781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538256742680917063179187 807385114021375594768781)
                  ·
                    refine ⟨302769417758015848038293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807385114021375594768781 302769417758015848038293)
                    ·
                      rfl

theorem cell22_884462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_884462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884462 prefixEnd_884462 := by exact prefixLift 884462
  have htrace : WordTrace (prefixWord ++ tailWord_884462) baseStart_884462 baseEnd_884462 := by
    simpa [prefixWord, tailWord_884462, baseEnd_884462] using wordTrace_append hprefix tailTrace_884462
  have hstable : (prefixWord ++ tailWord_884462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884462).length < 2 ^ (prefixWord ++ tailWord_884462).sum := by decide
  have hdescent : baseEnd_884462 < baseStart_884462 := by decide
  rcases family_descends (prefixWord ++ tailWord_884462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884520 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_884520 : Nat := 118140960795 + 884520 * 2 ^ 59
def prefixEnd_884520 : Nat := 4983230072969 + 3 ^ 40 * 884520 * 2
def baseEnd_884520 : Nat := 100929757447774343362705

theorem tailTrace_884520 : CollatzResearch.WordTrace tailWord_884520 prefixEnd_884520 100929757447774343362705 := by
  unfold tailWord_884520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130547377771289417145507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21507396503695052556194009 16130547377771289417145507)
  ·
    refine ⟨24195821066656934125718261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16130547377771289417145507 24195821066656934125718261)
    ·
      refine ⟨2268358224999087574286087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24195821066656934125718261 2268358224999087574286087)
      ·
        refine ⟨3402537337498631361429131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268358224999087574286087 3402537337498631361429131)
        ·
          refine ⟨5103806006247947042143697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402537337498631361429131 5103806006247947042143697)
          ·
            refine ⟨3827854504685960281607773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5103806006247947042143697 3827854504685960281607773)
            ·
              refine ⟨1435445439257235105602915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3827854504685960281607773 1435445439257235105602915)
              ·
                refine ⟨2153168158885852658404373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435445439257235105602915 2153168158885852658404373)
                ·
                  refine ⟨100929757447774343362705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2153168158885852658404373 100929757447774343362705)
                  ·
                    rfl

theorem cell22_884520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_884520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884520 prefixEnd_884520 := by exact prefixLift 884520
  have htrace : WordTrace (prefixWord ++ tailWord_884520) baseStart_884520 baseEnd_884520 := by
    simpa [prefixWord, tailWord_884520, baseEnd_884520] using wordTrace_append hprefix tailTrace_884520
  have hstable : (prefixWord ++ tailWord_884520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884520).length < 2 ^ (prefixWord ++ tailWord_884520).sum := by decide
  have hdescent : baseEnd_884520 < baseStart_884520 := by decide
  rcases family_descends (prefixWord ++ tailWord_884520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884526 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_884526 : Nat := 118140960795 + 884526 * 2 ^ 59
def prefixEnd_884526 : Nat := 4983230072969 + 3 ^ 40 * 884526 * 2
def baseEnd_884526 : Nat := 100930442088647004812699

theorem tailTrace_884526 : CollatzResearch.WordTrace tailWord_884526 prefixEnd_884526 100930442088647004812699 := by
  unfold tailWord_884526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032664199190105232376179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21507542395680561239339621 4032664199190105232376179)
  ·
    refine ⟨6048996298785157848564269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032664199190105232376179 6048996298785157848564269)
    ·
      refine ⟨2268373612044434193211601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6048996298785157848564269 2268373612044434193211601)
      ·
        refine ⟨1701280209033325644908701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2268373612044434193211601 1701280209033325644908701)
        ·
          refine ⟨637980078387497116840763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1701280209033325644908701 637980078387497116840763)
          ·
            refine ⟨956970117581245675261145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637980078387497116840763 956970117581245675261145)
            ·
              refine ⟨717727588185934256445859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956970117581245675261145 717727588185934256445859)
              ·
                refine ⟨1076591382278901384668789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717727588185934256445859 1076591382278901384668789)
                ·
                  refine ⟨100930442088647004812699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076591382278901384668789 100930442088647004812699)
                  ·
                    rfl

theorem cell22_884526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_884526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884526 prefixEnd_884526 := by exact prefixLift 884526
  have htrace : WordTrace (prefixWord ++ tailWord_884526) baseStart_884526 baseEnd_884526 := by
    simpa [prefixWord, tailWord_884526, baseEnd_884526] using wordTrace_append hprefix tailTrace_884526
  have hstable : (prefixWord ++ tailWord_884526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884526).length < 2 ^ (prefixWord ++ tailWord_884526).sum := by decide
  have hdescent : baseEnd_884526 < baseStart_884526 := by decide
  rcases family_descends (prefixWord ++ tailWord_884526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884597 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_884597 : Nat := 118140960795 + 884597 * 2 ^ 59
def prefixEnd_884597 : Nat := 4983230072969 + 3 ^ 40 * 884597 * 2
def baseEnd_884597 : Nat := 302815631016920495912879

theorem tailTrace_884597 : CollatzResearch.WordTrace tailWord_884597 prefixEnd_884597 302815631016920495912879 := by
  unfold tailWord_884597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32263903176263620984844045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21509268784175747323229363 32263903176263620984844045)
  ·
    refine ⟨12098963691098857869316517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32263903176263620984844045 12098963691098857869316517)
    ·
      refine ⟨2268555692081035850496847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12098963691098857869316517 2268555692081035850496847)
      ·
        refine ⟨3402833538121553775745271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268555692081035850496847 3402833538121553775745271)
        ·
          refine ⟨5104250307182330663617907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402833538121553775745271 5104250307182330663617907)
          ·
            refine ⟨7656375460773495995426861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104250307182330663617907 7656375460773495995426861)
            ·
              refine ⟨2871140797790060998285073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7656375460773495995426861 2871140797790060998285073)
              ·
                refine ⟨2153355598342545748713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871140797790060998285073 2153355598342545748713805)
                ·
                  refine ⟨807508349378454655767677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2153355598342545748713805 807508349378454655767677)
                  ·
                    refine ⟨302815631016920495912879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807508349378454655767677 302815631016920495912879)
                    ·
                      rfl

theorem cell22_884597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_884597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884597 prefixEnd_884597 := by exact prefixLift 884597
  have htrace : WordTrace (prefixWord ++ tailWord_884597) baseStart_884597 baseEnd_884597 := by
    simpa [prefixWord, tailWord_884597, baseEnd_884597] using wordTrace_append hprefix tailTrace_884597
  have hstable : (prefixWord ++ tailWord_884597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884597).length < 2 ^ (prefixWord ++ tailWord_884597).sum := by decide
  have hdescent : baseEnd_884597 < baseStart_884597 := by decide
  rcases family_descends (prefixWord ++ tailWord_884597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884608 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_884608 : Nat := 118140960795 + 884608 * 2 ^ 59
def prefixEnd_884608 : Nat := 4983230072969 + 3 ^ 40 * 884608 * 2
def baseEnd_884608 : Nat := 302819396541720133887845

theorem tailTrace_884608 : CollatzResearch.WordTrace tailWord_884608 prefixEnd_884608 302819396541720133887845 := by
  unfold tailWord_884608
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132152189611884931747239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21509536252815846575662985 16132152189611884931747239)
  ·
    refine ⟨24198228284417827397620859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16132152189611884931747239 24198228284417827397620859)
    ·
      refine ⟨36297342426626741096431289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24198228284417827397620859 36297342426626741096431289)
      ·
        refine ⟨27223006819970055822323467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36297342426626741096431289 27223006819970055822323467)
        ·
          refine ⟨40834510229955083733485201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27223006819970055822323467 40834510229955083733485201)
          ·
            refine ⟨30625882672466312800113901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40834510229955083733485201 30625882672466312800113901)
            ·
              refine ⟨11484706002174867300042713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30625882672466312800113901 11484706002174867300042713)
              ·
                refine ⟨8613529501631150475032035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11484706002174867300042713 8613529501631150475032035)
                ·
                  refine ⟨12920294252446725712548053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8613529501631150475032035 12920294252446725712548053)
                  ·
                    refine ⟨302819396541720133887845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12920294252446725712548053 302819396541720133887845)
                    ·
                      rfl

theorem cell22_884608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_884608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884608 prefixEnd_884608 := by exact prefixLift 884608
  have htrace : WordTrace (prefixWord ++ tailWord_884608) baseStart_884608 baseEnd_884608 := by
    simpa [prefixWord, tailWord_884608, baseEnd_884608] using wordTrace_append hprefix tailTrace_884608
  have hstable : (prefixWord ++ tailWord_884608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884608).length < 2 ^ (prefixWord ++ tailWord_884608).sum := by decide
  have hdescent : baseEnd_884608 < baseStart_884608 := by decide
  rcases family_descends (prefixWord ++ tailWord_884608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884657 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_884657 : Nat := 118140960795 + 884657 * 2 ^ 59
def prefixEnd_884657 : Nat := 4983230072969 + 3 ^ 40 * 884657 * 2
def baseEnd_884657 : Nat := 302836170243100339412695

theorem tailTrace_884657 : CollatzResearch.WordTrace tailWord_884657 prefixEnd_884657 302836170243100339412695 := by
  unfold tailWord_884657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32266091556046251232028225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21510727704030834154685483 32266091556046251232028225)
  ·
    refine ⟨24199568667034688424021169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32266091556046251232028225 24199568667034688424021169)
    ·
      refine ⟨18149676500276016318015877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24199568667034688424021169 18149676500276016318015877)
      ·
        refine ⟨3403064343801753059627977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18149676500276016318015877 3403064343801753059627977)
        ·
          refine ⟨2552298257851314794720983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3403064343801753059627977 2552298257851314794720983)
          ·
            refine ⟨3828447386776972192081475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552298257851314794720983 3828447386776972192081475)
            ·
              refine ⟨5742671080165458288122213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828447386776972192081475 5742671080165458288122213)
              ·
                refine ⟨1076750827531023429022915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5742671080165458288122213 1076750827531023429022915)
                ·
                  refine ⟨1615126241296535143534373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1076750827531023429022915 1615126241296535143534373)
                  ·
                    refine ⟨302836170243100339412695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615126241296535143534373 302836170243100339412695)
                    ·
                      rfl

theorem cell22_884657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_884657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884657 prefixEnd_884657 := by exact prefixLift 884657
  have htrace : WordTrace (prefixWord ++ tailWord_884657) baseStart_884657 baseEnd_884657 := by
    simpa [prefixWord, tailWord_884657, baseEnd_884657] using wordTrace_append hprefix tailTrace_884657
  have hstable : (prefixWord ++ tailWord_884657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884657).length < 2 ^ (prefixWord ++ tailWord_884657).sum := by decide
  have hdescent : baseEnd_884657 < baseStart_884657 := by decide
  rcases family_descends (prefixWord ++ tailWord_884657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884687 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 2, 3]
def baseStart_884687 : Nat := 118140960795 + 884687 * 2 ^ 59
def prefixEnd_884687 : Nat := 4983230072969 + 3 ^ 40 * 884687 * 2
def baseEnd_884687 : Nat := 302846439856190261162603

theorem tailTrace_884687 : CollatzResearch.WordTrace tailWord_884687 prefixEnd_884687 302846439856190261162603 := by
  unfold tailWord_884687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267185745937566355620315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21511457163958377570413543 32267185745937566355620315)
  ·
    refine ⟨48400778618906349533430473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32267185745937566355620315 48400778618906349533430473)
    ·
      refine ⟨36300583964179762150072855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48400778618906349533430473 36300583964179762150072855)
      ·
        refine ⟨54450875946269643225109283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36300583964179762150072855 54450875946269643225109283)
        ·
          refine ⟨81676313919404464837663925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54450875946269643225109283 81676313919404464837663925)
          ·
            refine ⟨7657154429944168578530993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81676313919404464837663925 7657154429944168578530993)
            ·
              refine ⟨5742865822458126433898245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657154429944168578530993 5742865822458126433898245)
              ·
                refine ⟨1076787341710898706355921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5742865822458126433898245 1076787341710898706355921)
                ·
                  refine ⟨807590506283174029766941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076787341710898706355921 807590506283174029766941)
                  ·
                    refine ⟨302846439856190261162603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807590506283174029766941 302846439856190261162603)
                    ·
                      rfl

theorem cell22_884687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_884687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884687 prefixEnd_884687 := by exact prefixLift 884687
  have htrace : WordTrace (prefixWord ++ tailWord_884687) baseStart_884687 baseEnd_884687 := by
    simpa [prefixWord, tailWord_884687, baseEnd_884687] using wordTrace_append hprefix tailTrace_884687
  have hstable : (prefixWord ++ tailWord_884687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884687).length < 2 ^ (prefixWord ++ tailWord_884687).sum := by decide
  have hdescent : baseEnd_884687 < baseStart_884687 := by decide
  rcases family_descends (prefixWord ++ tailWord_884687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884740 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_884740 : Nat := 118140960795 + 884740 * 2 ^ 59
def prefixEnd_884740 : Nat := 4983230072969 + 3 ^ 40 * 884740 * 2
def baseEnd_884740 : Nat := 100954860946438596529147

theorem tailTrace_884740 : CollatzResearch.WordTrace tailWord_884740 prefixEnd_884740 100954860946438596529147 := by
  unfold tailWord_884740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16134559407372778203649837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21512745876497037604866449 16134559407372778203649837)
  ·
    refine ⟨6050459777764791826368689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16134559407372778203649837 6050459777764791826368689)
    ·
      refine ⟨4537844833323593869776517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6050459777764791826368689 4537844833323593869776517)
      ·
        refine ⟨850845906248173850583097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4537844833323593869776517 850845906248173850583097)
        ·
          refine ⟨638134429686130387937323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850845906248173850583097 638134429686130387937323)
          ·
            refine ⟨957201644529195581905985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638134429686130387937323 957201644529195581905985)
            ·
              refine ⟨717901233396896686429489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957201644529195581905985 717901233396896686429489)
              ·
                refine ⟨538425925047672514822117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717901233396896686429489 538425925047672514822117)
                ·
                  refine ⟨100954860946438596529147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538425925047672514822117 100954860946438596529147)
                  ·
                    rfl

theorem cell22_884740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_884740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884740 prefixEnd_884740 := by exact prefixLift 884740
  have htrace : WordTrace (prefixWord ++ tailWord_884740) baseStart_884740 baseEnd_884740 := by
    simpa [prefixWord, tailWord_884740, baseEnd_884740] using wordTrace_append hprefix tailTrace_884740
  have hstable : (prefixWord ++ tailWord_884740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884740).length < 2 ^ (prefixWord ++ tailWord_884740).sum := by decide
  have hdescent : baseEnd_884740 < baseStart_884740 := by decide
  rcases family_descends (prefixWord ++ tailWord_884740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884762 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_884762 : Nat := 118140960795 + 884762 * 2 ^ 59
def prefixEnd_884762 : Nat := 4983230072969 + 3 ^ 40 * 884762 * 2
def baseEnd_884762 : Nat := 100957371296305021845791

theorem tailTrace_884762 : CollatzResearch.WordTrace tailWord_884762 prefixEnd_884762 100957371296305021845791 := by
  unfold tailWord_884762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067480305166463541150135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21513280813777236109733693 8067480305166463541150135)
  ·
    refine ⟨12101220457749695311725203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8067480305166463541150135 12101220457749695311725203)
    ·
      refine ⟨18151830686624542967587805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12101220457749695311725203 18151830686624542967587805)
      ·
        refine ⟨6806936507484203612845427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18151830686624542967587805 6806936507484203612845427)
        ·
          refine ⟨10210404761226305419268141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806936507484203612845427 10210404761226305419268141)
          ·
            refine ⟨3828901785459864532225553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10210404761226305419268141 3828901785459864532225553)
            ·
              refine ⟨2871676339094898399169165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828901785459864532225553 2871676339094898399169165)
              ·
                refine ⟨1076878627160586899688437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2871676339094898399169165 1076878627160586899688437)
                ·
                  refine ⟨100957371296305021845791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1076878627160586899688437 100957371296305021845791)
                  ·
                    rfl

theorem cell22_884762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_884762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884762 prefixEnd_884762 := by exact prefixLift 884762
  have htrace : WordTrace (prefixWord ++ tailWord_884762) baseStart_884762 baseEnd_884762 := by
    simpa [prefixWord, tailWord_884762, baseEnd_884762] using wordTrace_append hprefix tailTrace_884762
  have hstable : (prefixWord ++ tailWord_884762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884762).length < 2 ^ (prefixWord ++ tailWord_884762).sum := by decide
  have hdescent : baseEnd_884762 < baseStart_884762 := by decide
  rcases family_descends (prefixWord ++ tailWord_884762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884807 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 6]
def baseStart_884807 : Nat := 118140960795 + 884807 * 2 ^ 59
def prefixEnd_884807 : Nat := 4983230072969 + 3 ^ 40 * 884807 * 2
def baseEnd_884807 : Nat := 100962506102849982720745

theorem tailTrace_884807 : CollatzResearch.WordTrace tailWord_884807 prefixEnd_884807 100962506102849982720745 := by
  unfold tailWord_884807
  simp only [CollatzResearch.WordTrace]
  refine ⟨32271562505502826849988675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21514375003668551233325783 32271562505502826849988675)
  ·
    refine ⟨48407343758254240274983013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32271562505502826849988675 48407343758254240274983013)
    ·
      refine ⟨9076376954672670051559315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48407343758254240274983013 9076376954672670051559315)
      ·
        refine ⟨13614565432009005077338973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076376954672670051559315 13614565432009005077338973)
        ·
          refine ⟨5105462037003376904002115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13614565432009005077338973 5105462037003376904002115)
          ·
            refine ⟨7658193055505065356003173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105462037003376904002115 7658193055505065356003173)
            ·
              refine ⟨1435911197907199754250595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7658193055505065356003173 1435911197907199754250595)
              ·
                refine ⟨2153866796860799631375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435911197907199754250595 2153866796860799631375893)
                ·
                  refine ⟨100962506102849982720745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2153866796860799631375893 100962506102849982720745)
                  ·
                    rfl

theorem cell22_884807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 6].length) (baseStart_884807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884807 prefixEnd_884807 := by exact prefixLift 884807
  have htrace : WordTrace (prefixWord ++ tailWord_884807) baseStart_884807 baseEnd_884807 := by
    simpa [prefixWord, tailWord_884807, baseEnd_884807] using wordTrace_append hprefix tailTrace_884807
  have hstable : (prefixWord ++ tailWord_884807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884807).length < 2 ^ (prefixWord ++ tailWord_884807).sum := by decide
  have hdescent : baseEnd_884807 < baseStart_884807 := by decide
  rcases family_descends (prefixWord ++ tailWord_884807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884837 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_884837 : Nat := 118140960795 + 884837 * 2 ^ 59
def prefixEnd_884837 : Nat := 4983230072969 + 3 ^ 40 * 884837 * 2
def baseEnd_884837 : Nat := 302897787921639869912143

theorem tailTrace_884837 : CollatzResearch.WordTrace tailWord_884837 prefixEnd_884837 302897787921639869912143 := by
  unfold tailWord_884837
  simp only [CollatzResearch.WordTrace]
  refine ⟨32272656695394141973580765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21515104463596094649053843 32272656695394141973580765)
  ·
    refine ⟨12102246260772803240092787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32272656695394141973580765 12102246260772803240092787)
    ·
      refine ⟨18153369391159204860139181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12102246260772803240092787 18153369391159204860139181)
      ·
        refine ⟨6807513521684701822552193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18153369391159204860139181 6807513521684701822552193)
        ·
          refine ⟨5105635141263526366914145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807513521684701822552193 5105635141263526366914145)
          ·
            refine ⟨3829226355947644775185609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5105635141263526366914145 3829226355947644775185609)
            ·
              refine ⟨2871919766960733581389207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829226355947644775185609 2871919766960733581389207)
              ·
                refine ⟨4307879650441100372083811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871919766960733581389207 4307879650441100372083811)
                ·
                  refine ⟨6461819475661650558125717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4307879650441100372083811 6461819475661650558125717)
                  ·
                    refine ⟨302897787921639869912143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6461819475661650558125717 302897787921639869912143)
                    ·
                      rfl

theorem cell22_884837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_884837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884837 prefixEnd_884837 := by exact prefixLift 884837
  have htrace : WordTrace (prefixWord ++ tailWord_884837) baseStart_884837 baseEnd_884837 := by
    simpa [prefixWord, tailWord_884837, baseEnd_884837] using wordTrace_append hprefix tailTrace_884837
  have hstable : (prefixWord ++ tailWord_884837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884837).length < 2 ^ (prefixWord ++ tailWord_884837).sum := by decide
  have hdescent : baseEnd_884837 < baseStart_884837 := by decide
  rcases family_descends (prefixWord ++ tailWord_884837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884854 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_884854 : Nat := 118140960795 + 884854 * 2 ^ 59
def prefixEnd_884854 : Nat := 4983230072969 + 3 ^ 40 * 884854 * 2
def baseEnd_884854 : Nat := 302903607369057492237091

theorem tailTrace_884854 : CollatzResearch.WordTrace tailWord_884854 prefixEnd_884854 302903607369057492237091 := by
  unfold tailWord_884854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017079796020784617309351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21515517824221702584633077 2017079796020784617309351)
  ·
    refine ⟨3025619694031176925964027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2017079796020784617309351 3025619694031176925964027)
    ·
      refine ⟨4538429541046765388946041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025619694031176925964027 4538429541046765388946041)
      ·
        refine ⟨3403822155785074041709531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4538429541046765388946041 3403822155785074041709531)
        ·
          refine ⟨5105733233677611062564297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403822155785074041709531 5105733233677611062564297)
          ·
            refine ⟨3829299925258208296923223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5105733233677611062564297 3829299925258208296923223)
            ·
              refine ⟨5743949887887312445384835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829299925258208296923223 5743949887887312445384835)
              ·
                refine ⟨8615924831830968668077253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743949887887312445384835 8615924831830968668077253)
                ·
                  refine ⟨1615485905968306625264485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8615924831830968668077253 1615485905968306625264485)
                  ·
                    refine ⟨302903607369057492237091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615485905968306625264485 302903607369057492237091)
                    ·
                      rfl

theorem cell22_884854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_884854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884854 prefixEnd_884854 := by exact prefixLift 884854
  have htrace : WordTrace (prefixWord ++ tailWord_884854) baseStart_884854 baseEnd_884854 := by
    simpa [prefixWord, tailWord_884854, baseEnd_884854] using wordTrace_append hprefix tailTrace_884854
  have hstable : (prefixWord ++ tailWord_884854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884854).length < 2 ^ (prefixWord ++ tailWord_884854).sum := by decide
  have hdescent : baseEnd_884854 < baseStart_884854 := by decide
  rcases family_descends (prefixWord ++ tailWord_884854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884901 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_884901 : Nat := 118140960795 + 884901 * 2 ^ 59
def prefixEnd_884901 : Nat := 4983230072969 + 3 ^ 40 * 884901 * 2
def baseEnd_884901 : Nat := 302919696429565036311947

theorem tailTrace_884901 : CollatzResearch.WordTrace tailWord_884901 prefixEnd_884901 302919696429565036311947 := by
  unfold tailWord_884901
  simp only [CollatzResearch.WordTrace]
  refine ⟨32274990967162280903910557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21516660644774853935940371 32274990967162280903910557)
  ·
    refine ⟨12103121612685855338966459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32274990967162280903910557 12103121612685855338966459)
    ·
      refine ⟨18154682419028783008449689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103121612685855338966459 18154682419028783008449689)
      ·
        refine ⟨13616011814271587256337267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18154682419028783008449689 13616011814271587256337267)
        ·
          refine ⟨20424017721407380884505901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616011814271587256337267 20424017721407380884505901)
          ·
            refine ⟨7659006645527767831689713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20424017721407380884505901 7659006645527767831689713)
            ·
              refine ⟨5744254984145825873767285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659006645527767831689713 5744254984145825873767285)
              ·
                refine ⟨538523904763671175665683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5744254984145825873767285 538523904763671175665683)
                ·
                  refine ⟨807785857145506763498525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538523904763671175665683 807785857145506763498525)
                  ·
                    refine ⟨302919696429565036311947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807785857145506763498525 302919696429565036311947)
                    ·
                      rfl

theorem cell22_884901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_884901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884901 prefixEnd_884901 := by exact prefixLift 884901
  have htrace : WordTrace (prefixWord ++ tailWord_884901) baseStart_884901 baseEnd_884901 := by
    simpa [prefixWord, tailWord_884901, baseEnd_884901] using wordTrace_append hprefix tailTrace_884901
  have hstable : (prefixWord ++ tailWord_884901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884901).length < 2 ^ (prefixWord ++ tailWord_884901).sum := by decide
  have hdescent : baseEnd_884901 < baseStart_884901 := by decide
  rcases family_descends (prefixWord ++ tailWord_884901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884914 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_884914 : Nat := 118140960795 + 884914 * 2 ^ 59
def prefixEnd_884914 : Nat := 4983230072969 + 3 ^ 40 * 884914 * 2
def baseEnd_884914 : Nat := 100974715531745778578969

theorem tailTrace_884914 : CollatzResearch.WordTrace tailWord_884914 prefixEnd_884914 100974715531745778578969 := by
  unfold tailWord_884914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8068866279028796031033449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21516976744076789416089197 8068866279028796031033449)
  ·
    refine ⟨6051649709271597023275087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8068866279028796031033449 6051649709271597023275087)
    ·
      refine ⟨9077474563907395534912631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6051649709271597023275087 9077474563907395534912631)
      ·
        refine ⟨13616211845861093302368947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077474563907395534912631 13616211845861093302368947)
        ·
          refine ⟨20424317768791639953553421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616211845861093302368947 20424317768791639953553421)
          ·
            refine ⟨7659119163296864982582533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20424317768791639953553421 7659119163296864982582533)
            ·
              refine ⟨1436084843118162184234225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7659119163296864982582533 1436084843118162184234225)
              ·
                refine ⟨1077063632338621638175669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436084843118162184234225 1077063632338621638175669)
                ·
                  refine ⟨100974715531745778578969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1077063632338621638175669 100974715531745778578969)
                  ·
                    rfl

theorem cell22_884914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_884914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_884914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_884914 prefixEnd_884914 := by exact prefixLift 884914
  have htrace : WordTrace (prefixWord ++ tailWord_884914) baseStart_884914 baseEnd_884914 := by
    simpa [prefixWord, tailWord_884914, baseEnd_884914] using wordTrace_append hprefix tailTrace_884914
  have hstable : (prefixWord ++ tailWord_884914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884914).length < 2 ^ (prefixWord ++ tailWord_884914).sum := by decide
  have hdescent : baseEnd_884914 < baseStart_884914 := by decide
  rcases family_descends (prefixWord ++ tailWord_884914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885019 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 5, 3]
def baseStart_885019 : Nat := 118140960795 + 885019 * 2 ^ 59
def prefixEnd_885019 : Nat := 4983230072969 + 3 ^ 40 * 885019 * 2
def baseEnd_885019 : Nat := 302960090241052061861585

theorem tailTrace_885019 : CollatzResearch.WordTrace tailWord_885019 prefixEnd_885019 302960090241052061861585 := by
  unfold tailWord_885019
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279294780734787056706111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21519529853823191371137407 32279294780734787056706111)
  ·
    refine ⟨48418942171102180585059167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32279294780734787056706111 48418942171102180585059167)
    ·
      refine ⟨72628413256653270877588751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48418942171102180585059167 72628413256653270877588751)
      ·
        refine ⟨108942619884979906316383127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72628413256653270877588751 108942619884979906316383127)
        ·
          refine ⟨163413929827469859474574691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108942619884979906316383127 163413929827469859474574691)
          ·
            refine ⟨245120894741204789211862037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163413929827469859474574691 245120894741204789211862037)
            ·
              refine ⟨11490041940993974494306033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245120894741204789211862037 11490041940993974494306033)
              ·
                refine ⟨8617531455745480870729525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11490041940993974494306033 8617531455745480870729525)
                ·
                  refine ⟨807893573976138831630893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8617531455745480870729525 807893573976138831630893)
                  ·
                    refine ⟨302960090241052061861585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807893573976138831630893 302960090241052061861585)
                    ·
                      rfl

theorem cell22_885019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 3].length) (baseStart_885019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885019 prefixEnd_885019 := by exact prefixLift 885019
  have htrace : WordTrace (prefixWord ++ tailWord_885019) baseStart_885019 baseEnd_885019 := by
    simpa [prefixWord, tailWord_885019, baseEnd_885019] using wordTrace_append hprefix tailTrace_885019
  have hstable : (prefixWord ++ tailWord_885019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885019).length < 2 ^ (prefixWord ++ tailWord_885019).sum := by decide
  have hdescent : baseEnd_885019 < baseStart_885019 := by decide
  rcases family_descends (prefixWord ++ tailWord_885019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885021 : List Nat := [1, 4, 2, 3, 2, 2, 8]
def baseStart_885021 : Nat := 118140960795 + 885021 * 2 ^ 59
def prefixEnd_885021 : Nat := 4983230072969 + 3 ^ 40 * 885021 * 2
def baseEnd_885021 : Nat := 11220769440071286048577

theorem tailTrace_885021 : CollatzResearch.WordTrace tailWord_885021 prefixEnd_885021 11220769440071286048577 := by
  unfold tailWord_885021
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279367726727541398278917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21519578484485027598852611 32279367726727541398278917)
  ·
    refine ⟨6052381448761414012177297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32279367726727541398278917 6052381448761414012177297)
    ·
      refine ⟨4539286086571060509132973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6052381448761414012177297 4539286086571060509132973)
      ·
        refine ⟨1702232282464147690924865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4539286086571060509132973 1702232282464147690924865)
        ·
          refine ⟨1276674211848110768193649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702232282464147690924865 1276674211848110768193649)
          ·
            refine ⟨957505658886083076145237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276674211848110768193649 957505658886083076145237)
            ·
              refine ⟨11220769440071286048577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 957505658886083076145237 11220769440071286048577)
              ·
                rfl

theorem cell22_885021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 8].length) (baseStart_885021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885021 prefixEnd_885021 := by exact prefixLift 885021
  have htrace : WordTrace (prefixWord ++ tailWord_885021) baseStart_885021 baseEnd_885021 := by
    simpa [prefixWord, tailWord_885021, baseEnd_885021] using wordTrace_append hprefix tailTrace_885021
  have hstable : (prefixWord ++ tailWord_885021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885021).length < 2 ^ (prefixWord ++ tailWord_885021).sum := by decide
  have hdescent : baseEnd_885021 < baseStart_885021 := by decide
  rcases family_descends (prefixWord ++ tailWord_885021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885036 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_885036 : Nat := 118140960795 + 885036 * 2 ^ 59
def prefixEnd_885036 : Nat := 4983230072969 + 3 ^ 40 * 885036 * 2
def baseEnd_885036 : Nat := 302965909688469684186533

theorem tailTrace_885036 : CollatzResearch.WordTrace tailWord_885036 prefixEnd_885036 302965909688469684186533 := by
  unfold tailWord_885036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16139957410836599480037481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21519943214448799306716641 16139957410836599480037481)
  ·
    refine ⟨12104968058127449610028111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16139957410836599480037481 12104968058127449610028111)
    ·
      refine ⟨18157452087191174415042167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12104968058127449610028111 18157452087191174415042167)
      ·
        refine ⟨27236178130786761622563251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18157452087191174415042167 27236178130786761622563251)
        ·
          refine ⟨40854267196180142433844877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27236178130786761622563251 40854267196180142433844877)
          ·
            refine ⟨15320350198567553412691829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40854267196180142433844877 15320350198567553412691829)
            ·
              refine ⟨1436282831115708132439859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15320350198567553412691829 1436282831115708132439859)
              ·
                refine ⟨2154424246673562198659789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436282831115708132439859 2154424246673562198659789)
                ·
                  refine ⟨807909092502585824497421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2154424246673562198659789 807909092502585824497421)
                  ·
                    refine ⟨302965909688469684186533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807909092502585824497421 302965909688469684186533)
                    ·
                      rfl

theorem cell22_885036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_885036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885036 prefixEnd_885036 := by exact prefixLift 885036
  have htrace : WordTrace (prefixWord ++ tailWord_885036) baseStart_885036 baseEnd_885036 := by
    simpa [prefixWord, tailWord_885036, baseEnd_885036] using wordTrace_append hprefix tailTrace_885036
  have hstable : (prefixWord ++ tailWord_885036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885036).length < 2 ^ (prefixWord ++ tailWord_885036).sum := by decide
  have hdescent : baseEnd_885036 < baseStart_885036 := by decide
  rcases family_descends (prefixWord ++ tailWord_885036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885038 : List Nat := [4, 1, 3, 3, 1, 1, 2, 7]
def baseStart_885038 : Nat := 118140960795 + 885038 * 2 ^ 59
def prefixEnd_885038 : Nat := 4983230072969 + 3 ^ 40 * 885038 * 2
def baseEnd_885038 : Nat := 33662954925482482848503

theorem tailTrace_885038 : CollatzResearch.WordTrace tailWord_885038 prefixEnd_885038 33662954925482482848503 := by
  unfold tailWord_885038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034998470958244162705971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21519991845110635534431845 4034998470958244162705971)
  ·
    refine ⟨6052497706437366244058957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4034998470958244162705971 6052497706437366244058957)
    ·
      refine ⟨2269686639914012341522109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6052497706437366244058957 2269686639914012341522109)
      ·
        refine ⟨851132489967754628070791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2269686639914012341522109 851132489967754628070791)
        ·
          refine ⟨1276698734951631942106187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851132489967754628070791 1276698734951631942106187)
          ·
            refine ⟨1915048102427447913159281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276698734951631942106187 1915048102427447913159281)
            ·
              refine ⟨1436286076820585934869461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915048102427447913159281 1436286076820585934869461)
              ·
                refine ⟨33662954925482482848503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1436286076820585934869461 33662954925482482848503)
                ·
                  rfl

theorem cell22_885038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_885038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885038 prefixEnd_885038 := by exact prefixLift 885038
  have htrace : WordTrace (prefixWord ++ tailWord_885038) baseStart_885038 baseEnd_885038 := by
    simpa [prefixWord, tailWord_885038, baseEnd_885038] using wordTrace_append hprefix tailTrace_885038
  have hstable : (prefixWord ++ tailWord_885038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885038).length < 2 ^ (prefixWord ++ tailWord_885038).sum := by decide
  have hdescent : baseEnd_885038 < baseStart_885038 := by decide
  rcases family_descends (prefixWord ++ tailWord_885038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885042 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_885042 : Nat := 118140960795 + 885042 * 2 ^ 59
def prefixEnd_885042 : Nat := 4983230072969 + 3 ^ 40 * 885042 * 2
def baseEnd_885042 : Nat := 302967963611087668536515

theorem tailTrace_885042 : CollatzResearch.WordTrace tailWord_885042 prefixEnd_885042 302967963611087668536515 := by
  unfold tailWord_885042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070033414912865496198345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21520089106434307989862253 8070033414912865496198345)
  ·
    refine ⟨6052525061184649122148759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8070033414912865496198345 6052525061184649122148759)
    ·
      refine ⟨9078787591776973683223139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052525061184649122148759 9078787591776973683223139)
      ·
        refine ⟨13618181387665460524834709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9078787591776973683223139 13618181387665460524834709)
        ·
          refine ⟨638352252546818462101627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13618181387665460524834709 638352252546818462101627)
          ·
            refine ⟨957528378820227693152441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638352252546818462101627 957528378820227693152441)
            ·
              refine ⟨718146284115170769864331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957528378820227693152441 718146284115170769864331)
              ·
                refine ⟨1077219426172756154796497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718146284115170769864331 1077219426172756154796497)
                ·
                  refine ⟨807914569629567116097373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077219426172756154796497 807914569629567116097373)
                  ·
                    refine ⟨302967963611087668536515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 807914569629567116097373 302967963611087668536515)
                    ·
                      rfl

theorem cell22_885042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_885042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885042 prefixEnd_885042 := by exact prefixLift 885042
  have htrace : WordTrace (prefixWord ++ tailWord_885042) baseStart_885042 baseEnd_885042 := by
    simpa [prefixWord, tailWord_885042, baseEnd_885042] using wordTrace_append hprefix tailTrace_885042
  have hstable : (prefixWord ++ tailWord_885042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885042).length < 2 ^ (prefixWord ++ tailWord_885042).sum := by decide
  have hdescent : baseEnd_885042 < baseStart_885042 := by decide
  rcases family_descends (prefixWord ++ tailWord_885042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885096 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_885096 : Nat := 118140960795 + 885096 * 2 ^ 59
def prefixEnd_885096 : Nat := 4983230072969 + 3 ^ 40 * 885096 * 2
def baseEnd_885096 : Nat := 302986448914649527686349

theorem tailTrace_885096 : CollatzResearch.WordTrace tailWord_885096 prefixEnd_885096 302986448914649527686349 := by
  unfold tailWord_885096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141051600727914603629571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21521402134303886138172761 16141051600727914603629571)
  ·
    refine ⟨24211577401091871905444357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16141051600727914603629571 24211577401091871905444357)
    ·
      refine ⟨4539670762704725982270817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24211577401091871905444357 4539670762704725982270817)
      ·
        refine ⟨3404753072028544486703113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4539670762704725982270817 3404753072028544486703113)
        ·
          refine ⟨2553564804021408365027335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404753072028544486703113 2553564804021408365027335)
          ·
            refine ⟨3830347206032112547541003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553564804021408365027335 3830347206032112547541003)
            ·
              refine ⟨5745520809048168821311505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830347206032112547541003 5745520809048168821311505)
              ·
                refine ⟨4309140606786126615983629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745520809048168821311505 4309140606786126615983629)
                ·
                  refine ⟨1615927727544797480993861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4309140606786126615983629 1615927727544797480993861)
                  ·
                    refine ⟨302986448914649527686349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615927727544797480993861 302986448914649527686349)
                    ·
                      rfl

theorem cell22_885096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_885096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885096 prefixEnd_885096 := by exact prefixLift 885096
  have htrace : WordTrace (prefixWord ++ tailWord_885096) baseStart_885096 baseEnd_885096 := by
    simpa [prefixWord, tailWord_885096, baseEnd_885096] using wordTrace_append hprefix tailTrace_885096
  have hstable : (prefixWord ++ tailWord_885096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885096).length < 2 ^ (prefixWord ++ tailWord_885096).sum := by decide
  have hdescent : baseEnd_885096 < baseStart_885096 := by decide
  rcases family_descends (prefixWord ++ tailWord_885096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885128 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_885128 : Nat := 118140960795 + 885128 * 2 ^ 59
def prefixEnd_885128 : Nat := 4983230072969 + 3 ^ 40 * 885128 * 2
def baseEnd_885128 : Nat := 100999134389537370295417

theorem tailTrace_885128 : CollatzResearch.WordTrace tailWord_885128 prefixEnd_885128 100999134389537370295417 := by
  unfold tailWord_885128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141635168669949336212019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21522180224893265781616025 16141635168669949336212019)
  ·
    refine ⟨24212452753004924004318029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16141635168669949336212019 24212452753004924004318029)
    ·
      refine ⟨9079669782376846501619261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24212452753004924004318029 9079669782376846501619261)
      ·
        refine ⟨3404876168391317438107223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9079669782376846501619261 3404876168391317438107223)
        ·
          refine ⟨5107314252586976157160835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404876168391317438107223 5107314252586976157160835)
          ·
            refine ⟨7660971378880464235741253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107314252586976157160835 7660971378880464235741253)
            ·
              refine ⟨1436432133540087044201485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7660971378880464235741253 1436432133540087044201485)
              ·
                refine ⟨538662050077532641575557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1436432133540087044201485 538662050077532641575557)
                ·
                  refine ⟨100999134389537370295417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538662050077532641575557 100999134389537370295417)
                  ·
                    rfl

theorem cell22_885128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_885128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885128 prefixEnd_885128 := by exact prefixLift 885128
  have htrace : WordTrace (prefixWord ++ tailWord_885128) baseStart_885128 baseEnd_885128 := by
    simpa [prefixWord, tailWord_885128, baseEnd_885128] using wordTrace_append hprefix tailTrace_885128
  have hstable : (prefixWord ++ tailWord_885128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885128).length < 2 ^ (prefixWord ++ tailWord_885128).sum := by decide
  have hdescent : baseEnd_885128 < baseStart_885128 := by decide
  rcases family_descends (prefixWord ++ tailWord_885128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885130 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_885130 : Nat := 118140960795 + 885130 * 2 ^ 59
def prefixEnd_885130 : Nat := 4983230072969 + 3 ^ 40 * 885130 * 2
def baseEnd_885130 : Nat := 302998087809484772336245

theorem tailTrace_885130 : CollatzResearch.WordTrace tailWord_885130 prefixEnd_885130 302998087809484772336245 := by
  unfold tailWord_885130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070835820833163253499211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21522228855555102009331229 8070835820833163253499211)
  ·
    refine ⟨12106253731249744880248817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8070835820833163253499211 12106253731249744880248817)
    ·
      refine ⟨9079690298437308660186613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12106253731249744880248817 9079690298437308660186613)
      ·
        refine ⟨851220965478497686892495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9079690298437308660186613 851220965478497686892495)
        ·
          refine ⟨1276831448217746530338743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851220965478497686892495 1276831448217746530338743)
          ·
            refine ⟨1915247172326619795508115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276831448217746530338743 1915247172326619795508115)
            ·
              refine ⟨2872870758489929693262173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915247172326619795508115 2872870758489929693262173)
              ·
                refine ⟨1077326534433723634973315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2872870758489929693262173 1077326534433723634973315)
                ·
                  refine ⟨1615989801650585452459973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077326534433723634973315 1615989801650585452459973)
                  ·
                    refine ⟨302998087809484772336245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1615989801650585452459973 302998087809484772336245)
                    ·
                      rfl

theorem cell22_885130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_885130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885130 prefixEnd_885130 := by exact prefixLift 885130
  have htrace : WordTrace (prefixWord ++ tailWord_885130) baseStart_885130 baseEnd_885130 := by
    simpa [prefixWord, tailWord_885130, baseEnd_885130] using wordTrace_append hprefix tailTrace_885130
  have hstable : (prefixWord ++ tailWord_885130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885130).length < 2 ^ (prefixWord ++ tailWord_885130).sum := by decide
  have hdescent : baseEnd_885130 < baseStart_885130 := by decide
  rcases family_descends (prefixWord ++ tailWord_885130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885143 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 2, 3]
def baseStart_885143 : Nat := 118140960795 + 885143 * 2 ^ 59
def prefixEnd_885143 : Nat := 4983230072969 + 3 ^ 40 * 885143 * 2
def baseEnd_885143 : Nat := 303002537975157071761205

theorem tailTrace_885143 : CollatzResearch.WordTrace tailWord_885143 prefixEnd_885143 303002537975157071761205 := by
  unfold tailWord_885143
  simp only [CollatzResearch.WordTrace]
  refine ⟨32283817432285556234220083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21522544954857037489480055 32283817432285556234220083)
  ·
    refine ⟨48425726148428334351330125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32283817432285556234220083 48425726148428334351330125)
    ·
      refine ⟨18159647305660625381748797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48425726148428334351330125 18159647305660625381748797)
      ·
        refine ⟨6809867739622734518155799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18159647305660625381748797 6809867739622734518155799)
        ·
          refine ⟨10214801609434101777233699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809867739622734518155799 10214801609434101777233699)
          ·
            refine ⟨15322202414151152665850549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214801609434101777233699 15322202414151152665850549)
            ·
              refine ⟨1436456476326670562423489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15322202414151152665850549 1436456476326670562423489)
              ·
                refine ⟨1077342357245002921817617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436456476326670562423489 1077342357245002921817617)
                ·
                  refine ⟨808006767933752191363213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077342357245002921817617 808006767933752191363213)
                  ·
                    refine ⟨303002537975157071761205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808006767933752191363213 303002537975157071761205)
                    ·
                      rfl

theorem cell22_885143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_885143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885143 prefixEnd_885143 := by exact prefixLift 885143
  have htrace : WordTrace (prefixWord ++ tailWord_885143) baseStart_885143 baseEnd_885143 := by
    simpa [prefixWord, tailWord_885143, baseEnd_885143] using wordTrace_append hprefix tailTrace_885143
  have hstable : (prefixWord ++ tailWord_885143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885143).length < 2 ^ (prefixWord ++ tailWord_885143).sum := by decide
  have hdescent : baseEnd_885143 < baseStart_885143 := by decide
  rcases family_descends (prefixWord ++ tailWord_885143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885160 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_885160 : Nat := 118140960795 + 885160 * 2 ^ 59
def prefixEnd_885160 : Nat := 4983230072969 + 3 ^ 40 * 885160 * 2
def baseEnd_885160 : Nat := 303008357422574694086153

theorem tailTrace_885160 : CollatzResearch.WordTrace tailWord_885160 prefixEnd_885160 303008357422574694086153 := by
  unfold tailWord_885160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142218736611984068794467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21522958315482645425059289 16142218736611984068794467)
  ·
    refine ⟨24213328104917976103191701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16142218736611984068794467 24213328104917976103191701)
    ·
      refine ⟨1134999754918030129837111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24213328104917976103191701 1134999754918030129837111)
      ·
        refine ⟨1702499632377045194755667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134999754918030129837111 1702499632377045194755667)
        ·
          refine ⟨2553749448565567792133501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702499632377045194755667 2553749448565567792133501)
          ·
            refine ⟨957656043212087922050063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2553749448565567792133501 957656043212087922050063)
            ·
              refine ⟨1436484064818131883075095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957656043212087922050063 1436484064818131883075095)
              ·
                refine ⟨2154726097227197824612643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436484064818131883075095 2154726097227197824612643)
                ·
                  refine ⟨3232089145840796736918965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154726097227197824612643 3232089145840796736918965)
                  ·
                    refine ⟨303008357422574694086153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3232089145840796736918965 303008357422574694086153)
                    ·
                      rfl

theorem cell22_885160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_885160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885160 prefixEnd_885160 := by exact prefixLift 885160
  have htrace : WordTrace (prefixWord ++ tailWord_885160) baseStart_885160 baseEnd_885160 := by
    simpa [prefixWord, tailWord_885160, baseEnd_885160] using wordTrace_append hprefix tailTrace_885160
  have hstable : (prefixWord ++ tailWord_885160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885160).length < 2 ^ (prefixWord ++ tailWord_885160).sum := by decide
  have hdescent : baseEnd_885160 < baseStart_885160 := by decide
  rcases family_descends (prefixWord ++ tailWord_885160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885205 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_885205 : Nat := 118140960795 + 885205 * 2 ^ 59
def prefixEnd_885205 : Nat := 4983230072969 + 3 ^ 40 * 885205 * 2
def baseEnd_885205 : Nat := 303023761842209576711015

theorem tailTrace_885205 : CollatzResearch.WordTrace tailWord_885205 prefixEnd_885205 303023761842209576711015 := by
  unfold tailWord_885205
  simp only [CollatzResearch.WordTrace]
  refine ⟨32286078758060940822977069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21524052505373960548651379 32286078758060940822977069)
  ·
    refine ⟨12107279534272852808616401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32286078758060940822977069 12107279534272852808616401)
    ·
      refine ⟨9080459650704639606462301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12107279534272852808616401 9080459650704639606462301)
      ·
        refine ⟨3405172369014239852423363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9080459650704639606462301 3405172369014239852423363)
        ·
          refine ⟨5107758553521359778635045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405172369014239852423363 5107758553521359778635045)
          ·
            refine ⟨957704728785254958494071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5107758553521359778635045 957704728785254958494071)
            ·
              refine ⟨1436557093177882437741107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957704728785254958494071 1436557093177882437741107)
              ·
                refine ⟨2154835639766823656611661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1436557093177882437741107 2154835639766823656611661)
                ·
                  refine ⟨808063364912558871229373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2154835639766823656611661 808063364912558871229373)
                  ·
                    refine ⟨303023761842209576711015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808063364912558871229373 303023761842209576711015)
                    ·
                      rfl

theorem cell22_885205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_885205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885205 prefixEnd_885205 := by exact prefixLift 885205
  have htrace : WordTrace (prefixWord ++ tailWord_885205) baseStart_885205 baseEnd_885205 := by
    simpa [prefixWord, tailWord_885205, baseEnd_885205] using wordTrace_append hprefix tailTrace_885205
  have hstable : (prefixWord ++ tailWord_885205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885205).length < 2 ^ (prefixWord ++ tailWord_885205).sum := by decide
  have hdescent : baseEnd_885205 < baseStart_885205 := by decide
  rcases family_descends (prefixWord ++ tailWord_885205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885323 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 3, 3]
def baseStart_885323 : Nat := 118140960795 + 885323 * 2 ^ 59
def prefixEnd_885323 : Nat := 4983230072969 + 3 ^ 40 * 885323 * 2
def baseEnd_885323 : Nat := 303064155653696602260653

theorem tailTrace_885323 : CollatzResearch.WordTrace tailWord_885323 prefixEnd_885323 303064155653696602260653 := by
  unfold tailWord_885323
  simp only [CollatzResearch.WordTrace]
  refine ⟨32290382571633446975772623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21526921714422297983848415 32290382571633446975772623)
  ·
    refine ⟨48435573857450170463658935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32290382571633446975772623 48435573857450170463658935)
    ·
      refine ⟨72653360786175255695488403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48435573857450170463658935 72653360786175255695488403)
      ·
        refine ⟨108980041179262883543232605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72653360786175255695488403 108980041179262883543232605)
        ·
          refine ⟨40867515442223581328712227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108980041179262883543232605 40867515442223581328712227)
          ·
            refine ⟨61301273163335371993068341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40867515442223581328712227 61301273163335371993068341)
            ·
              refine ⟨5746994359062691124350157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61301273163335371993068341 5746994359062691124350157)
              ·
                refine ⟨2155122884648509171631309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5746994359062691124350157 2155122884648509171631309)
                ·
                  refine ⟨808171081743190939361741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2155122884648509171631309 808171081743190939361741)
                  ·
                    refine ⟨303064155653696602260653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808171081743190939361741 303064155653696602260653)
                    ·
                      rfl

theorem cell22_885323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3].length) (baseStart_885323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885323 prefixEnd_885323 := by exact prefixLift 885323
  have htrace : WordTrace (prefixWord ++ tailWord_885323) baseStart_885323 baseEnd_885323 := by
    simpa [prefixWord, tailWord_885323, baseEnd_885323] using wordTrace_append hprefix tailTrace_885323
  have hstable : (prefixWord ++ tailWord_885323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885323).length < 2 ^ (prefixWord ++ tailWord_885323).sum := by decide
  have hdescent : baseEnd_885323 < baseStart_885323 := by decide
  rcases family_descends (prefixWord ++ tailWord_885323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885383 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_885383 : Nat := 118140960795 + 885383 * 2 ^ 59
def prefixEnd_885383 : Nat := 4983230072969 + 3 ^ 40 * 885383 * 2
def baseEnd_885383 : Nat := 303084694879876445760469

theorem tailTrace_885383 : CollatzResearch.WordTrace tailWord_885383 prefixEnd_885383 303084694879876445760469 := by
  unfold tailWord_885383
  simp only [CollatzResearch.WordTrace]
  refine ⟨32292570951416077222956803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21528380634277384815304535 32292570951416077222956803)
  ·
    refine ⟨48438856427124115834435205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32292570951416077222956803 48438856427124115834435205)
    ·
      refine ⟨9082285580085771718956601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48438856427124115834435205 9082285580085771718956601)
      ·
        refine ⟨6811714185064328789217451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9082285580085771718956601 6811714185064328789217451)
        ·
          refine ⟨10217571277596493183826177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811714185064328789217451 10217571277596493183826177)
          ·
            refine ⟨7663178458197369887869633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10217571277596493183826177 7663178458197369887869633)
            ·
              refine ⟨5747383843648027415902225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7663178458197369887869633 5747383843648027415902225)
              ·
                refine ⟨4310537882736020561926669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5747383843648027415902225 4310537882736020561926669)
                ·
                  refine ⟨1616451706026007710722501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4310537882736020561926669 1616451706026007710722501)
                  ·
                    refine ⟨303084694879876445760469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616451706026007710722501 303084694879876445760469)
                    ·
                      rfl

theorem cell22_885383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_885383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885383 prefixEnd_885383 := by exact prefixLift 885383
  have htrace : WordTrace (prefixWord ++ tailWord_885383) baseStart_885383 baseEnd_885383 := by
    simpa [prefixWord, tailWord_885383, baseEnd_885383] using wordTrace_append hprefix tailTrace_885383
  have hstable : (prefixWord ++ tailWord_885383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885383).length < 2 ^ (prefixWord ++ tailWord_885383).sum := by decide
  have hdescent : baseEnd_885383 < baseStart_885383 := by decide
  rcases family_descends (prefixWord ++ tailWord_885383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885488 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_885488 : Nat := 118140960795 + 885488 * 2 ^ 59
def prefixEnd_885488 : Nat := 4983230072969 + 3 ^ 40 * 885488 * 2
def baseEnd_885488 : Nat := 101040212841897057295049

theorem tailTrace_885488 : CollatzResearch.WordTrace tailWord_885488 prefixEnd_885488 101040212841897057295049 := by
  unfold tailWord_885488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16148200308017840077764559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21530933744023786770352745 16148200308017840077764559)
  ·
    refine ⟨24222300462026760116646839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16148200308017840077764559 24222300462026760116646839)
    ·
      refine ⟨36333450693040140174970259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24222300462026760116646839 36333450693040140174970259)
      ·
        refine ⟨54500176039560210262455389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36333450693040140174970259 54500176039560210262455389)
        ·
          refine ⟨20437566014835078848420771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54500176039560210262455389 20437566014835078848420771)
          ·
            refine ⟨30656349022252618272631157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20437566014835078848420771 30656349022252618272631157)
            ·
              refine ⟨2874032720836182963059171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30656349022252618272631157 2874032720836182963059171)
              ·
                refine ⟨4311049081254274444588757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874032720836182963059171 4311049081254274444588757)
                ·
                  refine ⟨101040212841897057295049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4311049081254274444588757 101040212841897057295049)
                  ·
                    rfl

theorem cell22_885488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_885488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885488 prefixEnd_885488 := by exact prefixLift 885488
  have htrace : WordTrace (prefixWord ++ tailWord_885488) baseStart_885488 baseEnd_885488 := by
    simpa [prefixWord, tailWord_885488, baseEnd_885488] using wordTrace_append hprefix tailTrace_885488
  have hstable : (prefixWord ++ tailWord_885488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885488).length < 2 ^ (prefixWord ++ tailWord_885488).sum := by decide
  have hdescent : baseEnd_885488 < baseStart_885488 := by decide
  rcases family_descends (prefixWord ++ tailWord_885488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885556 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_885556 : Nat := 118140960795 + 885556 * 2 ^ 59
def prefixEnd_885556 : Nat := 4983230072969 + 3 ^ 40 * 885556 * 2
def baseEnd_885556 : Nat := 101047972105120553728313

theorem tailTrace_885556 : CollatzResearch.WordTrace tailWord_885556 prefixEnd_885556 101047972105120553728313 := by
  unfold tailWord_885556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16149440389894663884502261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21532587186526218512669681 16149440389894663884502261)
  ·
    refine ⟨1514010036552624739172087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16149440389894663884502261 1514010036552624739172087)
    ·
      refine ⟨2271015054828937108758131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514010036552624739172087 2271015054828937108758131)
      ·
        refine ⟨3406522582243405663137197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271015054828937108758131 3406522582243405663137197)
        ·
          refine ⟨1277445968341277123676449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3406522582243405663137197 1277445968341277123676449)
          ·
            refine ⟨958084476255957842757337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1277445968341277123676449 958084476255957842757337)
            ·
              refine ⟨718563357191968382068003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958084476255957842757337 718563357191968382068003)
              ·
                refine ⟨1077845035787952573102005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718563357191968382068003 1077845035787952573102005)
                ·
                  refine ⟨101047972105120553728313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1077845035787952573102005 101047972105120553728313)
                  ·
                    rfl

theorem cell22_885556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_885556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885556 prefixEnd_885556 := by exact prefixLift 885556
  have htrace : WordTrace (prefixWord ++ tailWord_885556) baseStart_885556 baseEnd_885556 := by
    simpa [prefixWord, tailWord_885556, baseEnd_885556] using wordTrace_append hprefix tailTrace_885556
  have hstable : (prefixWord ++ tailWord_885556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885556).length < 2 ^ (prefixWord ++ tailWord_885556).sum := by decide
  have hdescent : baseEnd_885556 < baseStart_885556 := by decide
  rcases family_descends (prefixWord ++ tailWord_885556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885569 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_885569 : Nat := 118140960795 + 885569 * 2 ^ 59
def prefixEnd_885569 : Nat := 4983230072969 + 3 ^ 40 * 885569 * 2
def baseEnd_885569 : Nat := 303148366481033960609899

theorem tailTrace_885569 : CollatzResearch.WordTrace tailWord_885569 prefixEnd_885569 303148366481033960609899 := by
  unfold tailWord_885569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299354928742230989227761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21532903285828153992818507 32299354928742230989227761)
  ·
    refine ⟨24224516196556673241920821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32299354928742230989227761 24224516196556673241920821)
    ·
      refine ⟨2271048393427188116430077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24224516196556673241920821 2271048393427188116430077)
      ·
        refine ⟨851643147535195543661279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2271048393427188116430077 851643147535195543661279)
        ·
          refine ⟨1277464721302793315491919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851643147535195543661279 1277464721302793315491919)
          ·
            refine ⟨1916197081954189973237879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277464721302793315491919 1916197081954189973237879)
            ·
              refine ⟨2874295622931284959856819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916197081954189973237879 2874295622931284959856819)
              ·
                refine ⟨4311443434396927439785229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2874295622931284959856819 4311443434396927439785229)
                ·
                  refine ⟨1616791287898847789919461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4311443434396927439785229 1616791287898847789919461)
                  ·
                    refine ⟨303148366481033960609899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1616791287898847789919461 303148366481033960609899)
                    ·
                      rfl

theorem cell22_885569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_885569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885569 prefixEnd_885569 := by exact prefixLift 885569
  have htrace : WordTrace (prefixWord ++ tailWord_885569) baseStart_885569 baseEnd_885569 := by
    simpa [prefixWord, tailWord_885569, baseEnd_885569] using wordTrace_append hprefix tailTrace_885569
  have hstable : (prefixWord ++ tailWord_885569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885569).length < 2 ^ (prefixWord ++ tailWord_885569).sum := by decide
  have hdescent : baseEnd_885569 < baseStart_885569 := by decide
  rcases family_descends (prefixWord ++ tailWord_885569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885644 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_885644 : Nat := 118140960795 + 885644 * 2 ^ 59
def prefixEnd_885644 : Nat := 4983230072969 + 3 ^ 40 * 885644 * 2
def baseEnd_885644 : Nat := 303174040513758764984669

theorem tailTrace_885644 : CollatzResearch.WordTrace tailWord_885644 prefixEnd_885644 303174040513758764984669 := by
  unfold tailWord_885644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151045201735259399103993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21534726935647012532138657 16151045201735259399103993)
  ·
    refine ⟨12113283901301444549327995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16151045201735259399103993 12113283901301444549327995)
    ·
      refine ⟨18169925851952166823991993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12113283901301444549327995 18169925851952166823991993)
      ·
        refine ⟨13627444388964125117993995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18169925851952166823991993 13627444388964125117993995)
        ·
          refine ⟨20441166583446187676990993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13627444388964125117993995 20441166583446187676990993)
          ·
            refine ⟨15330874937584640757743245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20441166583446187676990993 15330874937584640757743245)
            ·
              refine ⟨5749078101594240284153717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15330874937584640757743245 5749078101594240284153717)
              ·
                refine ⟨538976072024460026639411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5749078101594240284153717 538976072024460026639411)
                ·
                  refine ⟨808464108036690039959117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538976072024460026639411 808464108036690039959117)
                  ·
                    refine ⟨303174040513758764984669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808464108036690039959117 303174040513758764984669)
                    ·
                      rfl

theorem cell22_885644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_885644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885644 prefixEnd_885644 := by exact prefixLift 885644
  have htrace : WordTrace (prefixWord ++ tailWord_885644) baseStart_885644 baseEnd_885644 := by
    simpa [prefixWord, tailWord_885644, baseEnd_885644] using wordTrace_append hprefix tailTrace_885644
  have hstable : (prefixWord ++ tailWord_885644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885644).length < 2 ^ (prefixWord ++ tailWord_885644).sum := by decide
  have hdescent : baseEnd_885644 < baseStart_885644 := by decide
  rcases family_descends (prefixWord ++ tailWord_885644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885655 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_885655 : Nat := 118140960795 + 885655 * 2 ^ 59
def prefixEnd_885655 : Nat := 4983230072969 + 3 ^ 40 * 885655 * 2
def baseEnd_885655 : Nat := 303177806038558402959635

theorem tailTrace_885655 : CollatzResearch.WordTrace tailWord_885655 prefixEnd_885655 303177806038558402959635 := by
  unfold tailWord_885655
  simp only [CollatzResearch.WordTrace]
  refine ⟨32302491606430667676858419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21534994404287111784572279 32302491606430667676858419)
  ·
    refine ⟨48453737409646001515287629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32302491606430667676858419 48453737409646001515287629)
    ·
      refine ⟨18170151528617250568232861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48453737409646001515287629 18170151528617250568232861)
      ·
        refine ⟨6813806823231468963087323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18170151528617250568232861 6813806823231468963087323)
        ·
          refine ⟨10220710234847203444630985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813806823231468963087323 10220710234847203444630985)
          ·
            refine ⟨7665532676135402583473239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10220710234847203444630985 7665532676135402583473239)
            ·
              refine ⟨11498299014203103875209859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7665532676135402583473239 11498299014203103875209859)
              ·
                refine ⟨17247448521304655812814789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11498299014203103875209859 17247448521304655812814789)
                ·
                  refine ⟨3233896597744622964902773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17247448521304655812814789 3233896597744622964902773)
                  ·
                    refine ⟨303177806038558402959635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3233896597744622964902773 303177806038558402959635)
                    ·
                      rfl

theorem cell22_885655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_885655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885655 prefixEnd_885655 := by exact prefixLift 885655
  have htrace : WordTrace (prefixWord ++ tailWord_885655) baseStart_885655 baseEnd_885655 := by
    simpa [prefixWord, tailWord_885655, baseEnd_885655] using wordTrace_append hprefix tailTrace_885655
  have hstable : (prefixWord ++ tailWord_885655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885655).length < 2 ^ (prefixWord ++ tailWord_885655).sum := by decide
  have hdescent : baseEnd_885655 < baseStart_885655 := by decide
  rcases family_descends (prefixWord ++ tailWord_885655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885687 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 1, 4]
def baseStart_885687 : Nat := 118140960795 + 885687 * 2 ^ 59
def prefixEnd_885687 : Nat := 4983230072969 + 3 ^ 40 * 885687 * 2
def baseEnd_885687 : Nat := 303188760292520986159537

theorem tailTrace_885687 : CollatzResearch.WordTrace tailWord_885687 prefixEnd_885687 303188760292520986159537 := by
  unfold tailWord_885687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32303658742314737142023315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21535772494876491428015543 32303658742314737142023315)
  ·
    refine ⟨48455488113472105713034973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32303658742314737142023315 48455488113472105713034973)
    ·
      refine ⟨18170808042552039642388115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48455488113472105713034973 18170808042552039642388115)
      ·
        refine ⟨27256212063828059463582173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18170808042552039642388115 27256212063828059463582173)
        ·
          refine ⟨10221079523935522298843315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27256212063828059463582173 10221079523935522298843315)
          ·
            refine ⟨15331619285903283448264973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10221079523935522298843315 15331619285903283448264973)
            ·
              refine ⟨5749357232213731293099365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15331619285903283448264973 5749357232213731293099365)
              ·
                refine ⟨1078004481040074617456131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5749357232213731293099365 1078004481040074617456131)
                ·
                  refine ⟨1617006721560111926184197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078004481040074617456131 1617006721560111926184197)
                  ·
                    refine ⟨303188760292520986159537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617006721560111926184197 303188760292520986159537)
                    ·
                      rfl

theorem cell22_885687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_885687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885687 prefixEnd_885687 := by exact prefixLift 885687
  have htrace : WordTrace (prefixWord ++ tailWord_885687) baseStart_885687 baseEnd_885687 := by
    simpa [prefixWord, tailWord_885687, baseEnd_885687] using wordTrace_append hprefix tailTrace_885687
  have hstable : (prefixWord ++ tailWord_885687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885687).length < 2 ^ (prefixWord ++ tailWord_885687).sum := by decide
  have hdescent : baseEnd_885687 < baseStart_885687 := by decide
  rcases family_descends (prefixWord ++ tailWord_885687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885796 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_885796 : Nat := 118140960795 + 885796 * 2 ^ 59
def prefixEnd_885796 : Nat := 4983230072969 + 3 ^ 40 * 885796 * 2
def baseEnd_885796 : Nat := 303226073220081035184203

theorem tailTrace_885796 : CollatzResearch.WordTrace tailWord_885796 prefixEnd_885796 303226073220081035184203 := by
  unfold tailWord_885796
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153817149459924378870621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21538422865946565838494161 16153817149459924378870621)
  ·
    refine ⟨6057681431047471642076483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16153817149459924378870621 6057681431047471642076483)
    ·
      refine ⟨9086522146571207463114725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6057681431047471642076483 9086522146571207463114725)
      ·
        refine ⟨1703722902482101399334011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9086522146571207463114725 1703722902482101399334011)
        ·
          refine ⟨2555584353723152099001017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703722902482101399334011 2555584353723152099001017)
          ·
            refine ⟨1916688265292364074250763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555584353723152099001017 1916688265292364074250763)
            ·
              refine ⟨2875032397938546111376145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916688265292364074250763 2875032397938546111376145)
              ·
                refine ⟨2156274298453909583532109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875032397938546111376145 2156274298453909583532109)
                ·
                  refine ⟨808602861920216093824541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2156274298453909583532109 808602861920216093824541)
                  ·
                    refine ⟨303226073220081035184203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808602861920216093824541 303226073220081035184203)
                    ·
                      rfl

theorem cell22_885796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_885796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885796 prefixEnd_885796 := by exact prefixLift 885796
  have htrace : WordTrace (prefixWord ++ tailWord_885796) baseStart_885796 baseEnd_885796 := by
    simpa [prefixWord, tailWord_885796, baseEnd_885796] using wordTrace_append hprefix tailTrace_885796
  have hstable : (prefixWord ++ tailWord_885796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885796).length < 2 ^ (prefixWord ++ tailWord_885796).sum := by decide
  have hdescent : baseEnd_885796 < baseStart_885796 := by decide
  rcases family_descends (prefixWord ++ tailWord_885796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885830 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_885830 : Nat := 118140960795 + 885830 * 2 ^ 59
def prefixEnd_885830 : Nat := 4983230072969 + 3 ^ 40 * 885830 * 2
def baseEnd_885830 : Nat := 303237712114916279834099

theorem tailTrace_885830 : CollatzResearch.WordTrace tailWord_885830 prefixEnd_885830 303237712114916279834099 := by
  unfold tailWord_885830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009652324399896017639967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21539249587197781709652629 1009652324399896017639967)
  ·
    refine ⟨1514478486599844026459951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1009652324399896017639967 1514478486599844026459951)
    ·
      refine ⟨2271717729899766039689927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514478486599844026459951 2271717729899766039689927)
      ·
        refine ⟨3407576594849649059534891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271717729899766039689927 3407576594849649059534891)
        ·
          refine ⟨5111364892274473589302337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407576594849649059534891 5111364892274473589302337)
          ·
            refine ⟨3833523669205855191976753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5111364892274473589302337 3833523669205855191976753)
            ·
              refine ⟨2875142751904391393982565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3833523669205855191976753 2875142751904391393982565)
              ·
                refine ⟨539089265982073386371731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2875142751904391393982565 539089265982073386371731)
                ·
                  refine ⟨808633898973110079557597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539089265982073386371731 808633898973110079557597)
                  ·
                    refine ⟨303237712114916279834099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808633898973110079557597 303237712114916279834099)
                    ·
                      rfl

theorem cell22_885830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_885830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885830 prefixEnd_885830 := by exact prefixLift 885830
  have htrace : WordTrace (prefixWord ++ tailWord_885830) baseStart_885830 baseEnd_885830 := by
    simpa [prefixWord, tailWord_885830, baseEnd_885830] using wordTrace_append hprefix tailTrace_885830
  have hstable : (prefixWord ++ tailWord_885830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885830).length < 2 ^ (prefixWord ++ tailWord_885830).sum := by decide
  have hdescent : baseEnd_885830 < baseStart_885830 := by decide
  rcases family_descends (prefixWord ++ tailWord_885830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885867 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_885867 : Nat := 118140960795 + 885867 * 2 ^ 59
def prefixEnd_885867 : Nat := 4983230072969 + 3 ^ 40 * 885867 * 2
def baseEnd_885867 : Nat := 303250377971060516658985

theorem tailTrace_885867 : CollatzResearch.WordTrace tailWord_885867 prefixEnd_885867 303250377971060516658985 := by
  unfold tailWord_885867
  simp only [CollatzResearch.WordTrace]
  refine ⟨32310223881662627883575855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21540149254441751922383903 32310223881662627883575855)
  ·
    refine ⟨48465335822493941825363783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32310223881662627883575855 48465335822493941825363783)
    ·
      refine ⟨72698003733740912738045675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48465335822493941825363783 72698003733740912738045675)
      ·
        refine ⟨109047005600611369107068513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72698003733740912738045675 109047005600611369107068513)
        ·
          refine ⟨81785254200458526830301385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109047005600611369107068513 81785254200458526830301385)
          ·
            refine ⟨61338940650343895122726039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81785254200458526830301385 61338940650343895122726039)
            ·
              refine ⟨92008410975515842684089059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61338940650343895122726039 92008410975515842684089059)
              ·
                refine ⟨138012616463273764026133589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92008410975515842684089059 138012616463273764026133589)
                ·
                  refine ⟨1617335349178989422181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 138012616463273764026133589 1617335349178989422181253)
                  ·
                    refine ⟨303250377971060516658985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617335349178989422181253 303250377971060516658985)
                    ·
                      rfl

theorem cell22_885867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_885867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885867 prefixEnd_885867 := by exact prefixLift 885867
  have htrace : WordTrace (prefixWord ++ tailWord_885867) baseStart_885867 baseEnd_885867 := by
    simpa [prefixWord, tailWord_885867, baseEnd_885867] using wordTrace_append hprefix tailTrace_885867
  have hstable : (prefixWord ++ tailWord_885867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885867).length < 2 ^ (prefixWord ++ tailWord_885867).sum := by decide
  have hdescent : baseEnd_885867 < baseStart_885867 := by decide
  rcases family_descends (prefixWord ++ tailWord_885867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885884 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_885884 : Nat := 118140960795 + 885884 * 2 ^ 59
def prefixEnd_885884 : Nat := 4983230072969 + 3 ^ 40 * 885884 * 2
def baseEnd_885884 : Nat := 303256197418478138983933

theorem tailTrace_885884 : CollatzResearch.WordTrace tailWord_885884 prefixEnd_885884 303256197418478138983933 := by
  unfold tailWord_885884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16155421961300519893472353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21540562615067359857963137 16155421961300519893472353)
  ·
    refine ⟨12116566470975389920104265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16155421961300519893472353 12116566470975389920104265)
    ·
      refine ⟨9087424853231542440078199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12116566470975389920104265 9087424853231542440078199)
      ·
        refine ⟨13631137279847313660117299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087424853231542440078199 13631137279847313660117299)
        ·
          refine ⟨20446705919770970490175949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13631137279847313660117299 20446705919770970490175949)
          ·
            refine ⟨7667514719914113933815981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20446705919770970490175949 7667514719914113933815981)
            ·
              refine ⟨2875318019967792725180993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7667514719914113933815981 2875318019967792725180993)
              ·
                refine ⟨2156488514975844543885745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875318019967792725180993 2156488514975844543885745)
                ·
                  refine ⟨1617366386231883407914309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156488514975844543885745 1617366386231883407914309)
                  ·
                    refine ⟨303256197418478138983933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617366386231883407914309 303256197418478138983933)
                    ·
                      rfl

theorem cell22_885884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_885884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885884 prefixEnd_885884 := by exact prefixLift 885884
  have htrace : WordTrace (prefixWord ++ tailWord_885884) baseStart_885884 baseEnd_885884 := by
    simpa [prefixWord, tailWord_885884, baseEnd_885884] using wordTrace_append hprefix tailTrace_885884
  have hstable : (prefixWord ++ tailWord_885884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885884).length < 2 ^ (prefixWord ++ tailWord_885884).sum := by decide
  have hdescent : baseEnd_885884 < baseStart_885884 := by decide
  rcases family_descends (prefixWord ++ tailWord_885884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885918 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_885918 : Nat := 118140960795 + 885918 * 2 ^ 59
def prefixEnd_885918 : Nat := 4983230072969 + 3 ^ 40 * 885918 * 2
def baseEnd_885918 : Nat := 303267836313313383633829

theorem tailTrace_885918 : CollatzResearch.WordTrace tailWord_885918 prefixEnd_885918 303267836313313383633829 := by
  unfold tailWord_885918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039010500559732949210301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21541389336318575729121605 4039010500559732949210301)
  ·
    refine ⟨1514628937709899855953863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4039010500559732949210301 1514628937709899855953863)
    ·
      refine ⟨2271943406564849783930795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514628937709899855953863 2271943406564849783930795)
      ·
        refine ⟨3407915109847274675896193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271943406564849783930795 3407915109847274675896193)
        ·
          refine ⟨2555936332385456006922145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3407915109847274675896193 2555936332385456006922145)
          ·
            refine ⟨1916952249289092005191609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2555936332385456006922145 1916952249289092005191609)
            ·
              refine ⟨1437714186966819003893707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916952249289092005191609 1437714186966819003893707)
              ·
                refine ⟨2156571280450228505840561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437714186966819003893707 2156571280450228505840561)
                ·
                  refine ⟨1617428460337671379380421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2156571280450228505840561 1617428460337671379380421)
                  ·
                    refine ⟨303267836313313383633829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1617428460337671379380421 303267836313313383633829)
                    ·
                      rfl

theorem cell22_885918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_885918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_885918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_885918 prefixEnd_885918 := by exact prefixLift 885918
  have htrace : WordTrace (prefixWord ++ tailWord_885918) baseStart_885918 baseEnd_885918 := by
    simpa [prefixWord, tailWord_885918, baseEnd_885918] using wordTrace_append hprefix tailTrace_885918
  have hstable : (prefixWord ++ tailWord_885918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885918).length < 2 ^ (prefixWord ++ tailWord_885918).sum := by decide
  have hdescent : baseEnd_885918 < baseStart_885918 := by decide
  rcases family_descends (prefixWord ++ tailWord_885918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886019 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_886019 : Nat := 118140960795 + 886019 * 2 ^ 59
def prefixEnd_886019 : Nat := 4983230072969 + 3 ^ 40 * 886019 * 2
def baseEnd_886019 : Nat := 303302410677382786858519

theorem tailTrace_886019 : CollatzResearch.WordTrace tailWord_886019 prefixEnd_886019 303302410677382786858519 := by
  unfold tailWord_886019
  simp only [CollatzResearch.WordTrace]
  refine ⟨32315767777111957843109111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21543845184741305228739407 32315767777111957843109111)
  ·
    refine ⟨48473651665667936764663667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32315767777111957843109111 48473651665667936764663667)
    ·
      refine ⟨72710477498501905146995501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48473651665667936764663667 72710477498501905146995501)
      ·
        refine ⟨27266429061938214430123313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72710477498501905146995501 27266429061938214430123313)
        ·
          refine ⟨20449821796453660822592485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27266429061938214430123313 20449821796453660822592485)
          ·
            refine ⟨3834341586835061404236091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20449821796453660822592485 3834341586835061404236091)
            ·
              refine ⟨5751512380252592106354137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3834341586835061404236091 5751512380252592106354137)
              ·
                refine ⟨4313634285189444079765603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5751512380252592106354137 4313634285189444079765603)
                ·
                  refine ⟨6470451427784166119648405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313634285189444079765603 6470451427784166119648405)
                  ·
                    refine ⟨303302410677382786858519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6470451427784166119648405 303302410677382786858519)
                    ·
                      rfl

theorem cell22_886019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_886019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886019 prefixEnd_886019 := by exact prefixLift 886019
  have htrace : WordTrace (prefixWord ++ tailWord_886019) baseStart_886019 baseEnd_886019 := by
    simpa [prefixWord, tailWord_886019, baseEnd_886019] using wordTrace_append hprefix tailTrace_886019
  have hstable : (prefixWord ++ tailWord_886019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886019).length < 2 ^ (prefixWord ++ tailWord_886019).sum := by decide
  have hdescent : baseEnd_886019 < baseStart_886019 := by decide
  rcases family_descends (prefixWord ++ tailWord_886019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886064 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_886064 : Nat := 118140960795 + 886064 * 2 ^ 59
def prefixEnd_886064 : Nat := 4983230072969 + 3 ^ 40 * 886064 * 2
def baseEnd_886064 : Nat := 303317815097017669483381

theorem tailTrace_886064 : CollatzResearch.WordTrace tailWord_886064 prefixEnd_886064 303317815097017669483381 := by
  unfold tailWord_886064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16158704530974465264248623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21544939374632620352331497 16158704530974465264248623)
  ·
    refine ⟨24238056796461697896372935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16158704530974465264248623 24238056796461697896372935)
    ·
      refine ⟨36357085194692546844559403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24238056796461697896372935 36357085194692546844559403)
      ·
        refine ⟨54535627792038820266839105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36357085194692546844559403 54535627792038820266839105)
        ·
          refine ⟨40901720844029115200129329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54535627792038820266839105 40901720844029115200129329)
          ·
            refine ⟨30676290633021836400096997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40901720844029115200129329 30676290633021836400096997)
            ·
              refine ⟨5751804493691594325018187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30676290633021836400096997 5751804493691594325018187)
              ·
                refine ⟨8627706740537391487527281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751804493691594325018187 8627706740537391487527281)
                ·
                  refine ⟨6470780055403043615645461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8627706740537391487527281 6470780055403043615645461)
                  ·
                    refine ⟨303317815097017669483381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6470780055403043615645461 303317815097017669483381)
                    ·
                      rfl

theorem cell22_886064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_886064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886064 prefixEnd_886064 := by exact prefixLift 886064
  have htrace : WordTrace (prefixWord ++ tailWord_886064) baseStart_886064 baseEnd_886064 := by
    simpa [prefixWord, tailWord_886064, baseEnd_886064] using wordTrace_append hprefix tailTrace_886064
  have hstable : (prefixWord ++ tailWord_886064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886064).length < 2 ^ (prefixWord ++ tailWord_886064).sum := by decide
  have hdescent : baseEnd_886064 < baseStart_886064 := by decide
  rcases family_descends (prefixWord ++ tailWord_886064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886100 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_886100 : Nat := 118140960795 + 886100 * 2 ^ 59
def prefixEnd_886100 : Nat := 4983230072969 + 3 ^ 40 * 886100 * 2
def baseEnd_886100 : Nat := 303330138632725575583271

theorem tailTrace_886100 : CollatzResearch.WordTrace tailWord_886100 prefixEnd_886100 303330138632725575583271 := by
  unfold tailWord_886100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16159361044909254338403877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21545814726545672451205169 16159361044909254338403877)
  ·
    refine ⟨3029880195920485188450727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16159361044909254338403877 3029880195920485188450727)
    ·
      refine ⟨4544820293880727782676091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029880195920485188450727 4544820293880727782676091)
      ·
        refine ⟨6817230440821091674014137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544820293880727782676091 6817230440821091674014137)
        ·
          refine ⟨5112922830615818755510603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6817230440821091674014137 5112922830615818755510603)
          ·
            refine ⟨7669384245923728133265905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112922830615818755510603 7669384245923728133265905)
            ·
              refine ⟨5752038184442796099949429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7669384245923728133265905 5752038184442796099949429)
              ·
                refine ⟨539253579791512134370259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5752038184442796099949429 539253579791512134370259)
                ·
                  refine ⟨808880369687268201555389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539253579791512134370259 808880369687268201555389)
                  ·
                    refine ⟨303330138632725575583271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 808880369687268201555389 303330138632725575583271)
                    ·
                      rfl

theorem cell22_886100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_886100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886100 prefixEnd_886100 := by exact prefixLift 886100
  have htrace : WordTrace (prefixWord ++ tailWord_886100) baseStart_886100 baseEnd_886100 := by
    simpa [prefixWord, tailWord_886100, baseEnd_886100] using wordTrace_append hprefix tailTrace_886100
  have hstable : (prefixWord ++ tailWord_886100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886100).length < 2 ^ (prefixWord ++ tailWord_886100).sum := by decide
  have hdescent : baseEnd_886100 < baseStart_886100 := by decide
  rcases family_descends (prefixWord ++ tailWord_886100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886102 : List Nat := [5, 2, 3, 1, 2, 9]
def baseStart_886102 : Nat := 118140960795 + 886102 * 2 ^ 59
def prefixEnd_886102 : Nat := 4983230072969 + 3 ^ 40 * 886102 * 2
def baseEnd_886102 : Nat := 3744824978686397988065

theorem tailTrace_886102 : CollatzResearch.WordTrace tailWord_886102 prefixEnd_886102 3744824978686397988065 := by
  unfold tailWord_886102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019924689738203938648785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21545863357207508678920373 2019924689738203938648785)
  ·
    refine ⟨1514943517303652953986589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2019924689738203938648785 1514943517303652953986589)
    ·
      refine ⟨568103818988869857744971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1514943517303652953986589 568103818988869857744971)
      ·
        refine ⟨852155728483304786617457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568103818988869857744971 852155728483304786617457)
        ·
          refine ⟨639116796362478589963093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852155728483304786617457 639116796362478589963093)
          ·
            refine ⟨3744824978686397988065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 639116796362478589963093 3744824978686397988065)
            ·
              rfl

theorem cell22_886102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 9].length) (baseStart_886102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886102 prefixEnd_886102 := by exact prefixLift 886102
  have htrace : WordTrace (prefixWord ++ tailWord_886102) baseStart_886102 baseEnd_886102 := by
    simpa [prefixWord, tailWord_886102, baseEnd_886102] using wordTrace_append hprefix tailTrace_886102
  have hstable : (prefixWord ++ tailWord_886102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886102).length < 2 ^ (prefixWord ++ tailWord_886102).sum := by decide
  have hdescent : baseEnd_886102 < baseStart_886102 := by decide
  rcases family_descends (prefixWord ++ tailWord_886102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886141 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 6]
def baseStart_886141 : Nat := 118140960795 + 886141 * 2 ^ 59
def prefixEnd_886141 : Nat := 4983230072969 + 3 ^ 40 * 886141 * 2
def baseEnd_886141 : Nat := 101114724590205045102715

theorem tailTrace_886141 : CollatzResearch.WordTrace tailWord_886141 prefixEnd_886141 101114724590205045102715 := by
  unfold tailWord_886141
  simp only [CollatzResearch.WordTrace]
  refine ⟨32320217482669972679050277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21546811655113315119366851 32320217482669972679050277)
  ·
    refine ⟨6060040778000619877321927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32320217482669972679050277 6060040778000619877321927)
    ·
      refine ⟨9090061167000929815982891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060040778000619877321927 9090061167000929815982891)
      ·
        refine ⟨13635091750501394723974337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9090061167000929815982891 13635091750501394723974337)
        ·
          refine ⟨10226318812876046042980753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13635091750501394723974337 10226318812876046042980753)
          ·
            refine ⟨7669739109657034532235565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10226318812876046042980753 7669739109657034532235565)
            ·
              refine ⟨2876152166121387949588337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7669739109657034532235565 2876152166121387949588337)
              ·
                refine ⟨2157114124591040962191253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876152166121387949588337 2157114124591040962191253)
                ·
                  refine ⟨101114724590205045102715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2157114124591040962191253 101114724590205045102715)
                  ·
                    rfl

theorem cell22_886141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_886141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886141 prefixEnd_886141 := by exact prefixLift 886141
  have htrace : WordTrace (prefixWord ++ tailWord_886141) baseStart_886141 baseEnd_886141 := by
    simpa [prefixWord, tailWord_886141, baseEnd_886141] using wordTrace_append hprefix tailTrace_886141
  have hstable : (prefixWord ++ tailWord_886141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886141).length < 2 ^ (prefixWord ++ tailWord_886141).sum := by decide
  have hdescent : baseEnd_886141 < baseStart_886141 := by decide
  rcases family_descends (prefixWord ++ tailWord_886141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886156 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_886156 : Nat := 118140960795 + 886156 * 2 ^ 59
def prefixEnd_886156 : Nat := 4983230072969 + 3 ^ 40 * 886156 * 2
def baseEnd_886156 : Nat := 303349308577160096183099

theorem tailTrace_886156 : CollatzResearch.WordTrace tailWord_886156 prefixEnd_886156 303349308577160096183099 := by
  unfold tailWord_886156
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160382288807815120423161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21547176385077086827230881 16160382288807815120423161)
  ·
    refine ⟨12120286716605861340317371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16160382288807815120423161 12120286716605861340317371)
    ·
      refine ⟨18180430074908792010476057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120286716605861340317371 18180430074908792010476057)
      ·
        refine ⟨13635322556181594007857043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18180430074908792010476057 13635322556181594007857043)
        ·
          refine ⟨20452983834272391011785565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635322556181594007857043 20452983834272391011785565)
          ·
            refine ⟨7669868937852146629419587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20452983834272391011785565 7669868937852146629419587)
            ·
              refine ⟨11504803406778219944129381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669868937852146629419587 11504803406778219944129381)
              ·
                refine ⟨2157150638770916239524259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11504803406778219944129381 2157150638770916239524259)
                ·
                  refine ⟨3235725958156374359286389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2157150638770916239524259 3235725958156374359286389)
                  ·
                    refine ⟨303349308577160096183099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3235725958156374359286389 303349308577160096183099)
                    ·
                      rfl

theorem cell22_886156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_886156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886156 prefixEnd_886156 := by exact prefixLift 886156
  have htrace : WordTrace (prefixWord ++ tailWord_886156) baseStart_886156 baseEnd_886156 := by
    simpa [prefixWord, tailWord_886156, baseEnd_886156] using wordTrace_append hprefix tailTrace_886156
  have hstable : (prefixWord ++ tailWord_886156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886156).length < 2 ^ (prefixWord ++ tailWord_886156).sum := by decide
  have hdescent : baseEnd_886156 < baseStart_886156 := by decide
  rcases family_descends (prefixWord ++ tailWord_886156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886248 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_886248 : Nat := 118140960795 + 886248 * 2 ^ 59
def prefixEnd_886248 : Nat := 4983230072969 + 3 ^ 40 * 886248 * 2
def baseEnd_886248 : Nat := 101126934019100840960939

theorem tailTrace_886248 : CollatzResearch.WordTrace tailWord_886248 prefixEnd_886248 101126934019100840960939 := by
  unfold tailWord_886248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16162060046641164976597699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21549413395521553302130265 16162060046641164976597699)
  ·
    refine ⟨24243090069961747464896549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16162060046641164976597699 24243090069961747464896549)
    ·
      refine ⟨4545579388117827649668103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24243090069961747464896549 4545579388117827649668103)
      ·
        refine ⟨6818369082176741474502155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545579388117827649668103 6818369082176741474502155)
        ·
          refine ⟨10227553623265112211753233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6818369082176741474502155 10227553623265112211753233)
          ·
            refine ⟨7670665217448834158814925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10227553623265112211753233 7670665217448834158814925)
            ·
              refine ⟨2876499456543312809555597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7670665217448834158814925 2876499456543312809555597)
              ·
                refine ⟨1078687296203742303583349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2876499456543312809555597 1078687296203742303583349)
                ·
                  refine ⟨101126934019100840960939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1078687296203742303583349 101126934019100840960939)
                  ·
                    rfl

theorem cell22_886248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_886248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886248 prefixEnd_886248 := by exact prefixLift 886248
  have htrace : WordTrace (prefixWord ++ tailWord_886248) baseStart_886248 baseEnd_886248 := by
    simpa [prefixWord, tailWord_886248, baseEnd_886248] using wordTrace_append hprefix tailTrace_886248
  have hstable : (prefixWord ++ tailWord_886248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886248).length < 2 ^ (prefixWord ++ tailWord_886248).sum := by decide
  have hdescent : baseEnd_886248 < baseStart_886248 := by decide
  rcases family_descends (prefixWord ++ tailWord_886248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886286 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_886286 : Nat := 118140960795 + 886286 * 2 ^ 59
def prefixEnd_886286 : Nat := 4983230072969 + 3 ^ 40 * 886286 * 2
def baseEnd_886286 : Nat := 303393810233883090432701

theorem tailTrace_886286 : CollatzResearch.WordTrace tailWord_886286 prefixEnd_886286 303393810233883090432701 := by
  unfold tailWord_886286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040688258393082805384839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21550337378096441628719141 4040688258393082805384839)
  ·
    refine ⟨6061032387589624208077259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040688258393082805384839 6061032387589624208077259)
    ·
      refine ⟨9091548581384436312115889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061032387589624208077259 9091548581384436312115889)
      ·
        refine ⟨6818661436038327234086917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091548581384436312115889 6818661436038327234086917)
        ·
          refine ⟨1278499019257186356391297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6818661436038327234086917 1278499019257186356391297)
          ·
            refine ⟨958874264442889767293473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278499019257186356391297 958874264442889767293473)
            ·
              refine ⟨719155698332167325470105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958874264442889767293473 719155698332167325470105)
              ·
                refine ⟨539366773749125494102579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719155698332167325470105 539366773749125494102579)
                ·
                  refine ⟨809050160623688241153869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539366773749125494102579 809050160623688241153869)
                  ·
                    refine ⟨303393810233883090432701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809050160623688241153869 303393810233883090432701)
                    ·
                      rfl

theorem cell22_886286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_886286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886286 prefixEnd_886286 := by exact prefixLift 886286
  have htrace : WordTrace (prefixWord ++ tailWord_886286) baseStart_886286 baseEnd_886286 := by
    simpa [prefixWord, tailWord_886286, baseEnd_886286] using wordTrace_append hprefix tailTrace_886286
  have hstable : (prefixWord ++ tailWord_886286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886286).length < 2 ^ (prefixWord ++ tailWord_886286).sum := by decide
  have hdescent : baseEnd_886286 < baseStart_886286 := by decide
  rcases family_descends (prefixWord ++ tailWord_886286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886323 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_886323 : Nat := 118140960795 + 886323 * 2 ^ 59
def prefixEnd_886323 : Nat := 4983230072969 + 3 ^ 40 * 886323 * 2
def baseEnd_886323 : Nat := 303406476090027327257587

theorem tailTrace_886323 : CollatzResearch.WordTrace tailWord_886323 prefixEnd_886323 303406476090027327257587 := by
  unfold tailWord_886323
  simp only [CollatzResearch.WordTrace]
  refine ⟨32326855568010617762175623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21551237045340411841450415 32326855568010617762175623)
  ·
    refine ⟨48490283352015926643263435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32326855568010617762175623 48490283352015926643263435)
    ·
      refine ⟨72735425028023889964895153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48490283352015926643263435 72735425028023889964895153)
      ·
        refine ⟨54551568771017917473671365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72735425028023889964895153 54551568771017917473671365)
        ·
          refine ⟨10228419144565859526313381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54551568771017917473671365 10228419144565859526313381)
          ·
            refine ⟨1917828589606098661183759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10228419144565859526313381 1917828589606098661183759)
            ·
              refine ⟨2876742884409147991775639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1917828589606098661183759 2876742884409147991775639)
              ·
                refine ⟨4315114326613721987663459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2876742884409147991775639 4315114326613721987663459)
                ·
                  refine ⟨6472671489920582981495189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315114326613721987663459 6472671489920582981495189)
                  ·
                    refine ⟨303406476090027327257587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6472671489920582981495189 303406476090027327257587)
                    ·
                      rfl

theorem cell22_886323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_886323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886323 prefixEnd_886323 := by exact prefixLift 886323
  have htrace : WordTrace (prefixWord ++ tailWord_886323) baseStart_886323 baseEnd_886323 := by
    simpa [prefixWord, tailWord_886323, baseEnd_886323] using wordTrace_append hprefix tailTrace_886323
  have hstable : (prefixWord ++ tailWord_886323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886323).length < 2 ^ (prefixWord ++ tailWord_886323).sum := by decide
  have hdescent : baseEnd_886323 < baseStart_886323 := by decide
  rcases family_descends (prefixWord ++ tailWord_886323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886404 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_886404 : Nat := 118140960795 + 886404 * 2 ^ 59
def prefixEnd_886404 : Nat := 4983230072969 + 3 ^ 40 * 886404 * 2
def baseEnd_886404 : Nat := 303434204045370115982339

theorem tailTrace_886404 : CollatzResearch.WordTrace tailWord_886404 prefixEnd_886404 303434204045370115982339 := by
  unfold tailWord_886404
  simp only [CollatzResearch.WordTrace]
  refine ⟨16164904940358584297937133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21553206587144779063916177 16164904940358584297937133)
  ·
    refine ⟨6061839352634469111726425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16164904940358584297937133 6061839352634469111726425)
    ·
      refine ⟨4546379514475851833794819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6061839352634469111726425 4546379514475851833794819)
      ·
        refine ⟨6819569271713777750692229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4546379514475851833794819 6819569271713777750692229)
        ·
          refine ⟨1278669238446333328254793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6819569271713777750692229 1278669238446333328254793)
          ·
            refine ⟨959001928834749996191095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278669238446333328254793 959001928834749996191095)
            ·
              refine ⟨1438502893252124994286643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959001928834749996191095 1438502893252124994286643)
              ·
                refine ⟨2157754339878187491429965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438502893252124994286643 2157754339878187491429965)
                ·
                  refine ⟨809157877454320309286237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2157754339878187491429965 809157877454320309286237)
                  ·
                    refine ⟨303434204045370115982339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809157877454320309286237 303434204045370115982339)
                    ·
                      rfl

theorem cell22_886404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_886404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886404 prefixEnd_886404 := by exact prefixLift 886404
  have htrace : WordTrace (prefixWord ++ tailWord_886404) baseStart_886404 baseEnd_886404 := by
    simpa [prefixWord, tailWord_886404, baseEnd_886404] using wordTrace_append hprefix tailTrace_886404
  have hstable : (prefixWord ++ tailWord_886404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886404).length < 2 ^ (prefixWord ++ tailWord_886404).sum := by decide
  have hdescent : baseEnd_886404 < baseStart_886404 := by decide
  rcases family_descends (prefixWord ++ tailWord_886404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886447 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 1, 4]
def baseStart_886447 : Nat := 118140960795 + 886447 * 2 ^ 59
def prefixEnd_886447 : Nat := 4983230072969 + 3 ^ 40 * 886447 * 2
def baseEnd_886447 : Nat := 303448923824132337157207

theorem tailTrace_886447 : CollatzResearch.WordTrace tailWord_886447 prefixEnd_886447 303448923824132337157207 := by
  unfold tailWord_886447
  simp only [CollatzResearch.WordTrace]
  refine ⟨32331378219561386939689595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21554252146374257959793063 32331378219561386939689595)
  ·
    refine ⟨48497067329342080409534393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32331378219561386939689595 48497067329342080409534393)
    ·
      refine ⟨36372800497006560307150795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48497067329342080409534393 36372800497006560307150795)
      ·
        refine ⟨54559200745509840460726193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36372800497006560307150795 54559200745509840460726193)
        ·
          refine ⟨40919400559132380345544645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54559200745509840460726193 40919400559132380345544645)
          ·
            refine ⟨7672387604837321314789621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40919400559132380345544645 7672387604837321314789621)
            ·
              refine ⟨719286337953498873261527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7672387604837321314789621 719286337953498873261527)
              ·
                refine ⟨1078929506930248309892291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719286337953498873261527 1078929506930248309892291)
                ·
                  refine ⟨1618394260395372464838437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078929506930248309892291 1618394260395372464838437)
                  ·
                    refine ⟨303448923824132337157207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618394260395372464838437 303448923824132337157207)
                    ·
                      rfl

theorem cell22_886447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_886447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886447 prefixEnd_886447 := by exact prefixLift 886447
  have htrace : WordTrace (prefixWord ++ tailWord_886447) baseStart_886447 baseEnd_886447 := by
    simpa [prefixWord, tailWord_886447, baseEnd_886447] using wordTrace_append hprefix tailTrace_886447
  have hstable : (prefixWord ++ tailWord_886447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886447).length < 2 ^ (prefixWord ++ tailWord_886447).sum := by decide
  have hdescent : baseEnd_886447 < baseStart_886447 := by decide
  rcases family_descends (prefixWord ++ tailWord_886447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886466 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_886466 : Nat := 118140960795 + 886466 * 2 ^ 59
def prefixEnd_886466 : Nat := 4983230072969 + 3 ^ 40 * 886466 * 2
def baseEnd_886466 : Nat := 303455427912422620932149

theorem tailTrace_886466 : CollatzResearch.WordTrace tailWord_886466 prefixEnd_886466 303455427912422620932149 := by
  unfold tailWord_886466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8083017801623138296157813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21554714137661702123087501 8083017801623138296157813)
  ·
    refine ⟨757782918902169215264795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8083017801623138296157813 757782918902169215264795)
    ·
      refine ⟨1136674378353253822897193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757782918902169215264795 1136674378353253822897193)
      ·
        refine ⟨852505783764940367172895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1136674378353253822897193 852505783764940367172895)
        ·
          refine ⟨1278758675647410550759343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852505783764940367172895 1278758675647410550759343)
          ·
            refine ⟨1918138013471115826139015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278758675647410550759343 1918138013471115826139015)
            ·
              refine ⟨2877207020206673739208523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918138013471115826139015 2877207020206673739208523)
              ·
                refine ⟨4315810530310010608812785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877207020206673739208523 4315810530310010608812785)
                ·
                  refine ⟨3236857897732507956609589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4315810530310010608812785 3236857897732507956609589)
                  ·
                    refine ⟨303455427912422620932149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3236857897732507956609589 303455427912422620932149)
                    ·
                      rfl

theorem cell22_886466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_886466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886466 prefixEnd_886466 := by exact prefixLift 886466
  have htrace : WordTrace (prefixWord ++ tailWord_886466) baseStart_886466 baseEnd_886466 := by
    simpa [prefixWord, tailWord_886466, baseEnd_886466] using wordTrace_append hprefix tailTrace_886466
  have hstable : (prefixWord ++ tailWord_886466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886466).length < 2 ^ (prefixWord ++ tailWord_886466).sum := by decide
  have hdescent : baseEnd_886466 < baseStart_886466 := by decide
  rcases family_descends (prefixWord ++ tailWord_886466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886505 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_886505 : Nat := 118140960795 + 886505 * 2 ^ 59
def prefixEnd_886505 : Nat := 4983230072969 + 3 ^ 40 * 886505 * 2
def baseEnd_886505 : Nat := 303468778409439519207029

theorem tailTrace_886505 : CollatzResearch.WordTrace tailWord_886505 prefixEnd_886505 303468778409439519207029 := by
  unfold tailWord_886505
  simp only [CollatzResearch.WordTrace]
  refine ⟨32333493653351262845300969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21555662435567508563533979 32333493653351262845300969)
  ·
    refine ⟨24250120240013447133975727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32333493653351262845300969 24250120240013447133975727)
    ·
      refine ⟨36375180360020170700963591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24250120240013447133975727 36375180360020170700963591)
      ·
        refine ⟨54562770540030256051445387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36375180360020170700963591 54562770540030256051445387)
        ·
          refine ⟨81844155810045384077168081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54562770540030256051445387 81844155810045384077168081)
          ·
            refine ⟨61383116857534038057876061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81844155810045384077168081 61383116857534038057876061)
            ·
              refine ⟨23018668821575264271703523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61383116857534038057876061 23018668821575264271703523)
              ·
                refine ⟨34528003232362896407555285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23018668821575264271703523 34528003232362896407555285)
                ·
                  refine ⟨809250075758505384552077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 34528003232362896407555285 809250075758505384552077)
                  ·
                    refine ⟨303468778409439519207029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809250075758505384552077 303468778409439519207029)
                    ·
                      rfl

theorem cell22_886505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_886505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886505 prefixEnd_886505 := by exact prefixLift 886505
  have htrace : WordTrace (prefixWord ++ tailWord_886505) baseStart_886505 baseEnd_886505 := by
    simpa [prefixWord, tailWord_886505, baseEnd_886505] using wordTrace_append hprefix tailTrace_886505
  have hstable : (prefixWord ++ tailWord_886505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886505).length < 2 ^ (prefixWord ++ tailWord_886505).sum := by decide
  have hdescent : baseEnd_886505 < baseStart_886505 := by decide
  rcases family_descends (prefixWord ++ tailWord_886505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886612 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_886612 : Nat := 118140960795 + 886612 * 2 ^ 59
def prefixEnd_886612 : Nat := 4983230072969 + 3 ^ 40 * 886612 * 2
def baseEnd_886612 : Nat := 303505406696126906781701

theorem tailTrace_886612 : CollatzResearch.WordTrace tailWord_886612 prefixEnd_886612 303505406696126906781701 := by
  unfold tailWord_886612
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168698131981810059723045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21558264175975746746297393 16168698131981810059723045)
  ·
    refine ⟨3031630899746589386198071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16168698131981810059723045 3031630899746589386198071)
    ·
      refine ⟨4547446349619884079297107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031630899746589386198071 4547446349619884079297107)
      ·
        refine ⟨6821169524429826118945661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4547446349619884079297107 6821169524429826118945661)
        ·
          refine ⟨2557938571661184794604623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6821169524429826118945661 2557938571661184794604623)
          ·
            refine ⟨3836907857491777191906935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557938571661184794604623 3836907857491777191906935)
            ·
              refine ⟨5755361786237665787860403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3836907857491777191906935 5755361786237665787860403)
              ·
                refine ⟨8633042679356498681790605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755361786237665787860403 8633042679356498681790605)
                ·
                  refine ⟨3237391004758687005671477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8633042679356498681790605 3237391004758687005671477)
                  ·
                    refine ⟨303505406696126906781701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3237391004758687005671477 303505406696126906781701)
                    ·
                      rfl

theorem cell22_886612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_886612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886612 prefixEnd_886612 := by exact prefixLift 886612
  have htrace : WordTrace (prefixWord ++ tailWord_886612) baseStart_886612 baseEnd_886612 := by
    simpa [prefixWord, tailWord_886612, baseEnd_886612] using wordTrace_append hprefix tailTrace_886612
  have hstable : (prefixWord ++ tailWord_886612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886612).length < 2 ^ (prefixWord ++ tailWord_886612).sum := by decide
  have hdescent : baseEnd_886612 < baseStart_886612 := by decide
  rcases family_descends (prefixWord ++ tailWord_886612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886640 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_886640 : Nat := 118140960795 + 886640 * 2 ^ 59
def prefixEnd_886640 : Nat := 4983230072969 + 3 ^ 40 * 886640 * 2
def baseEnd_886640 : Nat := 303514991668344167081615

theorem tailTrace_886640 : CollatzResearch.WordTrace tailWord_886640 prefixEnd_886640 303514991668344167081615 := by
  unfold tailWord_886640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169208753931090450732687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21558945005241453934310249 16169208753931090450732687)
  ·
    refine ⟨24253813130896635676099031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16169208753931090450732687 24253813130896635676099031)
    ·
      refine ⟨36380719696344953514148547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24253813130896635676099031 36380719696344953514148547)
      ·
        refine ⟨54571079544517430271222821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36380719696344953514148547 54571079544517430271222821)
        ·
          refine ⟨10232077414597018175854279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54571079544517430271222821 10232077414597018175854279)
          ·
            refine ⟨15348116121895527263781419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232077414597018175854279 15348116121895527263781419)
            ·
              refine ⟨23022174182843290895672129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15348116121895527263781419 23022174182843290895672129)
              ·
                refine ⟨17266630637132468171754097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23022174182843290895672129 17266630637132468171754097)
                ·
                  refine ⟨12949972977849351128815573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17266630637132468171754097 12949972977849351128815573)
                  ·
                    refine ⟨303514991668344167081615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12949972977849351128815573 303514991668344167081615)
                    ·
                      rfl

theorem cell22_886640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_886640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886640 prefixEnd_886640 := by exact prefixLift 886640
  have htrace : WordTrace (prefixWord ++ tailWord_886640) baseStart_886640 baseEnd_886640 := by
    simpa [prefixWord, tailWord_886640, baseEnd_886640] using wordTrace_append hprefix tailTrace_886640
  have hstable : (prefixWord ++ tailWord_886640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886640).length < 2 ^ (prefixWord ++ tailWord_886640).sum := by decide
  have hdescent : baseEnd_886640 < baseStart_886640 := by decide
  rcases family_descends (prefixWord ++ tailWord_886640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886646 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_886646 : Nat := 118140960795 + 886646 * 2 ^ 59
def prefixEnd_886646 : Nat := 4983230072969 + 3 ^ 40 * 886646 * 2
def baseEnd_886646 : Nat := 303517045590962151431597

theorem tailTrace_886646 : CollatzResearch.WordTrace tailWord_886646 prefixEnd_886646 303517045590962151431597 := by
  unfold tailWord_886646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021164771615027745386487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21559090897226962617455861 2021164771615027745386487)
  ·
    refine ⟨3031747157422541618079731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2021164771615027745386487 3031747157422541618079731)
    ·
      refine ⟨4547620736133812427119597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3031747157422541618079731 4547620736133812427119597)
      ·
        refine ⟨1705357776050179660169849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4547620736133812427119597 1705357776050179660169849)
        ·
          refine ⟨1279018332037634745127387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705357776050179660169849 1279018332037634745127387)
          ·
            refine ⟨1918527498056452117691081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279018332037634745127387 1918527498056452117691081)
            ·
              refine ⟨1438895623542339088268311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918527498056452117691081 1438895623542339088268311)
              ·
                refine ⟨2158343435313508632402467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438895623542339088268311 2158343435313508632402467)
                ·
                  refine ⟨3237515152970262948603701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158343435313508632402467 3237515152970262948603701)
                  ·
                    refine ⟨303517045590962151431597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3237515152970262948603701 303517045590962151431597)
                    ·
                      rfl

theorem cell22_886646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_886646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886646 prefixEnd_886646 := by exact prefixLift 886646
  have htrace : WordTrace (prefixWord ++ tailWord_886646) baseStart_886646 baseEnd_886646 := by
    simpa [prefixWord, tailWord_886646, baseEnd_886646] using wordTrace_append hprefix tailTrace_886646
  have hstable : (prefixWord ++ tailWord_886646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886646).length < 2 ^ (prefixWord ++ tailWord_886646).sum := by decide
  have hdescent : baseEnd_886646 < baseStart_886646 := by decide
  rcases family_descends (prefixWord ++ tailWord_886646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886655 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_886655 : Nat := 118140960795 + 886655 * 2 ^ 59
def prefixEnd_886655 : Nat := 4983230072969 + 3 ^ 40 * 886655 * 2
def baseEnd_886655 : Nat := 303520126474889127956569

theorem tailTrace_886655 : CollatzResearch.WordTrace tailWord_886655 prefixEnd_886655 303520126474889127956569 := by
  unfold tailWord_886655
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338964602807838463261419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21559309735205225642174279 32338964602807838463261419)
  ·
    refine ⟨48508446904211757694892129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32338964602807838463261419 48508446904211757694892129)
    ·
      refine ⟨36381335178158818271169097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48508446904211757694892129 36381335178158818271169097)
      ·
        refine ⟨27286001383619113703376823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36381335178158818271169097 27286001383619113703376823)
        ·
          refine ⟨40929002075428670555065235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27286001383619113703376823 40929002075428670555065235)
          ·
            refine ⟨61393503113143005832597853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40929002075428670555065235 61393503113143005832597853)
            ·
              refine ⟨23022563667428627187224195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61393503113143005832597853 23022563667428627187224195)
              ·
                refine ⟨34533845501142940780836293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23022563667428627187224195 34533845501142940780836293)
                ·
                  refine ⟨6475096031464301396406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34533845501142940780836293 6475096031464301396406805)
                  ·
                    refine ⟨303520126474889127956569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6475096031464301396406805 303520126474889127956569)
                    ·
                      rfl

theorem cell22_886655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_886655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886655 prefixEnd_886655 := by exact prefixLift 886655
  have htrace : WordTrace (prefixWord ++ tailWord_886655) baseStart_886655 baseEnd_886655 := by
    simpa [prefixWord, tailWord_886655, baseEnd_886655] using wordTrace_append hprefix tailTrace_886655
  have hstable : (prefixWord ++ tailWord_886655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886655).length < 2 ^ (prefixWord ++ tailWord_886655).sum := by decide
  have hdescent : baseEnd_886655 < baseStart_886655 := by decide
  rcases family_descends (prefixWord ++ tailWord_886655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886680 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_886680 : Nat := 118140960795 + 886680 * 2 ^ 59
def prefixEnd_886680 : Nat := 4983230072969 + 3 ^ 40 * 886680 * 2
def baseEnd_886680 : Nat := 303528684485797396081493

theorem tailTrace_886680 : CollatzResearch.WordTrace tailWord_886680 prefixEnd_886680 303528684485797396081493 := by
  unfold tailWord_886680
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169938213858633866460747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21559917618478178488614329 16169938213858633866460747)
  ·
    refine ⟨24254907320787950799691121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16169938213858633866460747 24254907320787950799691121)
    ·
      refine ⟨18191180490590963099768341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24254907320787950799691121 18191180490590963099768341)
      ·
        refine ⟨852711585496451395301641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18191180490590963099768341 852711585496451395301641)
        ·
          refine ⟨639533689122338546476231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852711585496451395301641 639533689122338546476231)
          ·
            refine ⟨959300533683507819714347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639533689122338546476231 959300533683507819714347)
            ·
              refine ⟨1438950800525261729571521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959300533683507819714347 1438950800525261729571521)
              ·
                refine ⟨1079213100393946297178641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438950800525261729571521 1079213100393946297178641)
                ·
                  refine ⟨809409825295459722883981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079213100393946297178641 809409825295459722883981)
                  ·
                    refine ⟨303528684485797396081493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809409825295459722883981 303528684485797396081493)
                    ·
                      rfl

theorem cell22_886680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_886680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886680 prefixEnd_886680 := by exact prefixLift 886680
  have htrace : WordTrace (prefixWord ++ tailWord_886680) baseStart_886680 baseEnd_886680 := by
    simpa [prefixWord, tailWord_886680, baseEnd_886680] using wordTrace_append hprefix tailTrace_886680
  have hstable : (prefixWord ++ tailWord_886680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886680).length < 2 ^ (prefixWord ++ tailWord_886680).sum := by decide
  have hdescent : baseEnd_886680 < baseStart_886680 := by decide
  rcases family_descends (prefixWord ++ tailWord_886680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886734 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_886734 : Nat := 118140960795 + 886734 * 2 ^ 59
def prefixEnd_886734 : Nat := 4983230072969 + 3 ^ 40 * 886734 * 2
def baseEnd_886734 : Nat := 303547169789359255231327

theorem tailTrace_886734 : CollatzResearch.WordTrace tailWord_886734 prefixEnd_886734 303547169789359255231327 := by
  unfold tailWord_886734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042730746190204369423407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21561230646347756636924837 4042730746190204369423407)
  ·
    refine ⟨6064096119285306554135111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042730746190204369423407 6064096119285306554135111)
    ·
      refine ⟨9096144178927959831202667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6064096119285306554135111 9096144178927959831202667)
      ·
        refine ⟨13644216268391939746804001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9096144178927959831202667 13644216268391939746804001)
        ·
          refine ⟨10233162201293954810103001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13644216268391939746804001 10233162201293954810103001)
          ·
            refine ⟨7674871650970466107577251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10233162201293954810103001 7674871650970466107577251)
            ·
              refine ⟨11512307476455699161365877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674871650970466107577251 11512307476455699161365877)
              ·
                refine ⟨1079278825917721796378051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11512307476455699161365877 1079278825917721796378051)
                ·
                  refine ⟨1618918238876582694567077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079278825917721796378051 1618918238876582694567077)
                  ·
                    refine ⟨303547169789359255231327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1618918238876582694567077 303547169789359255231327)
                    ·
                      rfl

theorem cell22_886734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_886734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886734 prefixEnd_886734 := by exact prefixLift 886734
  have htrace : WordTrace (prefixWord ++ tailWord_886734) baseStart_886734 baseEnd_886734 := by
    simpa [prefixWord, tailWord_886734, baseEnd_886734] using wordTrace_append hprefix tailTrace_886734
  have hstable : (prefixWord ++ tailWord_886734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886734).length < 2 ^ (prefixWord ++ tailWord_886734).sum := by decide
  have hdescent : baseEnd_886734 < baseStart_886734 := by decide
  rcases family_descends (prefixWord ++ tailWord_886734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886742 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_886742 : Nat := 118140960795 + 886742 * 2 ^ 59
def prefixEnd_886742 : Nat := 4983230072969 + 3 ^ 40 * 886742 * 2
def baseEnd_886742 : Nat := 303549908352849901031303

theorem tailTrace_886742 : CollatzResearch.WordTrace tailWord_886742 prefixEnd_886742 303549908352849901031303 := by
  unfold tailWord_886742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021383609593290770104905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21561425168995101547785653 2021383609593290770104905)
  ·
    refine ⟨1516037707194968077578679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2021383609593290770104905 1516037707194968077578679)
    ·
      refine ⟨2274056560792452116368019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516037707194968077578679 2274056560792452116368019)
      ·
        refine ⟨3411084841188678174552029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274056560792452116368019 3411084841188678174552029)
        ·
          refine ⟨1279156815445754315457011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3411084841188678174552029 1279156815445754315457011)
          ·
            refine ⟨1918735223168631473185517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279156815445754315457011 1918735223168631473185517)
            ·
              refine ⟨719525708688236802444569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918735223168631473185517 719525708688236802444569)
              ·
                refine ⟨539644281516177601833427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719525708688236802444569 539644281516177601833427)
                ·
                  refine ⟨809466422274266402750141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539644281516177601833427 809466422274266402750141)
                  ·
                    refine ⟨303549908352849901031303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809466422274266402750141 303549908352849901031303)
                    ·
                      rfl

theorem cell22_886742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_886742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886742 prefixEnd_886742 := by exact prefixLift 886742
  have htrace : WordTrace (prefixWord ++ tailWord_886742) baseStart_886742 baseEnd_886742 := by
    simpa [prefixWord, tailWord_886742, baseEnd_886742] using wordTrace_append hprefix tailTrace_886742
  have hstable : (prefixWord ++ tailWord_886742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886742).length < 2 ^ (prefixWord ++ tailWord_886742).sum := by decide
  have hdescent : baseEnd_886742 < baseStart_886742 := by decide
  rcases family_descends (prefixWord ++ tailWord_886742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886777 : List Nat := [1, 2, 1, 3, 1, 4, 2, 8]
def baseStart_886777 : Nat := 118140960795 + 886777 * 2 ^ 59
def prefixEnd_886777 : Nat := 4983230072969 + 3 ^ 40 * 886777 * 2
def baseEnd_886777 : Nat := 33729098840902386267355

theorem tailTrace_886777 : CollatzResearch.WordTrace tailWord_886777 prefixEnd_886777 33729098840902386267355 := by
  unfold tailWord_886777
  simp only [CollatzResearch.WordTrace]
  refine ⟨32343414308365853299202585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21562276205577235532801723 32343414308365853299202585)
  ·
    refine ⟨24257560731274389974401939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32343414308365853299202585 24257560731274389974401939)
    ·
      refine ⟨36386341096911584961602909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257560731274389974401939 36386341096911584961602909)
      ·
        refine ⟨13644877911341844360601091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36386341096911584961602909 13644877911341844360601091)
        ·
          refine ⟨20467316867012766540901637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13644877911341844360601091 20467316867012766540901637)
          ·
            refine ⟨3837621912564893726419057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20467316867012766540901637 3837621912564893726419057)
            ·
              refine ⟨2878216434423670294814293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837621912564893726419057 2878216434423670294814293)
              ·
                refine ⟨33729098840902386267355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2878216434423670294814293 33729098840902386267355)
                ·
                  rfl

theorem cell22_886777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 8].length) (baseStart_886777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886777 prefixEnd_886777 := by exact prefixLift 886777
  have htrace : WordTrace (prefixWord ++ tailWord_886777) baseStart_886777 baseEnd_886777 := by
    simpa [prefixWord, tailWord_886777, baseEnd_886777] using wordTrace_append hprefix tailTrace_886777
  have hstable : (prefixWord ++ tailWord_886777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886777).length < 2 ^ (prefixWord ++ tailWord_886777).sum := by decide
  have hdescent : baseEnd_886777 < baseStart_886777 := by decide
  rcases family_descends (prefixWord ++ tailWord_886777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886794 : List Nat := [3, 1, 2, 2, 5, 9]
def baseStart_886794 : Nat := 118140960795 + 886794 * 2 ^ 59
def prefixEnd_886794 : Nat := 4983230072969 + 3 ^ 40 * 886794 * 2
def baseEnd_886794 : Nat := 3747749494019001218903

theorem tailTrace_886794 : CollatzResearch.WordTrace tailWord_886794 prefixEnd_886794 3747749494019001218903 := by
  unfold tailWord_886794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086008587326066300642859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21562689566202843468380957 8086008587326066300642859)
  ·
    refine ⟨12129012880989099450964289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086008587326066300642859 12129012880989099450964289)
    ·
      refine ⟨9096759660741824588223217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12129012880989099450964289 9096759660741824588223217)
      ·
        refine ⟨6822569745556368441167413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9096759660741824588223217 6822569745556368441167413)
        ·
          refine ⟨639615913645909541359445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6822569745556368441167413 639615913645909541359445)
          ·
            refine ⟨3747749494019001218903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 639615913645909541359445 3747749494019001218903)
            ·
              rfl

theorem cell22_886794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 9].length) (baseStart_886794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886794 prefixEnd_886794 := by exact prefixLift 886794
  have htrace : WordTrace (prefixWord ++ tailWord_886794) baseStart_886794 baseEnd_886794 := by
    simpa [prefixWord, tailWord_886794, baseEnd_886794] using wordTrace_append hprefix tailTrace_886794
  have hstable : (prefixWord ++ tailWord_886794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886794).length < 2 ^ (prefixWord ++ tailWord_886794).sum := by decide
  have hdescent : baseEnd_886794 < baseStart_886794 := by decide
  rcases family_descends (prefixWord ++ tailWord_886794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886809 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_886809 : Nat := 118140960795 + 886809 * 2 ^ 59
def prefixEnd_886809 : Nat := 4983230072969 + 3 ^ 40 * 886809 * 2
def baseEnd_886809 : Nat := 303572843822084059606097

theorem tailTrace_886809 : CollatzResearch.WordTrace tailWord_886809 prefixEnd_886809 303572843822084059606097 := by
  unfold tailWord_886809
  simp only [CollatzResearch.WordTrace]
  refine ⟨32344581444249922764367481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21563054296166615176244987 32344581444249922764367481)
  ·
    refine ⟨24258436083187442073275611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32344581444249922764367481 24258436083187442073275611)
    ·
      refine ⟨36387654124781163109913417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24258436083187442073275611 36387654124781163109913417)
      ·
        refine ⟨27290740593585872332435063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36387654124781163109913417 27290740593585872332435063)
        ·
          refine ⟨40936110890378808498652595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27290740593585872332435063 40936110890378808498652595)
          ·
            refine ⟨61404166335568212747978893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40936110890378808498652595 61404166335568212747978893)
            ·
              refine ⟨23026562375838079780492085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61404166335568212747978893 23026562375838079780492085)
              ·
                refine ⟨2158740222734819979421133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23026562375838079780492085 2158740222734819979421133)
                ·
                  refine ⟨809527583525557492282925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2158740222734819979421133 809527583525557492282925)
                  ·
                    refine ⟨303572843822084059606097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809527583525557492282925 303572843822084059606097)
                    ·
                      rfl

theorem cell22_886809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_886809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886809 prefixEnd_886809 := by exact prefixLift 886809
  have htrace : WordTrace (prefixWord ++ tailWord_886809) baseStart_886809 baseEnd_886809 := by
    simpa [prefixWord, tailWord_886809, baseEnd_886809] using wordTrace_append hprefix tailTrace_886809
  have hstable : (prefixWord ++ tailWord_886809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886809).length < 2 ^ (prefixWord ++ tailWord_886809).sum := by decide
  have hdescent : baseEnd_886809 < baseStart_886809 := by decide
  rcases family_descends (prefixWord ++ tailWord_886809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886826 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_886826 : Nat := 118140960795 + 886826 * 2 ^ 59
def prefixEnd_886826 : Nat := 4983230072969 + 3 ^ 40 * 886826 * 2
def baseEnd_886826 : Nat := 303578663269501681931045

theorem tailTrace_886826 : CollatzResearch.WordTrace tailWord_886826 prefixEnd_886826 303578663269501681931045 := by
  unfold tailWord_886826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086300371297083666934083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21563467656792223111824221 8086300371297083666934083)
  ·
    refine ⟨12129450556945625500401125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086300371297083666934083 12129450556945625500401125)
    ·
      refine ⟨2274271979427304781325211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12129450556945625500401125 2274271979427304781325211)
      ·
        refine ⟨3411407969140957171987817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274271979427304781325211 3411407969140957171987817)
        ·
          refine ⟨2558555976855717878990863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411407969140957171987817 2558555976855717878990863)
          ·
            refine ⟨3837833965283576818486295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558555976855717878990863 3837833965283576818486295)
            ·
              refine ⟨5756750947925365227729443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837833965283576818486295 5756750947925365227729443)
              ·
                refine ⟨8635126421888047841594165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756750947925365227729443 8635126421888047841594165)
                ·
                  refine ⟨809543102052004485149453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8635126421888047841594165 809543102052004485149453)
                  ·
                    refine ⟨303578663269501681931045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809543102052004485149453 303578663269501681931045)
                    ·
                      rfl

theorem cell22_886826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_886826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886826 prefixEnd_886826 := by exact prefixLift 886826
  have htrace : WordTrace (prefixWord ++ tailWord_886826) baseStart_886826 baseEnd_886826 := by
    simpa [prefixWord, tailWord_886826, baseEnd_886826] using wordTrace_append hprefix tailTrace_886826
  have hstable : (prefixWord ++ tailWord_886826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886826).length < 2 ^ (prefixWord ++ tailWord_886826).sum := by decide
  have hdescent : baseEnd_886826 < baseStart_886826 := by decide
  rcases family_descends (prefixWord ++ tailWord_886826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886884 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_886884 : Nat := 118140960795 + 886884 * 2 ^ 59
def prefixEnd_886884 : Nat := 4983230072969 + 3 ^ 40 * 886884 * 2
def baseEnd_886884 : Nat := 101199505951602954660289

theorem tailTrace_886884 : CollatzResearch.WordTrace tailWord_886884 prefixEnd_886884 101199505951602954660289 := by
  unfold tailWord_886884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16173658459489105286673853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21564877945985473715565137 16173658459489105286673853)
  ·
    refine ⟨6065121922308414482502695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16173658459489105286673853 6065121922308414482502695)
    ·
      refine ⟨9097682883462621723754043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065121922308414482502695 9097682883462621723754043)
      ·
        refine ⟨13646524325193932585631065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097682883462621723754043 13646524325193932585631065)
        ·
          refine ⟨10234893243895449439223299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13646524325193932585631065 10234893243895449439223299)
          ·
            refine ⟨15352339865843174158834949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234893243895449439223299 15352339865843174158834949)
            ·
              refine ⟨2878563724845595154781553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15352339865843174158834949 2878563724845595154781553)
              ·
                refine ⟨2158922793634196366086165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878563724845595154781553 2158922793634196366086165)
                ·
                  refine ⟨101199505951602954660289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2158922793634196366086165 101199505951602954660289)
                  ·
                    rfl

theorem cell22_886884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_886884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886884 prefixEnd_886884 := by exact prefixLift 886884
  have htrace : WordTrace (prefixWord ++ tailWord_886884) baseStart_886884 baseEnd_886884 := by
    simpa [prefixWord, tailWord_886884, baseEnd_886884] using wordTrace_append hprefix tailTrace_886884
  have hstable : (prefixWord ++ tailWord_886884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886884).length < 2 ^ (prefixWord ++ tailWord_886884).sum := by decide
  have hdescent : baseEnd_886884 < baseStart_886884 := by decide
  rcases family_descends (prefixWord ++ tailWord_886884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886916 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_886916 : Nat := 118140960795 + 886916 * 2 ^ 59
def prefixEnd_886916 : Nat := 4983230072969 + 3 ^ 40 * 886916 * 2
def baseEnd_886916 : Nat := 303609472108771447180769

theorem tailTrace_886916 : CollatzResearch.WordTrace tailWord_886916 prefixEnd_886916 303609472108771447180769 := by
  unfold tailWord_886916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174242027431140019256301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21565656036574853359008401 16174242027431140019256301)
  ·
    refine ⟨6065340760286677507221113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16174242027431140019256301 6065340760286677507221113)
    ·
      refine ⟨4549005570215008130415835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6065340760286677507221113 4549005570215008130415835)
      ·
        refine ⟨6823508355322512195623753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4549005570215008130415835 6823508355322512195623753)
        ·
          refine ⟨5117631266491884146717815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6823508355322512195623753 5117631266491884146717815)
          ·
            refine ⟨7676446899737826220076723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117631266491884146717815 7676446899737826220076723)
            ·
              refine ⟨11514670349606739330115085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676446899737826220076723 11514670349606739330115085)
              ·
                refine ⟨4318001381102527248793157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11514670349606739330115085 4318001381102527248793157)
                ·
                  refine ⟨809625258956723859148717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4318001381102527248793157 809625258956723859148717)
                  ·
                    refine ⟨303609472108771447180769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809625258956723859148717 303609472108771447180769)
                    ·
                      rfl

theorem cell22_886916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_886916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886916 prefixEnd_886916 := by exact prefixLift 886916
  have htrace : WordTrace (prefixWord ++ tailWord_886916) baseStart_886916 baseEnd_886916 := by
    simpa [prefixWord, tailWord_886916, baseEnd_886916] using wordTrace_append hprefix tailTrace_886916
  have hstable : (prefixWord ++ tailWord_886916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886916).length < 2 ^ (prefixWord ++ tailWord_886916).sum := by decide
  have hdescent : baseEnd_886916 < baseStart_886916 := by decide
  rcases family_descends (prefixWord ++ tailWord_886916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886946 : List Nat := [3, 3, 1, 3, 1, 1, 2, 8]
def baseStart_886946 : Nat := 118140960795 + 886946 * 2 ^ 59
def prefixEnd_886946 : Nat := 4983230072969 + 3 ^ 40 * 886946 * 2
def baseEnd_886946 : Nat := 33735526857984596547853

theorem tailTrace_886946 : CollatzResearch.WordTrace tailWord_886946 prefixEnd_886946 33735526857984596547853 := by
  unfold tailWord_886946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087394561188398790526173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21566385496502396774736461 8087394561188398790526173)
  ·
    refine ⟨3032772960445649546447315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8087394561188398790526173 3032772960445649546447315)
    ·
      refine ⟨4549159440668474319670973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3032772960445649546447315 4549159440668474319670973)
      ·
        refine ⟨1705934790250677869876615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4549159440668474319670973 1705934790250677869876615)
        ·
          refine ⟨2558902185376016804814923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705934790250677869876615 2558902185376016804814923)
          ·
            refine ⟨3838353278064025207222385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558902185376016804814923 3838353278064025207222385)
            ·
              refine ⟨2878764958548018905416789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838353278064025207222385 2878764958548018905416789)
              ·
                refine ⟨33735526857984596547853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2878764958548018905416789 33735526857984596547853)
                ·
                  rfl

theorem cell22_886946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_886946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886946 prefixEnd_886946 := by exact prefixLift 886946
  have htrace : WordTrace (prefixWord ++ tailWord_886946) baseStart_886946 baseEnd_886946 := by
    simpa [prefixWord, tailWord_886946, baseEnd_886946] using wordTrace_append hprefix tailTrace_886946
  have hstable : (prefixWord ++ tailWord_886946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886946).length < 2 ^ (prefixWord ++ tailWord_886946).sum := by decide
  have hdescent : baseEnd_886946 < baseStart_886946 := by decide
  rcases family_descends (prefixWord ++ tailWord_886946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886948 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_886948 : Nat := 118140960795 + 886948 * 2 ^ 59
def prefixEnd_886948 : Nat := 4983230072969 + 3 ^ 40 * 886948 * 2
def baseEnd_886948 : Nat := 303620426362734030380671

theorem tailTrace_886948 : CollatzResearch.WordTrace tailWord_886948 prefixEnd_886948 303620426362734030380671 := by
  unfold tailWord_886948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174825595373174751838749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21566434127164233002451665 16174825595373174751838749)
  ·
    refine ⟨6065559598264940531939531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16174825595373174751838749 6065559598264940531939531)
    ·
      refine ⟨9098339397397410797909297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065559598264940531939531 9098339397397410797909297)
      ·
        refine ⟨6823754548048058098431973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098339397397410797909297 6823754548048058098431973)
        ·
          refine ⟨1279453977759010893455995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6823754548048058098431973 1279453977759010893455995)
          ·
            refine ⟨1919180966638516340183993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279453977759010893455995 1919180966638516340183993)
            ·
              refine ⟨1439385724978887255137995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919180966638516340183993 1439385724978887255137995)
              ·
                refine ⟨2159078587468330882706993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439385724978887255137995 2159078587468330882706993)
                ·
                  refine ⟨1619308940601248162030245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159078587468330882706993 1619308940601248162030245)
                  ·
                    refine ⟨303620426362734030380671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619308940601248162030245 303620426362734030380671)
                    ·
                      rfl

theorem cell22_886948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_886948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_886948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_886948 prefixEnd_886948 := by exact prefixLift 886948
  have htrace : WordTrace (prefixWord ++ tailWord_886948) baseStart_886948 baseEnd_886948 := by
    simpa [prefixWord, tailWord_886948, baseEnd_886948] using wordTrace_append hprefix tailTrace_886948
  have hstable : (prefixWord ++ tailWord_886948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886948).length < 2 ^ (prefixWord ++ tailWord_886948).sum := by decide
  have hdescent : baseEnd_886948 < baseStart_886948 := by decide
  rcases family_descends (prefixWord ++ tailWord_886948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887019 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 8]
def baseStart_887019 : Nat := 118140960795 + 887019 * 2 ^ 59
def prefixEnd_887019 : Nat := 4983230072969 + 3 ^ 40 * 887019 * 2
def baseEnd_887019 : Nat := 101214910371237837285151

theorem tailTrace_887019 : CollatzResearch.WordTrace tailWord_887019 prefixEnd_887019 101214910371237837285151 := by
  unfold tailWord_887019
  simp only [CollatzResearch.WordTrace]
  refine ⟨32352240773489128629512111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21568160515659419086341407 32352240773489128629512111)
  ·
    refine ⟨48528361160233692944268167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32352240773489128629512111 48528361160233692944268167)
    ·
      refine ⟨72792541740350539416402251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48528361160233692944268167 72792541740350539416402251)
      ·
        refine ⟨109188812610525809124603377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72792541740350539416402251 109188812610525809124603377)
        ·
          refine ⟨81891609457894356843452533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109188812610525809124603377 81891609457894356843452533)
          ·
            refine ⟨7677338386677595954073675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81891609457894356843452533 7677338386677595954073675)
            ·
              refine ⟨11516007580016393931110513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677338386677595954073675 11516007580016393931110513)
              ·
                refine ⟨8637005685012295448332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11516007580016393931110513 8637005685012295448332885)
                ·
                  refine ⟨101214910371237837285151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8637005685012295448332885 101214910371237837285151)
                  ·
                    rfl

theorem cell22_887019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_887019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887019 prefixEnd_887019 := by exact prefixLift 887019
  have htrace : WordTrace (prefixWord ++ tailWord_887019) baseStart_887019 baseEnd_887019 := by
    simpa [prefixWord, tailWord_887019, baseEnd_887019] using wordTrace_append hprefix tailTrace_887019
  have hstable : (prefixWord ++ tailWord_887019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887019).length < 2 ^ (prefixWord ++ tailWord_887019).sum := by decide
  have hdescent : baseEnd_887019 < baseStart_887019 := by decide
  rcases family_descends (prefixWord ++ tailWord_887019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887036 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_887036 : Nat := 118140960795 + 887036 * 2 ^ 59
def prefixEnd_887036 : Nat := 4983230072969 + 3 ^ 40 * 887036 * 2
def baseEnd_887036 : Nat := 101216850187043711393467

theorem tailTrace_887036 : CollatzResearch.WordTrace tailWord_887036 prefixEnd_887036 101216850187043711393467 := by
  unfold tailWord_887036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176430407213770266440481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21568573876285027021920641 16176430407213770266440481)
  ·
    refine ⟨12132322805410327699830361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16176430407213770266440481 12132322805410327699830361)
    ·
      refine ⟨9099242104057745774872771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12132322805410327699830361 9099242104057745774872771)
      ·
        refine ⟨13648863156086618662309157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099242104057745774872771 13648863156086618662309157)
        ·
          refine ⟨2559161841766240999182967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13648863156086618662309157 2559161841766240999182967)
          ·
            refine ⟨3838742762649361498774451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559161841766240999182967 3838742762649361498774451)
            ·
              refine ⟨5758114143974042248161677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838742762649361498774451 5758114143974042248161677)
              ·
                refine ⟨2159292803990265843060629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5758114143974042248161677 2159292803990265843060629)
                ·
                  refine ⟨101216850187043711393467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2159292803990265843060629 101216850187043711393467)
                  ·
                    rfl

theorem cell22_887036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_887036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887036 prefixEnd_887036 := by exact prefixLift 887036
  have htrace : WordTrace (prefixWord ++ tailWord_887036) baseStart_887036 baseEnd_887036 := by
    simpa [prefixWord, tailWord_887036, baseEnd_887036] using wordTrace_append hprefix tailTrace_887036
  have hstable : (prefixWord ++ tailWord_887036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887036).length < 2 ^ (prefixWord ++ tailWord_887036).sum := by decide
  have hdescent : baseEnd_887036 < baseStart_887036 := by decide
  rcases family_descends (prefixWord ++ tailWord_887036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887102 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_887102 : Nat := 118140960795 + 887102 * 2 ^ 59
def prefixEnd_887102 : Nat := 4983230072969 + 3 ^ 40 * 887102 * 2
def baseEnd_887102 : Nat := 303673143709928962030199

theorem tailTrace_887102 : CollatzResearch.WordTrace tailWord_887102 prefixEnd_887102 303673143709928962030199 := by
  unfold tailWord_887102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044408504023554225597945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21570178688125622536522373 4044408504023554225597945)
  ·
    refine ⟨3033306378017665669198459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4044408504023554225597945 3033306378017665669198459)
    ·
      refine ⟨4549959567026498503797689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3033306378017665669198459 4549959567026498503797689)
      ·
        refine ⟨3412469675269873877848267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4549959567026498503797689 3412469675269873877848267)
        ·
          refine ⟨5118704512904810816772401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412469675269873877848267 5118704512904810816772401)
          ·
            refine ⟨3839028384678608112579301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5118704512904810816772401 3839028384678608112579301)
            ·
              refine ⟨719817822127239021108619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3839028384678608112579301 719817822127239021108619)
              ·
                refine ⟨1079726733190858531662929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719817822127239021108619 1079726733190858531662929)
                ·
                  refine ⟨809795049893143898747197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1079726733190858531662929 809795049893143898747197)
                  ·
                    refine ⟨303673143709928962030199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809795049893143898747197 303673143709928962030199)
                    ·
                      rfl

theorem cell22_887102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_887102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887102 prefixEnd_887102 := by exact prefixLift 887102
  have htrace : WordTrace (prefixWord ++ tailWord_887102) baseStart_887102 baseEnd_887102 := by
    simpa [prefixWord, tailWord_887102, baseEnd_887102] using wordTrace_append hprefix tailTrace_887102
  have hstable : (prefixWord ++ tailWord_887102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887102).length < 2 ^ (prefixWord ++ tailWord_887102).sum := by decide
  have hdescent : baseEnd_887102 < baseStart_887102 := by decide
  rcases family_descends (prefixWord ++ tailWord_887102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887130 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_887130 : Nat := 118140960795 + 887130 * 2 ^ 59
def prefixEnd_887130 : Nat := 4983230072969 + 3 ^ 40 * 887130 * 2
def baseEnd_887130 : Nat := 303682728682146222330113

theorem tailTrace_887130 : CollatzResearch.WordTrace tailWord_887130 prefixEnd_887130 303682728682146222330113 := by
  unfold tailWord_887130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089072319021748646700711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21570859517391329724535229 8089072319021748646700711)
  ·
    refine ⟨12133608478532622970051067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8089072319021748646700711 12133608478532622970051067)
    ·
      refine ⟨18200412717798934455076601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12133608478532622970051067 18200412717798934455076601)
      ·
        refine ⟨13650309538349200841307451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18200412717798934455076601 13650309538349200841307451)
        ·
          refine ⟨20475464307523801261961177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13650309538349200841307451 20475464307523801261961177)
          ·
            refine ⟨15356598230642850946470883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20475464307523801261961177 15356598230642850946470883)
            ·
              refine ⟨23034897345964276419706325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15356598230642850946470883 23034897345964276419706325)
              ·
                refine ⟨539880406546037728586867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23034897345964276419706325 539880406546037728586867)
                ·
                  refine ⟨809820609819056592880301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539880406546037728586867 809820609819056592880301)
                  ·
                    refine ⟨303682728682146222330113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809820609819056592880301 303682728682146222330113)
                    ·
                      rfl

theorem cell22_887130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_887130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887130 prefixEnd_887130 := by exact prefixLift 887130
  have htrace : WordTrace (prefixWord ++ tailWord_887130) baseStart_887130 baseEnd_887130 := by
    simpa [prefixWord, tailWord_887130, baseEnd_887130] using wordTrace_append hprefix tailTrace_887130
  have hstable : (prefixWord ++ tailWord_887130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887130).length < 2 ^ (prefixWord ++ tailWord_887130).sum := by decide
  have hdescent : baseEnd_887130 < baseStart_887130 := by decide
  rcases family_descends (prefixWord ++ tailWord_887130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887143 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 5]
def baseStart_887143 : Nat := 118140960795 + 887143 * 2 ^ 59
def prefixEnd_887143 : Nat := 4983230072969 + 3 ^ 40 * 887143 * 2
def baseEnd_887143 : Nat := 101229059615939507251691

theorem tailTrace_887143 : CollatzResearch.WordTrace tailWord_887143 prefixEnd_887143 101229059615939507251691 := by
  unfold tailWord_887143
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356763425039897807026083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21571175616693265204684055 32356763425039897807026083)
  ·
    refine ⟨48535145137559846710539125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32356763425039897807026083 48535145137559846710539125)
    ·
      refine ⟨4550169856646235629113043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48535145137559846710539125 4550169856646235629113043)
      ·
        refine ⟨6825254784969353443669565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550169856646235629113043 6825254784969353443669565)
        ·
          refine ⟨2559470544363507541376087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6825254784969353443669565 2559470544363507541376087)
          ·
            refine ⟨3839205816545261312064131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559470544363507541376087 3839205816545261312064131)
            ·
              refine ⟨5758808724817891968096197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839205816545261312064131 5758808724817891968096197)
              ·
                refine ⟨1079776635903354744018037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5758808724817891968096197 1079776635903354744018037)
                ·
                  refine ⟨101229059615939507251691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1079776635903354744018037 101229059615939507251691)
                  ·
                    rfl

theorem cell22_887143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 5].length) (baseStart_887143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887143 prefixEnd_887143 := by exact prefixLift 887143
  have htrace : WordTrace (prefixWord ++ tailWord_887143) baseStart_887143 baseEnd_887143 := by
    simpa [prefixWord, tailWord_887143, baseEnd_887143] using wordTrace_append hprefix tailTrace_887143
  have hstable : (prefixWord ++ tailWord_887143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887143).length < 2 ^ (prefixWord ++ tailWord_887143).sum := by decide
  have hdescent : baseEnd_887143 < baseStart_887143 := by decide
  rcases family_descends (prefixWord ++ tailWord_887143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887173 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_887173 : Nat := 118140960795 + 887173 * 2 ^ 59
def prefixEnd_887173 : Nat := 4983230072969 + 3 ^ 40 * 887173 * 2
def baseEnd_887173 : Nat := 303697448460908443504981

theorem tailTrace_887173 : CollatzResearch.WordTrace tailWord_887173 prefixEnd_887173 303697448460908443504981 := by
  unfold tailWord_887173
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357857614931212930618173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21571905076620808620412115 32357857614931212930618173)
  ·
    refine ⟨12134196605599204848981815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32357857614931212930618173 12134196605599204848981815)
    ·
      refine ⟨18201294908398807273472723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12134196605599204848981815 18201294908398807273472723)
      ·
        refine ⟨27301942362598210910209085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18201294908398807273472723 27301942362598210910209085)
        ·
          refine ⟨10238228385974329091328407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27301942362598210910209085 10238228385974329091328407)
          ·
            refine ⟨15357342578961493636992611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238228385974329091328407 15357342578961493636992611)
            ·
              refine ⟨23036013868442240455488917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15357342578961493636992611 23036013868442240455488917)
              ·
                refine ⟨1079813150083230021351043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23036013868442240455488917 1079813150083230021351043)
                ·
                  refine ⟨1619719725124845032026565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079813150083230021351043 1619719725124845032026565)
                  ·
                    refine ⟨303697448460908443504981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619719725124845032026565 303697448460908443504981)
                    ·
                      rfl

theorem cell22_887173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_887173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887173 prefixEnd_887173 := by exact prefixLift 887173
  have htrace : WordTrace (prefixWord ++ tailWord_887173) baseStart_887173 baseEnd_887173 := by
    simpa [prefixWord, tailWord_887173, baseEnd_887173] using wordTrace_append hprefix tailTrace_887173
  have hstable : (prefixWord ++ tailWord_887173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887173).length < 2 ^ (prefixWord ++ tailWord_887173).sum := by decide
  have hdescent : baseEnd_887173 < baseStart_887173 := by decide
  rcases family_descends (prefixWord ++ tailWord_887173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887316 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_887316 : Nat := 118140960795 + 887316 * 2 ^ 59
def prefixEnd_887316 : Nat := 4983230072969 + 3 ^ 40 * 887316 * 2
def baseEnd_887316 : Nat := 303746400283303737179543

theorem tailTrace_887316 : CollatzResearch.WordTrace tailWord_887316 prefixEnd_887316 303746400283303737179543 := by
  unfold tailWord_887316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16181536626706574176536901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21575382168942098902049201 16181536626706574176536901)
  ·
    refine ⟨3034038117507482658100669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16181536626706574176536901 3034038117507482658100669)
    ·
      refine ⟨1137764294065305996787751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3034038117507482658100669 1137764294065305996787751)
      ·
        refine ⟨1706646441097958995181627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137764294065305996787751 1706646441097958995181627)
        ·
          refine ⟨2559969661646938492772441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706646441097958995181627 2559969661646938492772441)
          ·
            refine ⟨1919977246235203869579331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559969661646938492772441 1919977246235203869579331)
            ·
              refine ⟨2879965869352805804368997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919977246235203869579331 2879965869352805804368997)
              ·
                refine ⟨539993600503651088319187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2879965869352805804368997 539993600503651088319187)
                ·
                  refine ⟨809990400755476632478781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539993600503651088319187 809990400755476632478781)
                  ·
                    refine ⟨303746400283303737179543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 809990400755476632478781 303746400283303737179543)
                    ·
                      rfl

theorem cell22_887316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_887316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887316 prefixEnd_887316 := by exact prefixLift 887316
  have htrace : WordTrace (prefixWord ++ tailWord_887316) baseStart_887316 baseEnd_887316 := by
    simpa [prefixWord, tailWord_887316, baseEnd_887316] using wordTrace_append hprefix tailTrace_887316
  have hstable : (prefixWord ++ tailWord_887316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887316).length < 2 ^ (prefixWord ++ tailWord_887316).sum := by decide
  have hdescent : baseEnd_887316 < baseStart_887316 := by decide
  rcases family_descends (prefixWord ++ tailWord_887316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887325 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_887325 : Nat := 118140960795 + 887325 * 2 ^ 59
def prefixEnd_887325 : Nat := 4983230072969 + 3 ^ 40 * 887325 * 2
def baseEnd_887325 : Nat := 303749481167230713704515

theorem tailTrace_887325 : CollatzResearch.WordTrace tailWord_887325 prefixEnd_887325 303749481167230713704515 := by
  unfold tailWord_887325
  simp only [CollatzResearch.WordTrace]
  refine ⟨32363401510380542890151429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21575601006920361926767619 32363401510380542890151429)
  ·
    refine ⟨6068137783196351791903393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32363401510380542890151429 6068137783196351791903393)
    ·
      refine ⟨4551103337397263843927545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6068137783196351791903393 4551103337397263843927545)
      ·
        refine ⟨3413327503047947882945659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4551103337397263843927545 3413327503047947882945659)
        ·
          refine ⟨5119991254571921824418489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413327503047947882945659 5119991254571921824418489)
          ·
            refine ⟨3839993440928941368313867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119991254571921824418489 3839993440928941368313867)
            ·
              refine ⟨5759990161393412052470801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839993440928941368313867 5759990161393412052470801)
              ·
                refine ⟨4319992621045059039353101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759990161393412052470801 4319992621045059039353101)
                ·
                  refine ⟨1619997232891897139757413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4319992621045059039353101 1619997232891897139757413)
                  ·
                    refine ⟨303749481167230713704515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619997232891897139757413 303749481167230713704515)
                    ·
                      rfl

theorem cell22_887325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_887325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887325 prefixEnd_887325 := by exact prefixLift 887325
  have htrace : WordTrace (prefixWord ++ tailWord_887325) baseStart_887325 baseEnd_887325 := by
    simpa [prefixWord, tailWord_887325, baseEnd_887325] using wordTrace_append hprefix tailTrace_887325
  have hstable : (prefixWord ++ tailWord_887325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887325).length < 2 ^ (prefixWord ++ tailWord_887325).sum := by decide
  have hdescent : baseEnd_887325 < baseStart_887325 := by decide
  rcases family_descends (prefixWord ++ tailWord_887325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887357 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 4]
def baseStart_887357 : Nat := 118140960795 + 887357 * 2 ^ 59
def prefixEnd_887357 : Nat := 4983230072969 + 3 ^ 40 * 887357 * 2
def baseEnd_887357 : Nat := 101253478473731098968139

theorem tailTrace_887357 : CollatzResearch.WordTrace tailWord_887357 prefixEnd_887357 101253478473731098968139 := by
  unfold tailWord_887357
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364568646264612355316325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21576379097509741570210883 32364568646264612355316325)
  ·
    refine ⟨6068356621174614816621811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32364568646264612355316325 6068356621174614816621811)
    ·
      refine ⟨9102534931761922224932717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068356621174614816621811 9102534931761922224932717)
      ·
        refine ⟨3413450599410720834349769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9102534931761922224932717 3413450599410720834349769)
        ·
          refine ⟨2560087949558040625762327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413450599410720834349769 2560087949558040625762327)
          ·
            refine ⟨3840131924337060938643491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560087949558040625762327 3840131924337060938643491)
            ·
              refine ⟨5760197886505591407965237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840131924337060938643491 5760197886505591407965237)
              ·
                refine ⟨540018551859899194496741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5760197886505591407965237 540018551859899194496741)
                ·
                  refine ⟨101253478473731098968139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540018551859899194496741 101253478473731098968139)
                  ·
                    rfl

theorem cell22_887357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_887357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887357 prefixEnd_887357 := by exact prefixLift 887357
  have htrace : WordTrace (prefixWord ++ tailWord_887357) baseStart_887357 baseEnd_887357 := by
    simpa [prefixWord, tailWord_887357, baseEnd_887357] using wordTrace_append hprefix tailTrace_887357
  have hstable : (prefixWord ++ tailWord_887357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887357).length < 2 ^ (prefixWord ++ tailWord_887357).sum := by decide
  have hdescent : baseEnd_887357 < baseStart_887357 := by decide
  rcases family_descends (prefixWord ++ tailWord_887357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887505 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_887505 : Nat := 118140960795 + 887505 * 2 ^ 59
def prefixEnd_887505 : Nat := 4983230072969 + 3 ^ 40 * 887505 * 2
def baseEnd_887505 : Nat := 303811098845770244203963

theorem tailTrace_887505 : CollatzResearch.WordTrace tailWord_887505 prefixEnd_887505 303811098845770244203963 := by
  unfold tailWord_887505
  simp only [CollatzResearch.WordTrace]
  refine ⟨32369966649728433631703969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21579977766485622421135979 32369966649728433631703969)
  ·
    refine ⟨24277474987296325223777977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32369966649728433631703969 24277474987296325223777977)
    ·
      refine ⟨18208106240472243917833483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24277474987296325223777977 18208106240472243917833483)
      ·
        refine ⟨27312159360708365876750225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18208106240472243917833483 27312159360708365876750225)
        ·
          refine ⟨20484119520531274407562669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27312159360708365876750225 20484119520531274407562669)
          ·
            refine ⟨7681544820199227902836001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20484119520531274407562669 7681544820199227902836001)
            ·
              refine ⟨5761158615149420927127001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7681544820199227902836001 5761158615149420927127001)
              ·
                refine ⟨4320868961362065695345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761158615149420927127001 4320868961362065695345251)
                ·
                  refine ⟨6481303442043098543017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320868961362065695345251 6481303442043098543017877)
                  ·
                    refine ⟨303811098845770244203963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6481303442043098543017877 303811098845770244203963)
                    ·
                      rfl

theorem cell22_887505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_887505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887505 prefixEnd_887505 := by exact prefixLift 887505
  have htrace : WordTrace (prefixWord ++ tailWord_887505) baseStart_887505 baseEnd_887505 := by
    simpa [prefixWord, tailWord_887505, baseEnd_887505] using wordTrace_append hprefix tailTrace_887505
  have hstable : (prefixWord ++ tailWord_887505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887505).length < 2 ^ (prefixWord ++ tailWord_887505).sum := by decide
  have hdescent : baseEnd_887505 < baseStart_887505 := by decide
  rcases family_descends (prefixWord ++ tailWord_887505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887509 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 6]
def baseStart_887509 : Nat := 118140960795 + 887509 * 2 ^ 59
def prefixEnd_887509 : Nat := 4983230072969 + 3 ^ 40 * 887509 * 2
def baseEnd_887509 : Nat := 101270822709171855701317

theorem tailTrace_887509 : CollatzResearch.WordTrace tailWord_887509 prefixEnd_887509 101270822709171855701317 := by
  unfold tailWord_887509
  simp only [CollatzResearch.WordTrace]
  refine ⟨32370112541713942314849581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21580075027809294876566387 32370112541713942314849581)
  ·
    refine ⟨12138792203142728368068593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32370112541713942314849581 12138792203142728368068593)
    ·
      refine ⟨9104094152357046276051445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12138792203142728368068593 9104094152357046276051445)
      ·
        refine ⟨853508826783473088379823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9104094152357046276051445 853508826783473088379823)
        ·
          refine ⟨1280263240175209632569735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853508826783473088379823 1280263240175209632569735)
          ·
            refine ⟨1920394860262814448854603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280263240175209632569735 1920394860262814448854603)
            ·
              refine ⟨2880592290394221673281905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920394860262814448854603 2880592290394221673281905)
              ·
                refine ⟨2160444217795666254961429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880592290394221673281905 2160444217795666254961429)
                ·
                  refine ⟨101270822709171855701317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2160444217795666254961429 101270822709171855701317)
                  ·
                    rfl

theorem cell22_887509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_887509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887509 prefixEnd_887509 := by exact prefixLift 887509
  have htrace : WordTrace (prefixWord ++ tailWord_887509) baseStart_887509 baseEnd_887509 := by
    simpa [prefixWord, tailWord_887509, baseEnd_887509] using wordTrace_append hprefix tailTrace_887509
  have hstable : (prefixWord ++ tailWord_887509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887509).length < 2 ^ (prefixWord ++ tailWord_887509).sum := by decide
  have hdescent : baseEnd_887509 < baseStart_887509 := by decide
  rcases family_descends (prefixWord ++ tailWord_887509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887528 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_887528 : Nat := 118140960795 + 887528 * 2 ^ 59
def prefixEnd_887528 : Nat := 4983230072969 + 3 ^ 40 * 887528 * 2
def baseEnd_887528 : Nat := 303818972215805850878893

theorem tailTrace_887528 : CollatzResearch.WordTrace tailWord_887528 prefixEnd_887528 303818972215805850878893 := by
  unfold tailWord_887528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16185402764322554279895619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21580537019096739039860825 16185402764322554279895619)
  ·
    refine ⟨24278104146483831419843429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16185402764322554279895619 24278104146483831419843429)
    ·
      refine ⟨4552144527465718391220643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24278104146483831419843429 4552144527465718391220643)
      ·
        refine ⟨6828216791198577586830965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552144527465718391220643 6828216791198577586830965)
        ·
          refine ⟨640145324174866648765403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6828216791198577586830965 640145324174866648765403)
          ·
            refine ⟨960217986262299973148105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640145324174866648765403 960217986262299973148105)
            ·
              refine ⟨720163489696724979861079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960217986262299973148105 720163489696724979861079)
              ·
                refine ⟨1080245234545087469791619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720163489696724979861079 1080245234545087469791619)
                ·
                  refine ⟨1620367851817631204687429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080245234545087469791619 1620367851817631204687429)
                  ·
                    refine ⟨303818972215805850878893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620367851817631204687429 303818972215805850878893)
                    ·
                      rfl

theorem cell22_887528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_887528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887528 prefixEnd_887528 := by exact prefixLift 887528
  have htrace : WordTrace (prefixWord ++ tailWord_887528) baseStart_887528 baseEnd_887528 := by
    simpa [prefixWord, tailWord_887528, baseEnd_887528] using wordTrace_append hprefix tailTrace_887528
  have hstable : (prefixWord ++ tailWord_887528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887528).length < 2 ^ (prefixWord ++ tailWord_887528).sum := by decide
  have hdescent : baseEnd_887528 < baseStart_887528 := by decide
  rcases family_descends (prefixWord ++ tailWord_887528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887603 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 1, 3]
def baseStart_887603 : Nat := 118140960795 + 887603 * 2 ^ 59
def prefixEnd_887603 : Nat := 4983230072969 + 3 ^ 40 * 887603 * 2
def baseEnd_887603 : Nat := 303844646248530655253663

theorem tailTrace_887603 : CollatzResearch.WordTrace tailWord_887603 prefixEnd_887603 303844646248530655253663 := by
  unfold tailWord_887603
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373541003373396368771463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21582360668915597579180975 32373541003373396368771463)
  ·
    refine ⟨48560311505060094553157195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32373541003373396368771463 48560311505060094553157195)
    ·
      refine ⟨72840467257590141829735793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48560311505060094553157195 72840467257590141829735793)
      ·
        refine ⟨54630350443192606372301845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72840467257590141829735793 54630350443192606372301845)
        ·
          refine ⟨2560797677024653423701649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54630350443192606372301845 2560797677024653423701649)
          ·
            refine ⟨1920598257768490067776237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2560797677024653423701649 1920598257768490067776237)
            ·
              refine ⟨720224346663183775416089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920598257768490067776237 720224346663183775416089)
              ·
                refine ⟨540168259997387831562067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720224346663183775416089 540168259997387831562067)
                ·
                  refine ⟨810252389996081747343101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540168259997387831562067 810252389996081747343101)
                  ·
                    refine ⟨303844646248530655253663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810252389996081747343101 303844646248530655253663)
                    ·
                      rfl

theorem cell22_887603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 3].length) (baseStart_887603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887603 prefixEnd_887603 := by exact prefixLift 887603
  have htrace : WordTrace (prefixWord ++ tailWord_887603) baseStart_887603 baseEnd_887603 := by
    simpa [prefixWord, tailWord_887603, baseEnd_887603] using wordTrace_append hprefix tailTrace_887603
  have hstable : (prefixWord ++ tailWord_887603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887603).length < 2 ^ (prefixWord ++ tailWord_887603).sum := by decide
  have hdescent : baseEnd_887603 < baseStart_887603 := by decide
  rcases family_descends (prefixWord ++ tailWord_887603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887612 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_887612 : Nat := 118140960795 + 887612 * 2 ^ 59
def prefixEnd_887612 : Nat := 4983230072969 + 3 ^ 40 * 887612 * 2
def baseEnd_887612 : Nat := 303847727132457631778635

theorem tailTrace_887612 : CollatzResearch.WordTrace tailWord_887612 prefixEnd_887612 303847727132457631778635 := by
  unfold tailWord_887612
  simp only [CollatzResearch.WordTrace]
  refine ⟨16186934630170395452924545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21582579506893860603899393 16186934630170395452924545)
  ·
    refine ⟨12140200972627796589693409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16186934630170395452924545 12140200972627796589693409)
    ·
      refine ⟨9105150729470847442270057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12140200972627796589693409 9105150729470847442270057)
      ·
        refine ⟨6828863047103135581702543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9105150729470847442270057 6828863047103135581702543)
        ·
          refine ⟨10243294570654703372553815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828863047103135581702543 10243294570654703372553815)
          ·
            refine ⟨15364941855982055058830723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10243294570654703372553815 15364941855982055058830723)
            ·
              refine ⟨23047412783973082588246085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364941855982055058830723 23047412783973082588246085)
              ·
                refine ⟨4321389896994952985296141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23047412783973082588246085 4321389896994952985296141)
                ·
                  refine ⟨1620521211373107369486053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4321389896994952985296141 1620521211373107369486053)
                  ·
                    refine ⟨303847727132457631778635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620521211373107369486053 303847727132457631778635)
                    ·
                      rfl

theorem cell22_887612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_887612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887612 prefixEnd_887612 := by exact prefixLift 887612
  have htrace : WordTrace (prefixWord ++ tailWord_887612) baseStart_887612 baseEnd_887612 := by
    simpa [prefixWord, tailWord_887612, baseEnd_887612] using wordTrace_append hprefix tailTrace_887612
  have hstable : (prefixWord ++ tailWord_887612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887612).length < 2 ^ (prefixWord ++ tailWord_887612).sum := by decide
  have hdescent : baseEnd_887612 < baseStart_887612 := by decide
  rcases family_descends (prefixWord ++ tailWord_887612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887642 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_887642 : Nat := 118140960795 + 887642 * 2 ^ 59
def prefixEnd_887642 : Nat := 4983230072969 + 3 ^ 40 * 887642 * 2
def baseEnd_887642 : Nat := 303857996745547553528543

theorem tailTrace_887642 : CollatzResearch.WordTrace tailWord_887642 prefixEnd_887642 303857996745547553528543 := by
  unfold tailWord_887642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093740862558026507360295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21583308966821404019627453 8093740862558026507360295)
  ·
    refine ⟨12140611293837039761040443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8093740862558026507360295 12140611293837039761040443)
    ·
      refine ⟨18210916940755559641560665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12140611293837039761040443 18210916940755559641560665)
      ·
        refine ⟨13658187705566669731170499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18210916940755559641560665 13658187705566669731170499)
        ·
          refine ⟨20487281558350004596755749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13658187705566669731170499 20487281558350004596755749)
          ·
            refine ⟨3841365292190625861891703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20487281558350004596755749 3841365292190625861891703)
            ·
              refine ⟨5762047938285938792837555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841365292190625861891703 5762047938285938792837555)
              ·
                refine ⟨8643071907428908189256333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762047938285938792837555 8643071907428908189256333)
                ·
                  refine ⟨3241151965285840570971125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8643071907428908189256333 3241151965285840570971125)
                  ·
                    refine ⟨303857996745547553528543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3241151965285840570971125 303857996745547553528543)
                    ·
                      rfl

theorem cell22_887642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_887642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887642 prefixEnd_887642 := by exact prefixLift 887642
  have htrace : WordTrace (prefixWord ++ tailWord_887642) baseStart_887642 baseEnd_887642 := by
    simpa [prefixWord, tailWord_887642, baseEnd_887642] using wordTrace_append hprefix tailTrace_887642
  have hstable : (prefixWord ++ tailWord_887642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887642).length < 2 ^ (prefixWord ++ tailWord_887642).sum := by decide
  have hdescent : baseEnd_887642 < baseStart_887642 := by decide
  rcases family_descends (prefixWord ++ tailWord_887642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887659 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 2, 3]
def baseStart_887659 : Nat := 118140960795 + 887659 * 2 ^ 59
def prefixEnd_887659 : Nat := 4983230072969 + 3 ^ 40 * 887659 * 2
def baseEnd_887659 : Nat := 303863816192965175853491

theorem tailTrace_887659 : CollatzResearch.WordTrace tailWord_887659 prefixEnd_887659 303863816192965175853491 := by
  unfold tailWord_887659
  simp only [CollatzResearch.WordTrace]
  refine ⟨32375583491170517932810031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21583722327447011955206687 32375583491170517932810031)
  ·
    refine ⟨48563375236755776899215047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32375583491170517932810031 48563375236755776899215047)
    ·
      refine ⟨72845062855133665348822571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48563375236755776899215047 72845062855133665348822571)
      ·
        refine ⟨109267594282700498023233857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72845062855133665348822571 109267594282700498023233857)
        ·
          refine ⟨81950695712025373517425393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109267594282700498023233857 81950695712025373517425393)
          ·
            refine ⟨61463021784019030138069045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81950695712025373517425393 61463021784019030138069045)
            ·
              refine ⟨5762158292251784075443973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61463021784019030138069045 5762158292251784075443973)
              ·
                refine ⟨1080404679797209514145745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5762158292251784075443973 1080404679797209514145745)
                ·
                  refine ⟨810303509847907135609309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1080404679797209514145745 810303509847907135609309)
                  ·
                    refine ⟨303863816192965175853491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810303509847907135609309 303863816192965175853491)
                    ·
                      rfl

theorem cell22_887659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 3].length) (baseStart_887659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887659 prefixEnd_887659 := by exact prefixLift 887659
  have htrace : WordTrace (prefixWord ++ tailWord_887659) baseStart_887659 baseEnd_887659 := by
    simpa [prefixWord, tailWord_887659, baseEnd_887659] using wordTrace_append hprefix tailTrace_887659
  have hstable : (prefixWord ++ tailWord_887659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887659).length < 2 ^ (prefixWord ++ tailWord_887659).sum := by decide
  have hdescent : baseEnd_887659 < baseStart_887659 := by decide
  rcases family_descends (prefixWord ++ tailWord_887659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887689 : List Nat := [1, 2, 1, 1, 5, 3, 3, 6]
def baseStart_887689 : Nat := 118140960795 + 887689 * 2 ^ 59
def prefixEnd_887689 : Nat := 4983230072969 + 3 ^ 40 * 887689 * 2
def baseEnd_887689 : Nat := 33763787311783899733711

theorem tailTrace_887689 : CollatzResearch.WordTrace tailWord_887689 prefixEnd_887689 33763787311783899733711 := by
  unfold tailWord_887689
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376677681061833056402121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21584451787374555370934747 32376677681061833056402121)
  ·
    refine ⟨24282508260796374792301591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32376677681061833056402121 24282508260796374792301591)
    ·
      refine ⟨36423762391194562188452387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24282508260796374792301591 36423762391194562188452387)
      ·
        refine ⟨54635643586791843282678581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36423762391194562188452387 54635643586791843282678581)
        ·
          refine ⟨5122091586261735307751117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54635643586791843282678581 5122091586261735307751117)
          ·
            refine ⟨1920784344848150740406669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5122091586261735307751117 1920784344848150740406669)
            ·
              refine ⟨720294129318056527652501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1920784344848150740406669 720294129318056527652501)
              ·
                refine ⟨33763787311783899733711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720294129318056527652501 33763787311783899733711)
                ·
                  rfl

theorem cell22_887689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 6].length) (baseStart_887689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887689 prefixEnd_887689 := by exact prefixLift 887689
  have htrace : WordTrace (prefixWord ++ tailWord_887689) baseStart_887689 baseEnd_887689 := by
    simpa [prefixWord, tailWord_887689, baseEnd_887689] using wordTrace_append hprefix tailTrace_887689
  have hstable : (prefixWord ++ tailWord_887689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887689).length < 2 ^ (prefixWord ++ tailWord_887689).sum := by decide
  have hdescent : baseEnd_887689 < baseStart_887689 := by decide
  rcases family_descends (prefixWord ++ tailWord_887689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887721 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 1, 3]
def baseStart_887721 : Nat := 118140960795 + 887721 * 2 ^ 59
def prefixEnd_887721 : Nat := 4983230072969 + 3 ^ 40 * 887721 * 2
def baseEnd_887721 : Nat := 303885040060017680803301

theorem tailTrace_887721 : CollatzResearch.WordTrace tailWord_887721 prefixEnd_887721 303885040060017680803301 := by
  unfold tailWord_887721
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377844816945902521567017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21585229877963935014378011 32377844816945902521567017)
  ·
    refine ⟨24283383612709426891175263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32377844816945902521567017 24283383612709426891175263)
    ·
      refine ⟨36425075419064140336762895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24283383612709426891175263 36425075419064140336762895)
      ·
        refine ⟨54637613128596210505144343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36425075419064140336762895 54637613128596210505144343)
        ·
          refine ⟨81956419692894315757716515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54637613128596210505144343 81956419692894315757716515)
          ·
            refine ⟨122934629539341473636574773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81956419692894315757716515 122934629539341473636574773)
            ·
              refine ⟨11525121519313263153428885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122934629539341473636574773 11525121519313263153428885)
              ·
                refine ⟨540240071217809210316979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11525121519313263153428885 540240071217809210316979)
                ·
                  refine ⟨810360106826713815475469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540240071217809210316979 810360106826713815475469)
                  ·
                    refine ⟨303885040060017680803301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810360106826713815475469 303885040060017680803301)
                    ·
                      rfl

theorem cell22_887721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_887721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887721 prefixEnd_887721 := by exact prefixLift 887721
  have htrace : WordTrace (prefixWord ++ tailWord_887721) baseStart_887721 baseEnd_887721 := by
    simpa [prefixWord, tailWord_887721, baseEnd_887721] using wordTrace_append hprefix tailTrace_887721
  have hstable : (prefixWord ++ tailWord_887721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887721).length < 2 ^ (prefixWord ++ tailWord_887721).sum := by decide
  have hdescent : baseEnd_887721 < baseStart_887721 := by decide
  rcases family_descends (prefixWord ++ tailWord_887721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887798 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_887798 : Nat := 118140960795 + 887798 * 2 ^ 59
def prefixEnd_887798 : Nat := 4983230072969 + 3 ^ 40 * 887798 * 2
def baseEnd_887798 : Nat := 303911398733615146628065

theorem tailTrace_887798 : CollatzResearch.WordTrace tailWord_887798 prefixEnd_887798 303911398733615146628065 := by
  unfold tailWord_887798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023790827354184042007503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21587102158444629781413365 2023790827354184042007503)
  ·
    refine ⟨3035686241031276063011255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023790827354184042007503 3035686241031276063011255)
    ·
      refine ⟨4553529361546914094516883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035686241031276063011255 4553529361546914094516883)
      ·
        refine ⟨6830294042320371141775325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553529361546914094516883 6830294042320371141775325)
        ·
          refine ⟨2561360265870139178165747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6830294042320371141775325 2561360265870139178165747)
          ·
            refine ⟨3842040398805208767248621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561360265870139178165747 3842040398805208767248621)
            ·
              refine ⟨1440765149551953287718233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3842040398805208767248621 1440765149551953287718233)
              ·
                refine ⟨1080573862163964965788675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440765149551953287718233 1080573862163964965788675)
                ·
                  refine ⟨1620860793245947448683013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080573862163964965788675 1620860793245947448683013)
                  ·
                    refine ⟨303911398733615146628065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620860793245947448683013 303911398733615146628065)
                    ·
                      rfl

theorem cell22_887798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_887798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887798 prefixEnd_887798 := by exact prefixLift 887798
  have htrace : WordTrace (prefixWord ++ tailWord_887798) baseStart_887798 baseEnd_887798 := by
    simpa [prefixWord, tailWord_887798, baseEnd_887798] using wordTrace_append hprefix tailTrace_887798
  have hstable : (prefixWord ++ tailWord_887798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887798).length < 2 ^ (prefixWord ++ tailWord_887798).sum := by decide
  have hdescent : baseEnd_887798 < baseStart_887798 := by decide
  rcases family_descends (prefixWord ++ tailWord_887798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887841 : List Nat := [1, 2, 3, 2, 3, 3, 1, 7]
def baseStart_887841 : Nat := 118140960795 + 887841 * 2 ^ 59
def prefixEnd_887841 : Nat := 4983230072969 + 3 ^ 40 * 887841 * 2
def baseEnd_887841 : Nat := 33769568723597485311437

theorem tailTrace_887841 : CollatzResearch.WordTrace tailWord_887841 prefixEnd_887841 33769568723597485311437 := by
  unfold tailWord_887841
  simp only [CollatzResearch.WordTrace]
  refine ⟨32382221576511163015935377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21588147717674108677290251 32382221576511163015935377)
  ·
    refine ⟨24286666182383372261951533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32382221576511163015935377 24286666182383372261951533)
    ·
      refine ⟨9107499818393764598231825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24286666182383372261951533 9107499818393764598231825)
      ·
        refine ⟨6830624863795323448673869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9107499818393764598231825 6830624863795323448673869)
        ·
          refine ⟨2561484323923246293252701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6830624863795323448673869 2561484323923246293252701)
          ·
            refine ⟨960556621471217359969763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2561484323923246293252701 960556621471217359969763)
            ·
              refine ⟨1440834932206826039954645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960556621471217359969763 1440834932206826039954645)
              ·
                refine ⟨33769568723597485311437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1440834932206826039954645 33769568723597485311437)
                ·
                  rfl

theorem cell22_887841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 7].length) (baseStart_887841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887841 prefixEnd_887841 := by exact prefixLift 887841
  have htrace : WordTrace (prefixWord ++ tailWord_887841) baseStart_887841 baseEnd_887841 := by
    simpa [prefixWord, tailWord_887841, baseEnd_887841] using wordTrace_append hprefix tailTrace_887841
  have hstable : (prefixWord ++ tailWord_887841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887841).length < 2 ^ (prefixWord ++ tailWord_887841).sum := by decide
  have hdescent : baseEnd_887841 < baseStart_887841 := by decide
  rcases family_descends (prefixWord ++ tailWord_887841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887856 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_887856 : Nat := 118140960795 + 887856 * 2 ^ 59
def prefixEnd_887856 : Nat := 4983230072969 + 3 ^ 40 * 887856 * 2
def baseEnd_887856 : Nat := 303931253318922328677887

theorem tailTrace_887856 : CollatzResearch.WordTrace tailWord_887856 prefixEnd_887856 303931253318922328677887 := by
  unfold tailWord_887856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16191384335728410288865711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21588512447637880385154281 16191384335728410288865711)
  ·
    refine ⟨24287076503592615433298567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16191384335728410288865711 24287076503592615433298567)
    ·
      refine ⟨36430614755388923149947851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24287076503592615433298567 36430614755388923149947851)
      ·
        refine ⟨54645922133083384724921777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36430614755388923149947851 54645922133083384724921777)
        ·
          refine ⟨40984441599812538543691333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54645922133083384724921777 40984441599812538543691333)
          ·
            refine ⟨7684582799964850976942125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40984441599812538543691333 7684582799964850976942125)
            ·
              refine ⟨2881718549986819116353297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7684582799964850976942125 2881718549986819116353297)
              ·
                refine ⟨2161288912490114337264973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881718549986819116353297 2161288912490114337264973)
                ·
                  refine ⟨810483342183792876474365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2161288912490114337264973 810483342183792876474365)
                  ·
                    refine ⟨303931253318922328677887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810483342183792876474365 303931253318922328677887)
                    ·
                      rfl

theorem cell22_887856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_887856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887856 prefixEnd_887856 := by exact prefixLift 887856
  have htrace : WordTrace (prefixWord ++ tailWord_887856) baseStart_887856 baseEnd_887856 := by
    simpa [prefixWord, tailWord_887856, baseEnd_887856] using wordTrace_append hprefix tailTrace_887856
  have hstable : (prefixWord ++ tailWord_887856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887856).length < 2 ^ (prefixWord ++ tailWord_887856).sum := by decide
  have hdescent : baseEnd_887856 < baseStart_887856 := by decide
  rcases family_descends (prefixWord ++ tailWord_887856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887860 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_887860 : Nat := 118140960795 + 887860 * 2 ^ 59
def prefixEnd_887860 : Nat := 4983230072969 + 3 ^ 40 * 887860 * 2
def baseEnd_887860 : Nat := 303932622600667651577875

theorem tailTrace_887860 : CollatzResearch.WordTrace tailWord_887860 prefixEnd_887860 303932622600667651577875 := by
  unfold tailWord_887860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16191457281721164630438517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21588609708961552840584689 16191457281721164630438517)
  ·
    refine ⟨1517949120161359184103611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16191457281721164630438517 1517949120161359184103611)
    ·
      refine ⟨2276923680242038776155417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517949120161359184103611 2276923680242038776155417)
      ·
        refine ⟨1707692760181529082116563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2276923680242038776155417 1707692760181529082116563)
        ·
          refine ⟨2561539140272293623174845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707692760181529082116563 2561539140272293623174845)
          ·
            refine ⟨960577177602110108690567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2561539140272293623174845 960577177602110108690567)
            ·
              refine ⟨1440865766403165163035851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960577177602110108690567 1440865766403165163035851)
              ·
                refine ⟨2161298649604747744553777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440865766403165163035851 2161298649604747744553777)
                ·
                  refine ⟨1620973987203560808415333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161298649604747744553777 1620973987203560808415333)
                  ·
                    refine ⟨303932622600667651577875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620973987203560808415333 303932622600667651577875)
                    ·
                      rfl

theorem cell22_887860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_887860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887860 prefixEnd_887860 := by exact prefixLift 887860
  have htrace : WordTrace (prefixWord ++ tailWord_887860) baseStart_887860 baseEnd_887860 := by
    simpa [prefixWord, tailWord_887860, baseEnd_887860] using wordTrace_append hprefix tailTrace_887860
  have hstable : (prefixWord ++ tailWord_887860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887860).length < 2 ^ (prefixWord ++ tailWord_887860).sum := by decide
  have hdescent : baseEnd_887860 < baseStart_887860 := by decide
  rcases family_descends (prefixWord ++ tailWord_887860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887890 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_887890 : Nat := 118140960795 + 887890 * 2 ^ 59
def prefixEnd_887890 : Nat := 4983230072969 + 3 ^ 40 * 887890 * 2
def baseEnd_887890 : Nat := 303942892213757573327783

theorem tailTrace_887890 : CollatzResearch.WordTrace tailWord_887890 prefixEnd_887890 303942892213757573327783 := by
  unfold tailWord_887890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8096002188333411096117281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21589339168889096256312749 8096002188333411096117281)
  ·
    refine ⟨6072001641250058322087961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8096002188333411096117281 6072001641250058322087961)
    ·
      refine ⟨4554001230937543741565971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6072001641250058322087961 4554001230937543741565971)
      ·
        refine ⟨6831001846406315612348957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554001230937543741565971 6831001846406315612348957)
        ·
          refine ⟨2561625692402368354630859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6831001846406315612348957 2561625692402368354630859)
          ·
            refine ⟨3842438538603552531946289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561625692402368354630859 3842438538603552531946289)
            ·
              refine ⟨2881828903952664398959717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3842438538603552531946289 2881828903952664398959717)
              ·
                refine ⟨540342919491124574804947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2881828903952664398959717 540342919491124574804947)
                ·
                  refine ⟨810514379236686862207421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540342919491124574804947 810514379236686862207421)
                  ·
                    refine ⟨303942892213757573327783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810514379236686862207421 303942892213757573327783)
                    ·
                      rfl

theorem cell22_887890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_887890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887890 prefixEnd_887890 := by exact prefixLift 887890
  have htrace : WordTrace (prefixWord ++ tailWord_887890) baseStart_887890 baseEnd_887890 := by
    simpa [prefixWord, tailWord_887890, baseEnd_887890] using wordTrace_append hprefix tailTrace_887890
  have hstable : (prefixWord ++ tailWord_887890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887890).length < 2 ^ (prefixWord ++ tailWord_887890).sum := by decide
  have hdescent : baseEnd_887890 < baseStart_887890 := by decide
  rcases family_descends (prefixWord ++ tailWord_887890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887967 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 1, 4]
def baseStart_887967 : Nat := 118140960795 + 887967 * 2 ^ 59
def prefixEnd_887967 : Nat := 4983230072969 + 3 ^ 40 * 887967 * 2
def baseEnd_887967 : Nat := 303969250887355039152547

theorem tailTrace_887967 : CollatzResearch.WordTrace tailWord_887967 prefixEnd_887967 303969250887355039152547 := by
  unfold tailWord_887967
  simp only [CollatzResearch.WordTrace]
  refine ⟨32386817174054686535022155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21591211449369791023348103 32386817174054686535022155)
  ·
    refine ⟨48580225761082029802533233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32386817174054686535022155 48580225761082029802533233)
    ·
      refine ⟨36435169320811522351899925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48580225761082029802533233 36435169320811522351899925)
      ·
        refine ⟨1707898561913040110245309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36435169320811522351899925 1707898561913040110245309)
        ·
          refine ⟨640461960717390041341991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1707898561913040110245309 640461960717390041341991)
          ·
            refine ⟨960692941076085062012987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640461960717390041341991 960692941076085062012987)
            ·
              refine ⟨1441039411614127593019481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960692941076085062012987 1441039411614127593019481)
              ·
                refine ⟨1080779558710595694764611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441039411614127593019481 1080779558710595694764611)
                ·
                  refine ⟨1621169338065893542146917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080779558710595694764611 1621169338065893542146917)
                  ·
                    refine ⟨303969250887355039152547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621169338065893542146917 303969250887355039152547)
                    ·
                      rfl

theorem cell22_887967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_887967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_887967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_887967 prefixEnd_887967 := by exact prefixLift 887967
  have htrace : WordTrace (prefixWord ++ tailWord_887967) baseStart_887967 baseEnd_887967 := by
    simpa [prefixWord, tailWord_887967, baseEnd_887967] using wordTrace_append hprefix tailTrace_887967
  have hstable : (prefixWord ++ tailWord_887967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887967).length < 2 ^ (prefixWord ++ tailWord_887967).sum := by decide
  have hdescent : baseEnd_887967 < baseStart_887967 := by decide
  rcases family_descends (prefixWord ++ tailWord_887967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888042 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_888042 : Nat := 118140960795 + 888042 * 2 ^ 59
def prefixEnd_888042 : Nat := 4983230072969 + 3 ^ 40 * 888042 * 2
def baseEnd_888042 : Nat := 303994924920079843527317

theorem tailTrace_888042 : CollatzResearch.WordTrace tailWord_888042 prefixEnd_888042 303994924920079843527317 := by
  unfold tailWord_888042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097388162195743586000595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21593035099188649562668253 8097388162195743586000595)
  ·
    refine ⟨12146082243293615379000893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8097388162195743586000595 12146082243293615379000893)
    ·
      refine ⟨4554780841235105767125335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12146082243293615379000893 4554780841235105767125335)
      ·
        refine ⟨6832171261852658650688003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554780841235105767125335 6832171261852658650688003)
        ·
          refine ⟨10248256892778987976032005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832171261852658650688003 10248256892778987976032005)
          ·
            refine ⟨1921548167396060245506001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10248256892778987976032005 1921548167396060245506001)
            ·
              refine ⟨1441161125547045184129501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921548167396060245506001 1441161125547045184129501)
              ·
                refine ⟨540435422080141944048563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441161125547045184129501 540435422080141944048563)
                ·
                  refine ⟨810653133120212916072845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540435422080141944048563 810653133120212916072845)
                  ·
                    refine ⟨303994924920079843527317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810653133120212916072845 303994924920079843527317)
                    ·
                      rfl

theorem cell22_888042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_888042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888042 prefixEnd_888042 := by exact prefixLift 888042
  have htrace : WordTrace (prefixWord ++ tailWord_888042) baseStart_888042 baseEnd_888042 := by
    simpa [prefixWord, tailWord_888042, baseEnd_888042] using wordTrace_append hprefix tailTrace_888042
  have hstable : (prefixWord ++ tailWord_888042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888042).length < 2 ^ (prefixWord ++ tailWord_888042).sum := by decide
  have hdescent : baseEnd_888042 < baseStart_888042 := by decide
  rcases family_descends (prefixWord ++ tailWord_888042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888113 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_888113 : Nat := 118140960795 + 888113 * 2 ^ 59
def prefixEnd_888113 : Nat := 4983230072969 + 3 ^ 40 * 888113 * 2
def baseEnd_888113 : Nat := 304019229671059325002099

theorem tailTrace_888113 : CollatzResearch.WordTrace tailWord_888113 prefixEnd_888113 304019229671059325002099 := by
  unfold tailWord_888113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32392142231525753469836993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21594761487683835646557995 32392142231525753469836993)
  ·
    refine ⟨24294106673644315102377745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32392142231525753469836993 24294106673644315102377745)
    ·
      refine ⟨18220580005233236326783309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24294106673644315102377745 18220580005233236326783309)
      ·
        refine ⟨6832717501962463622543741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18220580005233236326783309 6832717501962463622543741)
        ·
          refine ⟨2562269063235923858453903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6832717501962463622543741 2562269063235923858453903)
          ·
            refine ⟨3843403594853885787680855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562269063235923858453903 3843403594853885787680855)
            ·
              refine ⟨5765105392280828681521283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843403594853885787680855 5765105392280828681521283)
              ·
                refine ⟨8647658088421243022281925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765105392280828681521283 8647658088421243022281925)
                ·
                  refine ⟨1621435891578983066677861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8647658088421243022281925 1621435891578983066677861)
                  ·
                    refine ⟨304019229671059325002099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621435891578983066677861 304019229671059325002099)
                    ·
                      rfl

theorem cell22_888113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_888113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888113 prefixEnd_888113 := by exact prefixLift 888113
  have htrace : WordTrace (prefixWord ++ tailWord_888113) baseStart_888113 baseEnd_888113 := by
    simpa [prefixWord, tailWord_888113, baseEnd_888113] using wordTrace_append hprefix tailTrace_888113
  have hstable : (prefixWord ++ tailWord_888113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888113).length < 2 ^ (prefixWord ++ tailWord_888113).sum := by decide
  have hdescent : baseEnd_888113 < baseStart_888113 := by decide
  rcases family_descends (prefixWord ++ tailWord_888113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888117 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 4]
def baseStart_888117 : Nat := 118140960795 + 888117 * 2 ^ 59
def prefixEnd_888117 : Nat := 4983230072969 + 3 ^ 40 * 888117 * 2
def baseEnd_888117 : Nat := 101340199650934882634029

theorem tailTrace_888117 : CollatzResearch.WordTrace tailWord_888117 prefixEnd_888117 101340199650934882634029 := by
  unfold tailWord_888117
  simp only [CollatzResearch.WordTrace]
  refine ⟨32392288123511262152982605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21594858749007508101988403 32392288123511262152982605)
  ·
    refine ⟨12147108046316723307368477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32392288123511262152982605 12147108046316723307368477)
    ·
      refine ⟨4555165517368771240263179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12147108046316723307368477 4555165517368771240263179)
      ·
        refine ⟨6832748276053156860394769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555165517368771240263179 6832748276053156860394769)
        ·
          refine ⟨5124561207039867645296077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6832748276053156860394769 5124561207039867645296077)
          ·
            refine ⟨1921710452639950366986029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5124561207039867645296077 1921710452639950366986029)
            ·
              refine ⟨720641419739981387619761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1921710452639950366986029 720641419739981387619761)
              ·
                refine ⟨540481064804986040714821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720641419739981387619761 540481064804986040714821)
                ·
                  refine ⟨101340199650934882634029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540481064804986040714821 101340199650934882634029)
                  ·
                    rfl

theorem cell22_888117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_888117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888117 prefixEnd_888117 := by exact prefixLift 888117
  have htrace : WordTrace (prefixWord ++ tailWord_888117) baseStart_888117 baseEnd_888117 := by
    simpa [prefixWord, tailWord_888117, baseEnd_888117] using wordTrace_append hprefix tailTrace_888117
  have hstable : (prefixWord ++ tailWord_888117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888117).length < 2 ^ (prefixWord ++ tailWord_888117).sum := by decide
  have hdescent : baseEnd_888117 < baseStart_888117 := by decide
  rcases family_descends (prefixWord ++ tailWord_888117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888188 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_888188 : Nat := 118140960795 + 888188 * 2 ^ 59
def prefixEnd_888188 : Nat := 4983230072969 + 3 ^ 40 * 888188 * 2
def baseEnd_888188 : Nat := 304044903703784129376869

theorem tailTrace_888188 : CollatzResearch.WordTrace tailWord_888188 prefixEnd_888188 304044903703784129376869 := by
  unfold tailWord_888188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16197438853127020639408609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21596585137502694185878145 16197438853127020639408609)
  ·
    refine ⟨12148079139845265479556457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16197438853127020639408609 12148079139845265479556457)
    ·
      refine ⟨9111059354883949109667343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12148079139845265479556457 9111059354883949109667343)
      ·
        refine ⟨13666589032325923664501015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9111059354883949109667343 13666589032325923664501015)
        ·
          refine ⟨20499883548488885496751523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666589032325923664501015 20499883548488885496751523)
          ·
            refine ⟨30749825322733328245127285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20499883548488885496751523 30749825322733328245127285)
            ·
              refine ⟨2882796124006249522980683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30749825322733328245127285 2882796124006249522980683)
              ·
                refine ⟨4324194186009374284471025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882796124006249522980683 4324194186009374284471025)
                ·
                  refine ⟨3243145639507030713353269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324194186009374284471025 3243145639507030713353269)
                  ·
                    refine ⟨304044903703784129376869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3243145639507030713353269 304044903703784129376869)
                    ·
                      rfl

theorem cell22_888188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_888188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888188 prefixEnd_888188 := by exact prefixLift 888188
  have htrace : WordTrace (prefixWord ++ tailWord_888188) baseStart_888188 baseEnd_888188 := by
    simpa [prefixWord, tailWord_888188, baseEnd_888188] using wordTrace_append hprefix tailTrace_888188
  have hstable : (prefixWord ++ tailWord_888188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888188).length < 2 ^ (prefixWord ++ tailWord_888188).sum := by decide
  have hdescent : baseEnd_888188 < baseStart_888188 := by decide
  rcases family_descends (prefixWord ++ tailWord_888188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888194 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_888194 : Nat := 118140960795 + 888194 * 2 ^ 59
def prefixEnd_888194 : Nat := 4983230072969 + 3 ^ 40 * 888194 * 2
def baseEnd_888194 : Nat := 304046957626402113726851

theorem tailTrace_888194 : CollatzResearch.WordTrace tailWord_888194 prefixEnd_888194 304046957626402113726851 := by
  unfold tailWord_888194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098774136058076075883909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21596731029488202869023757 8098774136058076075883909)
  ·
    refine ⟨1518520150510889264228233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8098774136058076075883909 1518520150510889264228233)
    ·
      refine ⟨1138890112883166948171175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518520150510889264228233 1138890112883166948171175)
      ·
        refine ⟨1708335169324750422256763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138890112883166948171175 1708335169324750422256763)
        ·
          refine ⟨2562502753987125633385145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708335169324750422256763 2562502753987125633385145)
          ·
            refine ⟨1921877065490344225038859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562502753987125633385145 1921877065490344225038859)
            ·
              refine ⟨2882815598235516337558289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921877065490344225038859 2882815598235516337558289)
              ·
                refine ⟨2162111698676637253168717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882815598235516337558289 2162111698676637253168717)
                ·
                  refine ⟨810791887003738969938269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2162111698676637253168717 810791887003738969938269)
                  ·
                    refine ⟨304046957626402113726851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 810791887003738969938269 304046957626402113726851)
                    ·
                      rfl

theorem cell22_888194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_888194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888194 prefixEnd_888194 := by exact prefixLift 888194
  have htrace : WordTrace (prefixWord ++ tailWord_888194) baseStart_888194 baseEnd_888194 := by
    simpa [prefixWord, tailWord_888194, baseEnd_888194] using wordTrace_append hprefix tailTrace_888194
  have hstable : (prefixWord ++ tailWord_888194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888194).length < 2 ^ (prefixWord ++ tailWord_888194).sum := by decide
  have hdescent : baseEnd_888194 < baseStart_888194 := by decide
  rcases family_descends (prefixWord ++ tailWord_888194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888203 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_888203 : Nat := 118140960795 + 888203 * 2 ^ 59
def prefixEnd_888203 : Nat := 4983230072969 + 3 ^ 40 * 888203 * 2
def baseEnd_888203 : Nat := 304050038510329090251823

theorem tailTrace_888203 : CollatzResearch.WordTrace tailWord_888203 prefixEnd_888203 304050038510329090251823 := by
  unfold tailWord_888203
  simp only [CollatzResearch.WordTrace]
  refine ⟨32395424801199698840613263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21596949867466465893742175 32395424801199698840613263)
  ·
    refine ⟨48593137201799548260919895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32395424801199698840613263 48593137201799548260919895)
    ·
      refine ⟨72889705802699322391379843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48593137201799548260919895 72889705802699322391379843)
      ·
        refine ⟨109334558704048983587069765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72889705802699322391379843 109334558704048983587069765)
        ·
          refine ⟨20500229757009184422575581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109334558704048983587069765 20500229757009184422575581)
          ·
            refine ⟨7687586158878444158465843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20500229757009184422575581 7687586158878444158465843)
            ·
              refine ⟨11531379238317666237698765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687586158878444158465843 11531379238317666237698765)
              ·
                refine ⟨4324267214369124839137037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11531379238317666237698765 4324267214369124839137037)
                ·
                  refine ⟨1621600205388421814676389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4324267214369124839137037 1621600205388421814676389)
                  ·
                    refine ⟨304050038510329090251823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621600205388421814676389 304050038510329090251823)
                    ·
                      rfl

theorem cell22_888203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_888203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888203 prefixEnd_888203 := by exact prefixLift 888203
  have htrace : WordTrace (prefixWord ++ tailWord_888203) baseStart_888203 baseEnd_888203 := by
    simpa [prefixWord, tailWord_888203, baseEnd_888203] using wordTrace_append hprefix tailTrace_888203
  have hstable : (prefixWord ++ tailWord_888203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888203).length < 2 ^ (prefixWord ++ tailWord_888203).sum := by decide
  have hdescent : baseEnd_888203 < baseStart_888203 := by decide
  rcases family_descends (prefixWord ++ tailWord_888203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888218 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_888218 : Nat := 118140960795 + 888218 * 2 ^ 59
def prefixEnd_888218 : Nat := 4983230072969 + 3 ^ 40 * 888218 * 2
def baseEnd_888218 : Nat := 101351724438958017042259

theorem tailTrace_888218 : CollatzResearch.WordTrace tailWord_888218 prefixEnd_888218 101351724438958017042259 := by
  unfold tailWord_888218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098992974036339100602327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21597314597430237601606205 8098992974036339100602327)
  ·
    refine ⟨12148489461054508650903491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098992974036339100602327 12148489461054508650903491)
    ·
      refine ⟨18222734191581762976355237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12148489461054508650903491 18222734191581762976355237)
      ·
        refine ⟨3416762660921580558066607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18222734191581762976355237 3416762660921580558066607)
        ·
          refine ⟨5125143991382370837099911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416762660921580558066607 5125143991382370837099911)
          ·
            refine ⟨7687715987073556255649867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125143991382370837099911 7687715987073556255649867)
            ·
              refine ⟨11531573980610334383474801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687715987073556255649867 11531573980610334383474801)
              ·
                refine ⟨8648680485457750787606101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531573980610334383474801 8648680485457750787606101)
                ·
                  refine ⟨101351724438958017042259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8648680485457750787606101 101351724438958017042259)
                  ·
                    rfl

theorem cell22_888218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_888218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888218 prefixEnd_888218 := by exact prefixLift 888218
  have htrace : WordTrace (prefixWord ++ tailWord_888218) baseStart_888218 baseEnd_888218 := by
    simpa [prefixWord, tailWord_888218, baseEnd_888218] using wordTrace_append hprefix tailTrace_888218
  have hstable : (prefixWord ++ tailWord_888218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888218).length < 2 ^ (prefixWord ++ tailWord_888218).sum := by decide
  have hdescent : baseEnd_888218 < baseStart_888218 := by decide
  rcases family_descends (prefixWord ++ tailWord_888218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888248 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_888248 : Nat := 118140960795 + 888248 * 2 ^ 59
def prefixEnd_888248 : Nat := 4983230072969 + 3 ^ 40 * 888248 * 2
def baseEnd_888248 : Nat := 304065442929963972876685

theorem tailTrace_888248 : CollatzResearch.WordTrace tailWord_888248 prefixEnd_888248 304065442929963972876685 := by
  unfold tailWord_888248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198533043018335763000699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21598044057357781017334265 16198533043018335763000699)
  ·
    refine ⟨24297799564527503644501049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16198533043018335763000699 24297799564527503644501049)
    ·
      refine ⟨18223349673395627733375787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24297799564527503644501049 18223349673395627733375787)
      ·
        refine ⟨27335024510093441600063681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223349673395627733375787 27335024510093441600063681)
        ·
          refine ⟨20501268382570081200047761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27335024510093441600063681 20501268382570081200047761)
          ·
            refine ⟨15375951286927560900035821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20501268382570081200047761 15375951286927560900035821)
            ·
              refine ⟨5765981732597835337513433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15375951286927560900035821 5765981732597835337513433)
              ·
                refine ⟨4324486299448376503135075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5765981732597835337513433 4324486299448376503135075)
                ·
                  refine ⟨6486729449172564754702613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324486299448376503135075 6486729449172564754702613)
                  ·
                    refine ⟨304065442929963972876685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6486729449172564754702613 304065442929963972876685)
                    ·
                      rfl

theorem cell22_888248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_888248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888248 prefixEnd_888248 := by exact prefixLift 888248
  have htrace : WordTrace (prefixWord ++ tailWord_888248) baseStart_888248 baseEnd_888248 := by
    simpa [prefixWord, tailWord_888248, baseEnd_888248] using wordTrace_append hprefix tailTrace_888248
  have hstable : (prefixWord ++ tailWord_888248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888248).length < 2 ^ (prefixWord ++ tailWord_888248).sum := by decide
  have hdescent : baseEnd_888248 < baseStart_888248 := by decide
  rcases family_descends (prefixWord ++ tailWord_888248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
