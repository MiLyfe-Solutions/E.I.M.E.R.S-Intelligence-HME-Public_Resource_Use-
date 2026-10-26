import V185TrunkScan23Chunk0229

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1359688 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_1359688 : Nat := 118140960795 + 1359688 * 2 ^ 59
def prefixEnd_1359688 : Nat := 4983230072969 + 3 ^ 40 * 1359688 * 2
def baseEnd_1359688 : Nat := 698173484150581448146915

theorem tailTrace_1359688 : CollatzResearch.WordTrace tailWord_1359688 prefixEnd_1359688 698173484150581448146915 := by
  unfold tailWord_1359688
  simp only [CollatzResearch.WordTrace]
  refine ⟨24795947749045033533915859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33061263665393378045221145 24795947749045033533915859)
  ·
    refine ⟨37193921623567550300873789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24795947749045033533915859 37193921623567550300873789)
    ·
      refine ⟨13947720608837831362827671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37193921623567550300873789 13947720608837831362827671)
      ·
        refine ⟨20921580913256747044241507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13947720608837831362827671 20921580913256747044241507)
        ·
          refine ⟨31382371369885120566362261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20921580913256747044241507 31382371369885120566362261)
          ·
            refine ⟨1471048657963365026548231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31382371369885120566362261 1471048657963365026548231)
            ·
              refine ⟨2206572986945047539822347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471048657963365026548231 2206572986945047539822347)
              ·
                refine ⟨3309859480417571309733521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206572986945047539822347 3309859480417571309733521)
                ·
                  refine ⟨2482394610313178482300141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309859480417571309733521 2482394610313178482300141)
                  ·
                    refine ⟨930897978867441930862553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482394610313178482300141 930897978867441930862553)
                    ·
                      refine ⟨698173484150581448146915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930897978867441930862553 698173484150581448146915)
                      ·
                        rfl

theorem cell23_1359688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_1359688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359688 prefixEnd_1359688 := by exact prefixLift 1359688
  have htrace : WordTrace (prefixWord ++ tailWord_1359688) baseStart_1359688 baseEnd_1359688 := by
    simpa [prefixWord, tailWord_1359688, baseEnd_1359688] using wordTrace_append hprefix tailTrace_1359688
  have hstable : (prefixWord ++ tailWord_1359688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359688).length < 2 ^ (prefixWord ++ tailWord_1359688).sum := by decide
  have hdescent : baseEnd_1359688 < baseStart_1359688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359698 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1359698 : Nat := 118140960795 + 1359698 * 2 ^ 59
def prefixEnd_1359698 : Nat := 4983230072969 + 3 ^ 40 * 1359698 * 2
def baseEnd_1359698 : Nat := 232726206319042136340623

theorem tailTrace_1359698 : CollatzResearch.WordTrace tailWord_1359698 prefixEnd_1359698 232726206319042136340623 := by
  unfold tailWord_1359698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398065057013459693923937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33061506818702559183797165 12398065057013459693923937)
  ·
    refine ⟨9298548792760094770442953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12398065057013459693923937 9298548792760094770442953)
    ·
      refine ⟨6973911594570071077832215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9298548792760094770442953 6973911594570071077832215)
      ·
        refine ⟨10460867391855106616748323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6973911594570071077832215 10460867391855106616748323)
        ·
          refine ⟨15691301087782659925122485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10460867391855106616748323 15691301087782659925122485)
          ·
            refine ⟨1471059476979624367980233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15691301087782659925122485 1471059476979624367980233)
            ·
              refine ⟨1103294607734718275985175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471059476979624367980233 1103294607734718275985175)
              ·
                refine ⟨1654941911602077413977763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103294607734718275985175 1654941911602077413977763)
                ·
                  refine ⟨2482412867403116120966645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654941911602077413977763 2482412867403116120966645)
                  ·
                    refine ⟨232726206319042136340623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2482412867403116120966645 232726206319042136340623)
                    ·
                      rfl

theorem cell23_1359698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1359698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359698 prefixEnd_1359698 := by exact prefixLift 1359698
  have htrace : WordTrace (prefixWord ++ tailWord_1359698) baseStart_1359698 baseEnd_1359698 := by
    simpa [prefixWord, tailWord_1359698, baseEnd_1359698] using wordTrace_append hprefix tailTrace_1359698
  have hstable : (prefixWord ++ tailWord_1359698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359698).length < 2 ^ (prefixWord ++ tailWord_1359698).sum := by decide
  have hdescent : baseEnd_1359698 < baseStart_1359698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359701 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1359701 : Nat := 118140960795 + 1359701 * 2 ^ 59
def prefixEnd_1359701 : Nat := 4983230072969 + 3 ^ 40 * 1359701 * 2
def baseEnd_1359701 : Nat := 698180159399089897284355

theorem tailTrace_1359701 : CollatzResearch.WordTrace tailWord_1359701 prefixEnd_1359701 698180159399089897284355 := by
  unfold tailWord_1359701
  simp only [CollatzResearch.WordTrace]
  refine ⟨49592369647042970288054957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33061579764695313525369971 49592369647042970288054957)
  ·
    refine ⟨18597138617641113858020609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49592369647042970288054957 18597138617641113858020609)
    ·
      refine ⟨13947853963230835393515457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18597138617641113858020609 13947853963230835393515457)
      ·
        refine ⟨10460890472423126545136593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13947853963230835393515457 10460890472423126545136593)
        ·
          refine ⟨7845667854317344908852445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10460890472423126545136593 7845667854317344908852445)
          ·
            refine ⟨2942125445369004340819667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7845667854317344908852445 2942125445369004340819667)
            ·
              refine ⟨4413188168053506511229501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942125445369004340819667 4413188168053506511229501)
              ·
                refine ⟨1654945563020064941711063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4413188168053506511229501 1654945563020064941711063)
                ·
                  refine ⟨2482418344530097412566595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654945563020064941711063 2482418344530097412566595)
                  ·
                    refine ⟨3723627516795146118849893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482418344530097412566595 3723627516795146118849893)
                    ·
                      refine ⟨698180159399089897284355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3723627516795146118849893 698180159399089897284355)
                      ·
                        rfl

theorem cell23_1359701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1359701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359701 prefixEnd_1359701 := by exact prefixLift 1359701
  have htrace : WordTrace (prefixWord ++ tailWord_1359701) baseStart_1359701 baseEnd_1359701 := by
    simpa [prefixWord, tailWord_1359701, baseEnd_1359701] using wordTrace_append hprefix tailTrace_1359701
  have hstable : (prefixWord ++ tailWord_1359701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359701).length < 2 ^ (prefixWord ++ tailWord_1359701).sum := by decide
  have hdescent : baseEnd_1359701 < baseStart_1359701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359711 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 2, 4]
def baseStart_1359711 : Nat := 118140960795 + 1359711 * 2 ^ 59
def prefixEnd_1359711 : Nat := 4983230072969 + 3 ^ 40 * 1359711 * 2
def baseEnd_1359711 : Nat := 232728431401878286053103

theorem tailTrace_1359711 : CollatzResearch.WordTrace tailWord_1359711 prefixEnd_1359711 232728431401878286053103 := by
  unfold tailWord_1359711
  simp only [CollatzResearch.WordTrace]
  refine ⟨49592734377006741995918987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33061822918004494663945991 49592734377006741995918987)
  ·
    refine ⟨74389101565510112993878481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49592734377006741995918987 74389101565510112993878481)
    ·
      refine ⟨55791826174132584745408861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74389101565510112993878481 55791826174132584745408861)
      ·
        refine ⟨20921934815299719279528323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55791826174132584745408861 20921934815299719279528323)
        ·
          refine ⟨31382902222949578919292485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20921934815299719279528323 31382902222949578919292485)
          ·
            refine ⟨5884294166803046047367341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31382902222949578919292485 5884294166803046047367341)
            ·
              refine ⟨2206610312551142267762753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5884294166803046047367341 2206610312551142267762753)
              ·
                refine ⟨1654957734413356700822065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206610312551142267762753 1654957734413356700822065)
                ·
                  refine ⟨1241218300810017525616549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654957734413356700822065 1241218300810017525616549)
                  ·
                    refine ⟨232728431401878286053103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241218300810017525616549 232728431401878286053103)
                    ·
                      rfl

theorem cell23_1359711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_1359711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359711 prefixEnd_1359711 := by exact prefixLift 1359711
  have htrace : WordTrace (prefixWord ++ tailWord_1359711) baseStart_1359711 baseEnd_1359711 := by
    simpa [prefixWord, tailWord_1359711, baseEnd_1359711] using wordTrace_append hprefix tailTrace_1359711
  have hstable : (prefixWord ++ tailWord_1359711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359711).length < 2 ^ (prefixWord ++ tailWord_1359711).sum := by decide
  have hdescent : baseEnd_1359711 < baseStart_1359711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359717 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1359717 : Nat := 118140960795 + 1359717 * 2 ^ 59
def prefixEnd_1359717 : Nat := 4983230072969 + 3 ^ 40 * 1359717 * 2
def baseEnd_1359717 : Nat := 698188375089561834684281

theorem tailTrace_1359717 : CollatzResearch.WordTrace tailWord_1359717 prefixEnd_1359717 698188375089561834684281 := by
  unfold tailWord_1359717
  simp only [CollatzResearch.WordTrace]
  refine ⟨49592953214985005020637405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33061968809990003347091603 49592953214985005020637405)
  ·
    refine ⟨18597357455619376882739027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49592953214985005020637405 18597357455619376882739027)
    ·
      refine ⟨27896036183429065324108541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18597357455619376882739027 27896036183429065324108541)
      ·
        refine ⟨10461013568785899496540703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27896036183429065324108541 10461013568785899496540703)
        ·
          refine ⟨15691520353178849244811055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10461013568785899496540703 15691520353178849244811055)
          ·
            refine ⟨23537280529768273867216583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15691520353178849244811055 23537280529768273867216583)
            ·
              refine ⟨35305920794652410800824875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23537280529768273867216583 35305920794652410800824875)
              ·
                refine ⟨52958881191978616201237313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35305920794652410800824875 52958881191978616201237313)
                ·
                  refine ⟨39719160893983962150927985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52958881191978616201237313 39719160893983962150927985)
                  ·
                    refine ⟨29789370670487971613195989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39719160893983962150927985 29789370670487971613195989)
                    ·
                      refine ⟨698188375089561834684281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29789370670487971613195989 698188375089561834684281)
                      ·
                        rfl

theorem cell23_1359717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1359717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359717 prefixEnd_1359717 := by exact prefixLift 1359717
  have htrace : WordTrace (prefixWord ++ tailWord_1359717) baseStart_1359717 baseEnd_1359717 := by
    simpa [prefixWord, tailWord_1359717, baseEnd_1359717] using wordTrace_append hprefix tailTrace_1359717
  have hstable : (prefixWord ++ tailWord_1359717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359717).length < 2 ^ (prefixWord ++ tailWord_1359717).sum := by decide
  have hdescent : baseEnd_1359717 < baseStart_1359717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359758 : List Nat := [4, 1, 1, 5, 2, 1, 9]
def baseStart_1359758 : Nat := 118140960795 + 1359758 * 2 ^ 59
def prefixEnd_1359758 : Nat := 4983230072969 + 3 ^ 40 * 1359758 * 2
def baseEnd_1359758 : Nat := 8619869478967854003353

theorem tailTrace_1359758 : CollatzResearch.WordTrace tailWord_1359758 prefixEnd_1359758 8619869478967854003353 := by
  unfold tailWord_1359758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6199306075979558627859991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33062965738557646015253285 6199306075979558627859991)
  ·
    refine ⟨9298959113969337941789987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6199306075979558627859991 9298959113969337941789987)
    ·
      refine ⟨13948438670954006912684981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9298959113969337941789987 13948438670954006912684981)
      ·
        refine ⟨1307666125401938148064217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13948438670954006912684981 1307666125401938148064217)
        ·
          refine ⟨980749594051453611048163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307666125401938148064217 980749594051453611048163)
          ·
            refine ⟨1471124391077180416572245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980749594051453611048163 1471124391077180416572245)
            ·
              refine ⟨8619869478967854003353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1471124391077180416572245 8619869478967854003353)
              ·
                rfl

theorem cell23_1359758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 9].length) (baseStart_1359758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359758 prefixEnd_1359758 := by exact prefixLift 1359758
  have htrace : WordTrace (prefixWord ++ tailWord_1359758) baseStart_1359758 baseEnd_1359758 := by
    simpa [prefixWord, tailWord_1359758, baseEnd_1359758] using wordTrace_append hprefix tailTrace_1359758
  have hstable : (prefixWord ++ tailWord_1359758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359758).length < 2 ^ (prefixWord ++ tailWord_1359758).sum := by decide
  have hdescent : baseEnd_1359758 < baseStart_1359758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359791 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 1, 4, 2]
def baseStart_1359791 : Nat := 118140960795 + 1359791 * 2 ^ 59
def prefixEnd_1359791 : Nat := 4983230072969 + 3 ^ 40 * 1359791 * 2
def baseEnd_1359791 : Nat := 698226372657994545158941

theorem tailTrace_1359791 : CollatzResearch.WordTrace tailWord_1359791 prefixEnd_1359791 698226372657994545158941 := by
  unfold tailWord_1359791
  simp only [CollatzResearch.WordTrace]
  refine ⟨49595652216716915658831227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33063768144477943772554151 49595652216716915658831227)
  ·
    refine ⟨74393478325075373488246841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49595652216716915658831227 74393478325075373488246841)
    ·
      refine ⟨55795108743806530116185131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74393478325075373488246841 55795108743806530116185131)
      ·
        refine ⟨83692663115709795174277697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55795108743806530116185131 83692663115709795174277697)
        ·
          refine ⟨62769497336782346380708273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83692663115709795174277697 62769497336782346380708273)
          ·
            refine ⟨47077123002586759785531205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62769497336782346380708273 47077123002586759785531205)
            ·
              refine ⟨8826960562985017459787101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47077123002586759785531205 8826960562985017459787101)
              ·
                refine ⟨3310110211119381547420163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8826960562985017459787101 3310110211119381547420163)
                ·
                  refine ⟨4965165316679072321130245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310110211119381547420163 4965165316679072321130245)
                  ·
                    refine ⟨930968496877326060211921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965165316679072321130245 930968496877326060211921)
                    ·
                      refine ⟨698226372657994545158941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 930968496877326060211921 698226372657994545158941)
                      ·
                        rfl

theorem cell23_1359791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4, 2].length) (baseStart_1359791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359791 prefixEnd_1359791 := by exact prefixLift 1359791
  have htrace : WordTrace (prefixWord ++ tailWord_1359791) baseStart_1359791 baseEnd_1359791 := by
    simpa [prefixWord, tailWord_1359791, baseEnd_1359791] using wordTrace_append hprefix tailTrace_1359791
  have hstable : (prefixWord ++ tailWord_1359791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359791).length < 2 ^ (prefixWord ++ tailWord_1359791).sum := by decide
  have hdescent : baseEnd_1359791 < baseStart_1359791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359831 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 5]
def baseStart_1359831 : Nat := 118140960795 + 1359831 * 2 ^ 59
def prefixEnd_1359831 : Nat := 4983230072969 + 3 ^ 40 * 1359831 * 2
def baseEnd_1359831 : Nat := 77582990209352709850973

theorem tailTrace_1359831 : CollatzResearch.WordTrace tailWord_1359831 prefixEnd_1359831 77582990209352709850973 := by
  unfold tailWord_1359831
  simp only [CollatzResearch.WordTrace]
  refine ⟨49597111136572002490287347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33064740757714668326858231 49597111136572002490287347)
  ·
    refine ⟨74395666704858003735431021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49597111136572002490287347 74395666704858003735431021)
    ·
      refine ⟨27898375014321751400786633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74395666704858003735431021 27898375014321751400786633)
      ·
        refine ⟨20923781260741313550589975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27898375014321751400786633 20923781260741313550589975)
        ·
          refine ⟨31385671891111970325884963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20923781260741313550589975 31385671891111970325884963)
          ·
            refine ⟨47078507836667955488827445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31385671891111970325884963 47078507836667955488827445)
            ·
              refine ⟨4413610109687620827077573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47078507836667955488827445 4413610109687620827077573)
              ·
                refine ⟨827551895566428905077045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4413610109687620827077573 827551895566428905077045)
                ·
                  refine ⟨77582990209352709850973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 827551895566428905077045 77582990209352709850973)
                  ·
                    rfl

theorem cell23_1359831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 5].length) (baseStart_1359831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359831 prefixEnd_1359831 := by exact prefixLift 1359831
  have htrace : WordTrace (prefixWord ++ tailWord_1359831) baseStart_1359831 baseEnd_1359831 := by
    simpa [prefixWord, tailWord_1359831, baseEnd_1359831] using wordTrace_append hprefix tailTrace_1359831
  have hstable : (prefixWord ++ tailWord_1359831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359831).length < 2 ^ (prefixWord ++ tailWord_1359831).sum := by decide
  have hdescent : baseEnd_1359831 < baseStart_1359831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359842 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1359842 : Nat := 118140960795 + 1359842 * 2 ^ 59
def prefixEnd_1359842 : Nat := 4983230072969 + 3 ^ 40 * 1359842 * 2
def baseEnd_1359842 : Nat := 698252560171373845621207

theorem tailTrace_1359842 : CollatzResearch.WordTrace tailWord_1359842 prefixEnd_1359842 698252560171373845621207 := by
  unfold tailWord_1359842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12399378084883037842234445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33065008226354767579291853 12399378084883037842234445)
  ·
    refine ⟨4649766781831139190837917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12399378084883037842234445 4649766781831139190837917)
    ·
      refine ⟨1743662543186677196564219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4649766781831139190837917 1743662543186677196564219)
      ·
        refine ⟨2615493814780015794846329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743662543186677196564219 2615493814780015794846329)
        ·
          refine ⟨1961620361085011846134747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615493814780015794846329 1961620361085011846134747)
          ·
            refine ⟨2942430541627517769202121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961620361085011846134747 2942430541627517769202121)
            ·
              refine ⟨2206822906220638326901591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942430541627517769202121 2206822906220638326901591)
              ·
                refine ⟨3310234359330957490352387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206822906220638326901591 3310234359330957490352387)
                ·
                  refine ⟨4965351538996436235528581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310234359330957490352387 4965351538996436235528581)
                  ·
                    refine ⟨931003413561831794161609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965351538996436235528581 931003413561831794161609)
                    ·
                      refine ⟨698252560171373845621207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931003413561831794161609 698252560171373845621207)
                      ·
                        rfl

theorem cell23_1359842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1359842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359842 prefixEnd_1359842 := by exact prefixLift 1359842
  have htrace : WordTrace (prefixWord ++ tailWord_1359842) baseStart_1359842 baseEnd_1359842 := by
    simpa [prefixWord, tailWord_1359842, baseEnd_1359842] using wordTrace_append hprefix tailTrace_1359842
  have hstable : (prefixWord ++ tailWord_1359842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359842).length < 2 ^ (prefixWord ++ tailWord_1359842).sum := by decide
  have hdescent : baseEnd_1359842 < baseStart_1359842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359844 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1359844 : Nat := 118140960795 + 1359844 * 2 ^ 59
def prefixEnd_1359844 : Nat := 4983230072969 + 3 ^ 40 * 1359844 * 2
def baseEnd_1359844 : Nat := 232751195710894279265399

theorem tailTrace_1359844 : CollatzResearch.WordTrace tailWord_1359844 prefixEnd_1359844 232751195710894279265399 := by
  unfold tailWord_1359844
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798792642762452855255293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33065056857016603807007057 24798792642762452855255293)
  ·
    refine ⟨9299547241035919820720735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24798792642762452855255293 9299547241035919820720735)
    ·
      refine ⟨13949320861553879731081103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9299547241035919820720735 13949320861553879731081103)
      ·
        refine ⟨20923981292330819596621655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13949320861553879731081103 20923981292330819596621655)
        ·
          refine ⟨31385971938496229394932483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20923981292330819596621655 31385971938496229394932483)
          ·
            refine ⟨47078957907744344092398725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31385971938496229394932483 47078957907744344092398725)
            ·
              refine ⟨8827304607702064517324761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47078957907744344092398725 8827304607702064517324761)
              ·
                refine ⟨6620478455776548387993571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8827304607702064517324761 6620478455776548387993571)
                ·
                  refine ⟨9930717683664822581990357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620478455776548387993571 9930717683664822581990357)
                  ·
                    refine ⟨232751195710894279265399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9930717683664822581990357 232751195710894279265399)
                    ·
                      rfl

theorem cell23_1359844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1359844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359844 prefixEnd_1359844 := by exact prefixLift 1359844
  have htrace : WordTrace (prefixWord ++ tailWord_1359844) baseStart_1359844 baseEnd_1359844 := by
    simpa [prefixWord, tailWord_1359844, baseEnd_1359844] using wordTrace_append hprefix tailTrace_1359844
  have hstable : (prefixWord ++ tailWord_1359844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359844).length < 2 ^ (prefixWord ++ tailWord_1359844).sum := by decide
  have hdescent : baseEnd_1359844 < baseStart_1359844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359876 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1359876 : Nat := 118140960795 + 1359876 * 2 ^ 59
def prefixEnd_1359876 : Nat := 4983230072969 + 3 ^ 40 * 1359876 * 2
def baseEnd_1359876 : Nat := 698270018513626712596051

theorem tailTrace_1359876 : CollatzResearch.WordTrace tailWord_1359876 prefixEnd_1359876 698270018513626712596051 := by
  unfold tailWord_1359876
  simp only [CollatzResearch.WordTrace]
  refine ⟨24799376210704487587837741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33065834947605983450450321 24799376210704487587837741)
  ·
    refine ⟨9299766079014182845439153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24799376210704487587837741 9299766079014182845439153)
    ·
      refine ⟨6974824559260637134079365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9299766079014182845439153 6974824559260637134079365)
      ·
        refine ⟨1307779604861369462639881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6974824559260637134079365 1307779604861369462639881)
        ·
          refine ⟨980834703646027096979911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307779604861369462639881 980834703646027096979911)
          ·
            refine ⟨1471252055469040645469867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980834703646027096979911 1471252055469040645469867)
            ·
              refine ⟨2206878083203560968204801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471252055469040645469867 2206878083203560968204801)
              ·
                refine ⟨1655158562402670726153601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206878083203560968204801 1655158562402670726153601)
                ·
                  refine ⟨1241368921802003044615201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1655158562402670726153601 1241368921802003044615201)
                  ·
                    refine ⟨931026691351502283461401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1241368921802003044615201 931026691351502283461401)
                    ·
                      refine ⟨698270018513626712596051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931026691351502283461401 698270018513626712596051)
                      ·
                        rfl

theorem cell23_1359876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1359876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359876 prefixEnd_1359876 := by exact prefixLift 1359876
  have htrace : WordTrace (prefixWord ++ tailWord_1359876) baseStart_1359876 baseEnd_1359876 := by
    simpa [prefixWord, tailWord_1359876, baseEnd_1359876] using wordTrace_append hprefix tailTrace_1359876
  have hstable : (prefixWord ++ tailWord_1359876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359876).length < 2 ^ (prefixWord ++ tailWord_1359876).sum := by decide
  have hdescent : baseEnd_1359876 < baseStart_1359876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359891 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 3, 4]
def baseStart_1359891 : Nat := 118140960795 + 1359891 * 2 ^ 59
def prefixEnd_1359891 : Nat := 4983230072969 + 3 ^ 40 * 1359891 * 2
def baseEnd_1359891 : Nat := 232759240241148051302827

theorem tailTrace_1359891 : CollatzResearch.WordTrace tailWord_1359891 prefixEnd_1359891 232759240241148051302827 := by
  unfold tailWord_1359891
  simp only [CollatzResearch.WordTrace]
  refine ⟨49599299516354632737471527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33066199677569755158314351 49599299516354632737471527)
  ·
    refine ⟨74398949274531949106207291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49599299516354632737471527 74398949274531949106207291)
    ·
      refine ⟨111598423911797923659310937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74398949274531949106207291 111598423911797923659310937)
      ·
        refine ⟨83698817933848442744483203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111598423911797923659310937 83698817933848442744483203)
        ·
          refine ⟨125548226900772664116724805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83698817933848442744483203 125548226900772664116724805)
          ·
            refine ⟨23540292543894874521885901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125548226900772664116724805 23540292543894874521885901)
            ·
              refine ⟨8827609703960577945707213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23540292543894874521885901 8827609703960577945707213)
              ·
                refine ⟨3310353638985216729640205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8827609703960577945707213 3310353638985216729640205)
                ·
                  refine ⟨1241382614619456273615077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3310353638985216729640205 1241382614619456273615077)
                  ·
                    refine ⟨232759240241148051302827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241382614619456273615077 232759240241148051302827)
                    ·
                      rfl

theorem cell23_1359891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 4].length) (baseStart_1359891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359891 prefixEnd_1359891 := by exact prefixLift 1359891
  have htrace : WordTrace (prefixWord ++ tailWord_1359891) baseStart_1359891 baseEnd_1359891 := by
    simpa [prefixWord, tailWord_1359891, baseEnd_1359891] using wordTrace_append hprefix tailTrace_1359891
  have hstable : (prefixWord ++ tailWord_1359891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359891).length < 2 ^ (prefixWord ++ tailWord_1359891).sum := by decide
  have hdescent : baseEnd_1359891 < baseStart_1359891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359898 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_1359898 : Nat := 118140960795 + 1359898 * 2 ^ 59
def prefixEnd_1359898 : Nat := 4983230072969 + 3 ^ 40 * 1359898 * 2
def baseEnd_1359898 : Nat := 698281315088025626520949

theorem tailTrace_1359898 : CollatzResearch.WordTrace tailWord_1359898 prefixEnd_1359898 698281315088025626520949 := by
  unfold tailWord_1359898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12399888706832318233244087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33066369884886181955317565 12399888706832318233244087)
  ·
    refine ⟨18599833060248477349866131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12399888706832318233244087 18599833060248477349866131)
    ·
      refine ⟨27899749590372716024799197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18599833060248477349866131 27899749590372716024799197)
      ·
        refine ⟨10462406096389768509299699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27899749590372716024799197 10462406096389768509299699)
        ·
          refine ⟨15693609144584652763949549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462406096389768509299699 15693609144584652763949549)
          ·
            refine ⟨5885103429219244786481081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15693609144584652763949549 5885103429219244786481081)
            ·
              refine ⟨4413827571914433589860811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885103429219244786481081 4413827571914433589860811)
              ·
                refine ⟨6620741357871650384791217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413827571914433589860811 6620741357871650384791217)
                ·
                  refine ⟨4965556018403737788593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6620741357871650384791217 4965556018403737788593413)
                  ·
                    refine ⟨931041753450700835361265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965556018403737788593413 931041753450700835361265)
                    ·
                      refine ⟨698281315088025626520949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931041753450700835361265 698281315088025626520949)
                      ·
                        rfl

theorem cell23_1359898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_1359898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359898 prefixEnd_1359898 := by exact prefixLift 1359898
  have htrace : WordTrace (prefixWord ++ tailWord_1359898) baseStart_1359898 baseEnd_1359898 := by
    simpa [prefixWord, tailWord_1359898, baseEnd_1359898] using wordTrace_append hprefix tailTrace_1359898
  have hstable : (prefixWord ++ tailWord_1359898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359898).length < 2 ^ (prefixWord ++ tailWord_1359898).sum := by decide
  have hdescent : baseEnd_1359898 < baseStart_1359898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359918 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1359918 : Nat := 118140960795 + 1359918 * 2 ^ 59
def prefixEnd_1359918 : Nat := 4983230072969 + 3 ^ 40 * 1359918 * 2
def baseEnd_1359918 : Nat := 698291584701115548270857

theorem tailTrace_1359918 : CollatzResearch.WordTrace tailWord_1359918 prefixEnd_1359918 698291584701115548270857 := by
  unfold tailWord_1359918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200035535907102043588051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33066856191504544232469605 6200035535907102043588051)
  ·
    refine ⟨9300053303860653065382077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200035535907102043588051 9300053303860653065382077)
    ·
      refine ⟨3487519988947744899518279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9300053303860653065382077 3487519988947744899518279)
      ·
        refine ⟨5231279983421617349277419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487519988947744899518279 5231279983421617349277419)
        ·
          refine ⟨7846919975132426023916129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231279983421617349277419 7846919975132426023916129)
          ·
            refine ⟨5885189981349319517937097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7846919975132426023916129 5885189981349319517937097)
            ·
              refine ⟨4413892486011989638452823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885189981349319517937097 4413892486011989638452823)
              ·
                refine ⟨6620838729017984457679235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413892486011989638452823 6620838729017984457679235)
                ·
                  refine ⟨9931258093526976686518853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620838729017984457679235 9931258093526976686518853)
                  ·
                    refine ⟨1862110892536308128722285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9931258093526976686518853 1862110892536308128722285)
                    ·
                      refine ⟨698291584701115548270857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862110892536308128722285 698291584701115548270857)
                      ·
                        rfl

theorem cell23_1359918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1359918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359918 prefixEnd_1359918 := by exact prefixLift 1359918
  have htrace : WordTrace (prefixWord ++ tailWord_1359918) baseStart_1359918 baseEnd_1359918 := by
    simpa [prefixWord, tailWord_1359918, baseEnd_1359918] using wordTrace_append hprefix tailTrace_1359918
  have hstable : (prefixWord ++ tailWord_1359918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359918).length < 2 ^ (prefixWord ++ tailWord_1359918).sum := by decide
  have hdescent : baseEnd_1359918 < baseStart_1359918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359925 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1359925 : Nat := 118140960795 + 1359925 * 2 ^ 59
def prefixEnd_1359925 : Nat := 4983230072969 + 3 ^ 40 * 1359925 * 2
def baseEnd_1359925 : Nat := 232765059688565673627775

theorem tailTrace_1359925 : CollatzResearch.WordTrace tailWord_1359925 prefixEnd_1359925 232765059688565673627775 := by
  unfold tailWord_1359925
  simp only [CollatzResearch.WordTrace]
  refine ⟨49600539598231456544209229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33067026398820971029472819 49600539598231456544209229)
  ·
    refine ⟨18600202349336796204078461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49600539598231456544209229 18600202349336796204078461)
    ·
      refine ⟨6975075881001298576529423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18600202349336796204078461 6975075881001298576529423)
      ·
        refine ⟨10462613821501947864794135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6975075881001298576529423 10462613821501947864794135)
        ·
          refine ⟨15693920732252921797191203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462613821501947864794135 15693920732252921797191203)
          ·
            refine ⟨23540881098379382695786805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693920732252921797191203 23540881098379382695786805)
            ·
              refine ⟨2206957602973067127730013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23540881098379382695786805 2206957602973067127730013)
              ·
                refine ⟨827609101114900172898755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2206957602973067127730013 827609101114900172898755)
                ·
                  refine ⟨1241413651672350259348133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827609101114900172898755 1241413651672350259348133)
                  ·
                    refine ⟨232765059688565673627775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241413651672350259348133 232765059688565673627775)
                    ·
                      rfl

theorem cell23_1359925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1359925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359925 prefixEnd_1359925 := by exact prefixLift 1359925
  have htrace : WordTrace (prefixWord ++ tailWord_1359925) baseStart_1359925 baseEnd_1359925 := by
    simpa [prefixWord, tailWord_1359925, baseEnd_1359925] using wordTrace_append hprefix tailTrace_1359925
  have hstable : (prefixWord ++ tailWord_1359925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359925).length < 2 ^ (prefixWord ++ tailWord_1359925).sum := by decide
  have hdescent : baseEnd_1359925 < baseStart_1359925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359968 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_1359968 : Nat := 118140960795 + 1359968 * 2 ^ 59
def prefixEnd_1359968 : Nat := 4983230072969 + 3 ^ 40 * 1359968 * 2
def baseEnd_1359968 : Nat := 232772419577946784215209

theorem tailTrace_1359968 : CollatzResearch.WordTrace tailWord_1359968 prefixEnd_1359968 232772419577946784215209 := by
  unfold tailWord_1359968
  simp only [CollatzResearch.WordTrace]
  refine ⟨24801053968537837444012279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33068071958050449925349705 24801053968537837444012279)
  ·
    refine ⟨37201580952806756166018419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24801053968537837444012279 37201580952806756166018419)
    ·
      refine ⟨55802371429210134249027629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37201580952806756166018419 55802371429210134249027629)
      ·
        refine ⟨20925889285953800343385361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55802371429210134249027629 20925889285953800343385361)
        ·
          refine ⟨15694416964465350257539021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20925889285953800343385361 15694416964465350257539021)
          ·
            refine ⟨5885406361674506346577133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15694416964465350257539021 5885406361674506346577133)
            ·
              refine ⟨2207027385627939879966425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5885406361674506346577133 2207027385627939879966425)
              ·
                refine ⟨1655270539220954909974819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207027385627939879966425 1655270539220954909974819)
                ·
                  refine ⟨2482905808831432364962229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655270539220954909974819 2482905808831432364962229)
                  ·
                    refine ⟨232772419577946784215209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2482905808831432364962229 232772419577946784215209)
                    ·
                      rfl

theorem cell23_1359968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_1359968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359968 prefixEnd_1359968 := by exact prefixLift 1359968
  have htrace : WordTrace (prefixWord ++ tailWord_1359968) baseStart_1359968 baseEnd_1359968 := by
    simpa [prefixWord, tailWord_1359968, baseEnd_1359968] using wordTrace_append hprefix tailTrace_1359968
  have hstable : (prefixWord ++ tailWord_1359968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359968).length < 2 ^ (prefixWord ++ tailWord_1359968).sum := by decide
  have hdescent : baseEnd_1359968 < baseStart_1359968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359975 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_1359975 : Nat := 118140960795 + 1359975 * 2 ^ 59
def prefixEnd_1359975 : Nat := 4983230072969 + 3 ^ 40 * 1359975 * 2
def baseEnd_1359975 : Nat := 698320853098421825258095

theorem tailTrace_1359975 : CollatzResearch.WordTrace tailWord_1359975 prefixEnd_1359975 698320853098421825258095 := by
  unfold tailWord_1359975
  simp only [CollatzResearch.WordTrace]
  refine ⟨49602363248050315083529379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33068242165366876722352919 49602363248050315083529379)
  ·
    refine ⟨74403544872075472625294069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49602363248050315083529379 74403544872075472625294069)
    ·
      refine ⟨6975332331757075558621319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74403544872075472625294069 6975332331757075558621319)
      ·
        refine ⟨10462998497635613337931979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6975332331757075558621319 10462998497635613337931979)
        ·
          refine ⟨15694497746453420006897969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462998497635613337931979 15694497746453420006897969)
          ·
            refine ⟨11770873309840065005173477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15694497746453420006897969 11770873309840065005173477)
            ·
              refine ⟨2207038745595012188470027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11770873309840065005173477 2207038745595012188470027)
              ·
                refine ⟨3310558118392518282705041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207038745595012188470027 3310558118392518282705041)
                ·
                  refine ⟨2482918588794388712028781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310558118392518282705041 2482918588794388712028781)
                  ·
                    refine ⟨931094470797895767010793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482918588794388712028781 931094470797895767010793)
                    ·
                      refine ⟨698320853098421825258095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931094470797895767010793 698320853098421825258095)
                      ·
                        rfl

theorem cell23_1359975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_1359975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359975 prefixEnd_1359975 := by exact prefixLift 1359975
  have htrace : WordTrace (prefixWord ++ tailWord_1359975) baseStart_1359975 baseEnd_1359975 := by
    simpa [prefixWord, tailWord_1359975, baseEnd_1359975] using wordTrace_append hprefix tailTrace_1359975
  have hstable : (prefixWord ++ tailWord_1359975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359975).length < 2 ^ (prefixWord ++ tailWord_1359975).sum := by decide
  have hdescent : baseEnd_1359975 < baseStart_1359975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359982 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1359982 : Nat := 118140960795 + 1359982 * 2 ^ 59
def prefixEnd_1359982 : Nat := 4983230072969 + 3 ^ 40 * 1359982 * 2
def baseEnd_1359982 : Nat := 698324447463003297870563

theorem tailTrace_1359982 : CollatzResearch.WordTrace tailWord_1359982 prefixEnd_1359982 698324447463003297870563 := by
  unfold tailWord_1359982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200327319878119409879275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33068412372683303519356133 6200327319878119409879275)
  ·
    refine ⟨9300490979817179114818913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200327319878119409879275 9300490979817179114818913)
    ·
      refine ⟨6975368234862884336114185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9300490979817179114818913 6975368234862884336114185)
      ·
        refine ⟨5231526176147163252085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6975368234862884336114185 5231526176147163252085639)
        ·
          refine ⟨7847289264220744878128459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231526176147163252085639 7847289264220744878128459)
          ·
            refine ⟨11770933896331117317192689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847289264220744878128459 11770933896331117317192689)
            ·
              refine ⟨8828200422248337987894517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11770933896331117317192689 8828200422248337987894517)
              ·
                refine ⟨827643789585781686365111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8828200422248337987894517 827643789585781686365111)
                ·
                  refine ⟨1241465684378672529547667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827643789585781686365111 1241465684378672529547667)
                  ·
                    refine ⟨1862198526568008794321501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1241465684378672529547667 1862198526568008794321501)
                    ·
                      refine ⟨698324447463003297870563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862198526568008794321501 698324447463003297870563)
                      ·
                        rfl

theorem cell23_1359982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1359982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1359982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1359982 prefixEnd_1359982 := by exact prefixLift 1359982
  have htrace : WordTrace (prefixWord ++ tailWord_1359982) baseStart_1359982 baseEnd_1359982 := by
    simpa [prefixWord, tailWord_1359982, baseEnd_1359982] using wordTrace_append hprefix tailTrace_1359982
  have hstable : (prefixWord ++ tailWord_1359982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359982).length < 2 ^ (prefixWord ++ tailWord_1359982).sum := by decide
  have hdescent : baseEnd_1359982 < baseStart_1359982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360028 : List Nat := [2, 2, 3, 2, 1, 1, 5, 7]
def baseStart_1360028 : Nat := 118140960795 + 1360028 * 2 ^ 59
def prefixEnd_1360028 : Nat := 4983230072969 + 3 ^ 40 * 1360028 * 2
def baseEnd_1360028 : Nat := 25864743243448522885013

theorem tailTrace_1360028 : CollatzResearch.WordTrace tailWord_1360028 prefixEnd_1360028 25864743243448522885013 := by
  unfold tailWord_1360028
  simp only [CollatzResearch.WordTrace]
  refine ⟨24802148158429152567604369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33069530877905536756805825 24802148158429152567604369)
  ·
    refine ⟨18601611118821864425703277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24802148158429152567604369 18601611118821864425703277)
    ·
      refine ⟨6975604169558199159638729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18601611118821864425703277 6975604169558199159638729)
      ·
        refine ⟨5231703127168649369729047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6975604169558199159638729 5231703127168649369729047)
        ·
          refine ⟨7847554690752974054593571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231703127168649369729047 7847554690752974054593571)
          ·
            refine ⟨11771332036129461081890357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847554690752974054593571 11771332036129461081890357)
            ·
              refine ⟨1103562378387136976427221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11771332036129461081890357 1103562378387136976427221)
              ·
                refine ⟨25864743243448522885013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1103562378387136976427221 25864743243448522885013)
                ·
                  rfl

theorem cell23_1360028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 7].length) (baseStart_1360028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360028 prefixEnd_1360028 := by exact prefixLift 1360028
  have htrace : WordTrace (prefixWord ++ tailWord_1360028) baseStart_1360028 baseEnd_1360028 := by
    simpa [prefixWord, tailWord_1360028, baseEnd_1360028] using wordTrace_append hprefix tailTrace_1360028
  have hstable : (prefixWord ++ tailWord_1360028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360028).length < 2 ^ (prefixWord ++ tailWord_1360028).sum := by decide
  have hdescent : baseEnd_1360028 < baseStart_1360028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360039 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1360039 : Nat := 118140960795 + 1360039 * 2 ^ 59
def prefixEnd_1360039 : Nat := 4983230072969 + 3 ^ 40 * 1360039 * 2
def baseEnd_1360039 : Nat := 698353715860309574857801

theorem tailTrace_1360039 : CollatzResearch.WordTrace tailWord_1360039 prefixEnd_1360039 698353715860309574857801 := by
  unfold tailWord_1360039
  simp only [CollatzResearch.WordTrace]
  refine ⟨49604697519818454013859171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33069798346545636009239447 49604697519818454013859171)
  ·
    refine ⟨74407046279727681020788757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49604697519818454013859171 74407046279727681020788757)
    ·
      refine ⟨3487830294362235047849473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74407046279727681020788757 3487830294362235047849473)
      ·
        refine ⟨2615872720771676285887105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3487830294362235047849473 2615872720771676285887105)
        ·
          refine ⟨1961904540578757214415329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615872720771676285887105 1961904540578757214415329)
          ·
            refine ⟨1471428405434067910811497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961904540578757214415329 1471428405434067910811497)
            ·
              refine ⟨1103571304075550933108623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471428405434067910811497 1103571304075550933108623)
              ·
                refine ⟨1655356956113326399662935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103571304075550933108623 1655356956113326399662935)
                ·
                  refine ⟨2483035434169989599494403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655356956113326399662935 2483035434169989599494403)
                  ·
                    refine ⟨3724553151254984399241605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2483035434169989599494403 3724553151254984399241605)
                    ·
                      refine ⟨698353715860309574857801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3724553151254984399241605 698353715860309574857801)
                      ·
                        rfl

theorem cell23_1360039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1360039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360039 prefixEnd_1360039 := by exact prefixLift 1360039
  have htrace : WordTrace (prefixWord ++ tailWord_1360039) baseStart_1360039 baseEnd_1360039 := by
    simpa [prefixWord, tailWord_1360039, baseEnd_1360039] using wordTrace_append hprefix tailTrace_1360039
  have hstable : (prefixWord ++ tailWord_1360039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360039).length < 2 ^ (prefixWord ++ tailWord_1360039).sum := by decide
  have hdescent : baseEnd_1360039 < baseStart_1360039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360049 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 2, 4]
def baseStart_1360049 : Nat := 118140960795 + 1360049 * 2 ^ 59
def prefixEnd_1360049 : Nat := 4983230072969 + 3 ^ 40 * 1360049 * 2
def baseEnd_1360049 : Nat := 232786283555618178577585

theorem tailTrace_1360049 : CollatzResearch.WordTrace tailWord_1360049 prefixEnd_1360049 232786283555618178577585 := by
  unfold tailWord_1360049
  simp only [CollatzResearch.WordTrace]
  refine ⟨49605062249782225721723201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33070041499854817147815467 49605062249782225721723201)
  ·
    refine ⟨37203796687336669291292401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49605062249782225721723201 37203796687336669291292401)
    ·
      refine ⟨27902847515502501968469301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37203796687336669291292401 27902847515502501968469301)
      ·
        refine ⟨2615891954578359559543997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27902847515502501968469301 2615891954578359559543997)
        ·
          refine ⟨980959482966884834828999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2615891954578359559543997 980959482966884834828999)
          ·
            refine ⟨1471439224450327252243499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980959482966884834828999 1471439224450327252243499)
            ·
              refine ⟨2207158836675490878365249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471439224450327252243499 2207158836675490878365249)
              ·
                refine ⟨1655369127506618158773937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207158836675490878365249 1655369127506618158773937)
                ·
                  refine ⟨1241526845629963619080453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1655369127506618158773937 1241526845629963619080453)
                  ·
                    refine ⟨232786283555618178577585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241526845629963619080453 232786283555618178577585)
                    ·
                      rfl

theorem cell23_1360049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_1360049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360049 prefixEnd_1360049 := by exact prefixLift 1360049
  have htrace : WordTrace (prefixWord ++ tailWord_1360049) baseStart_1360049 baseEnd_1360049 := by
    simpa [prefixWord, tailWord_1360049, baseEnd_1360049] using wordTrace_append hprefix tailTrace_1360049
  have hstable : (prefixWord ++ tailWord_1360049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360049).length < 2 ^ (prefixWord ++ tailWord_1360049).sum := by decide
  have hdescent : baseEnd_1360049 < baseStart_1360049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360055 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_1360055 : Nat := 118140960795 + 1360055 * 2 ^ 59
def prefixEnd_1360055 : Nat := 4983230072969 + 3 ^ 40 * 1360055 * 2
def baseEnd_1360055 : Nat := 698361931550781512257727

theorem tailTrace_1360055 : CollatzResearch.WordTrace tailWord_1360055 prefixEnd_1360055 698361931550781512257727 := by
  unfold tailWord_1360055
  simp only [CollatzResearch.WordTrace]
  refine ⟨49605281087760488746441619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33070187391840325830961079 49605281087760488746441619)
  ·
    refine ⟨74407921631640733119662429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49605281087760488746441619 74407921631640733119662429)
    ·
      refine ⟨27902970611865274919873411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74407921631640733119662429 27902970611865274919873411)
      ·
        refine ⟨41854455917797912379810117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27902970611865274919873411 41854455917797912379810117)
        ·
          refine ⟨7847710484587108571214397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41854455917797912379810117 7847710484587108571214397)
          ·
            refine ⟨2942891431720165714205399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7847710484587108571214397 2942891431720165714205399)
            ·
              refine ⟨4414337147580248571308099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942891431720165714205399 4414337147580248571308099)
              ·
                refine ⟨6621505721370372856962149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414337147580248571308099 6621505721370372856962149)
                ·
                  refine ⟨1241532322756944910680403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6621505721370372856962149 1241532322756944910680403)
                  ·
                    refine ⟨1862298484135417366020605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1241532322756944910680403 1862298484135417366020605)
                    ·
                      refine ⟨698361931550781512257727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862298484135417366020605 698361931550781512257727)
                      ·
                        rfl

theorem cell23_1360055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_1360055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360055 prefixEnd_1360055 := by exact prefixLift 1360055
  have htrace : WordTrace (prefixWord ++ tailWord_1360055) baseStart_1360055 baseEnd_1360055 := by
    simpa [prefixWord, tailWord_1360055, baseEnd_1360055] using wordTrace_append hprefix tailTrace_1360055
  have hstable : (prefixWord ++ tailWord_1360055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360055).length < 2 ^ (prefixWord ++ tailWord_1360055).sum := by decide
  have hdescent : baseEnd_1360055 < baseStart_1360055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360066 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1360066 : Nat := 118140960795 + 1360066 * 2 ^ 59
def prefixEnd_1360066 : Nat := 4983230072969 + 3 ^ 40 * 1360066 * 2
def baseEnd_1360066 : Nat := 232789193279326989740059

theorem tailTrace_1360066 : CollatzResearch.WordTrace tailWord_1360066 prefixEnd_1360066 232789193279326989740059 := by
  unfold tailWord_1360066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401420572680159406273013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33070454860480425083394701 12401420572680159406273013)
  ·
    refine ⟨1162633178688764944338095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12401420572680159406273013 1162633178688764944338095)
    ·
      refine ⟨1743949768033147416507143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162633178688764944338095 1743949768033147416507143)
      ·
        refine ⟨2615924652049721124760715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743949768033147416507143 2615924652049721124760715)
        ·
          refine ⟨3923886978074581687141073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2615924652049721124760715 3923886978074581687141073)
          ·
            refine ⟨2942915233555936265355805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3923886978074581687141073 2942915233555936265355805)
            ·
              refine ⟨1103593212583476099508427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2942915233555936265355805 1103593212583476099508427)
              ·
                refine ⟨1655389818875214149262641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103593212583476099508427 1655389818875214149262641)
                ·
                  refine ⟨1241542364156410611946981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1655389818875214149262641 1241542364156410611946981)
                  ·
                    refine ⟨232789193279326989740059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1241542364156410611946981 232789193279326989740059)
                    ·
                      rfl

theorem cell23_1360066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1360066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360066 prefixEnd_1360066 := by exact prefixLift 1360066
  have htrace : WordTrace (prefixWord ++ tailWord_1360066) baseStart_1360066 baseEnd_1360066 := by
    simpa [prefixWord, tailWord_1360066, baseEnd_1360066] using wordTrace_append hprefix tailTrace_1360066
  have hstable : (prefixWord ++ tailWord_1360066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360066).length < 2 ^ (prefixWord ++ tailWord_1360066).sum := by decide
  have hdescent : baseEnd_1360066 < baseStart_1360066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360082 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1360082 : Nat := 118140960795 + 1360082 * 2 ^ 59
def prefixEnd_1360082 : Nat := 4983230072969 + 3 ^ 40 * 1360082 * 2
def baseEnd_1360082 : Nat := 698375795528452906620103

theorem tailTrace_1360082 : CollatzResearch.WordTrace tailWord_1360082 prefixEnd_1360082 698375795528452906620103 := by
  unfold tailWord_1360082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401566464665668089418625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33070843905775114905116333 12401566464665668089418625)
  ·
    refine ⟨9301174848499251067063969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12401566464665668089418625 9301174848499251067063969)
    ·
      refine ⟨6975881136374438300297977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9301174848499251067063969 6975881136374438300297977)
      ·
        refine ⟨5231910852280828725223483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6975881136374438300297977 5231910852280828725223483)
        ·
          refine ⟨7847866278421243087835225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5231910852280828725223483 7847866278421243087835225)
          ·
            refine ⟨5885899708815932315876419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7847866278421243087835225 5885899708815932315876419)
            ·
              refine ⟨8828849563223898473814629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885899708815932315876419 8828849563223898473814629)
              ·
                refine ⟨1655409293104480963840243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8828849563223898473814629 1655409293104480963840243)
                ·
                  refine ⟨2483113939656721445760365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655409293104480963840243 2483113939656721445760365)
                  ·
                    refine ⟨931167727371270542160137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2483113939656721445760365 931167727371270542160137)
                    ·
                      refine ⟨698375795528452906620103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931167727371270542160137 698375795528452906620103)
                      ·
                        rfl

theorem cell23_1360082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1360082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360082 prefixEnd_1360082 := by exact prefixLift 1360082
  have htrace : WordTrace (prefixWord ++ tailWord_1360082) baseStart_1360082 baseEnd_1360082 := by
    simpa [prefixWord, tailWord_1360082, baseEnd_1360082] using wordTrace_append hprefix tailTrace_1360082
  have hstable : (prefixWord ++ tailWord_1360082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360082).length < 2 ^ (prefixWord ++ tailWord_1360082).sum := by decide
  have hdescent : baseEnd_1360082 < baseStart_1360082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360091 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_1360091 : Nat := 118140960795 + 1360091 * 2 ^ 59
def prefixEnd_1360091 : Nat := 4983230072969 + 3 ^ 40 * 1360091 * 2
def baseEnd_1360091 : Nat := 698380416854343371407561

theorem tailTrace_1360091 : CollatzResearch.WordTrace tailWord_1360091 prefixEnd_1360091 698380416854343371407561 := by
  unfold tailWord_1360091
  simp only [CollatzResearch.WordTrace]
  refine ⟨49606594115630066894752127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33071062743753377929834751 49606594115630066894752127)
  ·
    refine ⟨74409891173445100342128191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49606594115630066894752127 74409891173445100342128191)
    ·
      refine ⟨111614836760167650513192287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74409891173445100342128191 111614836760167650513192287)
      ·
        refine ⟨167422255140251475769788431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111614836760167650513192287 167422255140251475769788431)
        ·
          refine ⟨251133382710377213654682647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167422255140251475769788431 251133382710377213654682647)
          ·
            refine ⟨376700074065565820482023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251133382710377213654682647 376700074065565820482023971)
            ·
              refine ⟨565050111098348730723035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376700074065565820482023971 565050111098348730723035957)
              ·
                refine ⟨52973447915470193505284621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565050111098348730723035957 52973447915470193505284621)
                ·
                  refine ⟨19865042968301322564481733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52973447915470193505284621 19865042968301322564481733)
                  ·
                    refine ⟨3724695556556497980840325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19865042968301322564481733 3724695556556497980840325)
                    ·
                      refine ⟨698380416854343371407561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3724695556556497980840325 698380416854343371407561)
                      ·
                        rfl

theorem cell23_1360091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_1360091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360091 prefixEnd_1360091 := by exact prefixLift 1360091
  have htrace : WordTrace (prefixWord ++ tailWord_1360091) baseStart_1360091 baseEnd_1360091 := by
    simpa [prefixWord, tailWord_1360091, baseEnd_1360091] using wordTrace_append hprefix tailTrace_1360091
  have hstable : (prefixWord ++ tailWord_1360091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360091).length < 2 ^ (prefixWord ++ tailWord_1360091).sum := by decide
  have hdescent : baseEnd_1360091 < baseStart_1360091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360121 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1360121 : Nat := 118140960795 + 1360121 * 2 ^ 59
def prefixEnd_1360121 : Nat := 4983230072969 + 3 ^ 40 * 1360121 * 2
def baseEnd_1360121 : Nat := 698395821273978254032423

theorem tailTrace_1360121 : CollatzResearch.WordTrace tailWord_1360121 prefixEnd_1360121 698395821273978254032423 := by
  unfold tailWord_1360121
  simp only [CollatzResearch.WordTrace]
  refine ⟨49607688305521382018344217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33071792203680921345562811 49607688305521382018344217)
  ·
    refine ⟨37205766229141036513758163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49607688305521382018344217 37205766229141036513758163)
    ·
      refine ⟨55808649343711554770637245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37205766229141036513758163 55808649343711554770637245)
      ·
        refine ⟨20928243503891833038988967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55808649343711554770637245 20928243503891833038988967)
        ·
          refine ⟨31392365255837749558483451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20928243503891833038988967 31392365255837749558483451)
          ·
            refine ⟨47088547883756624337725177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31392365255837749558483451 47088547883756624337725177)
            ·
              refine ⟨35316410912817468253293883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47088547883756624337725177 35316410912817468253293883)
              ·
                refine ⟨52974616369226202379940825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35316410912817468253293883 52974616369226202379940825)
                ·
                  refine ⟨39730962276919651784955619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52974616369226202379940825 39730962276919651784955619)
                  ·
                    refine ⟨59596443415379477677433429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39730962276919651784955619 59596443415379477677433429)
                    ·
                      refine ⟨698395821273978254032423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 59596443415379477677433429 698395821273978254032423)
                      ·
                        rfl

theorem cell23_1360121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1360121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360121 prefixEnd_1360121 := by exact prefixLift 1360121
  have htrace : WordTrace (prefixWord ++ tailWord_1360121) baseStart_1360121 baseEnd_1360121 := by
    simpa [prefixWord, tailWord_1360121, baseEnd_1360121] using wordTrace_append hprefix tailTrace_1360121
  have hstable : (prefixWord ++ tailWord_1360121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360121).length < 2 ^ (prefixWord ++ tailWord_1360121).sum := by decide
  have hdescent : baseEnd_1360121 < baseStart_1360121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360128 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_1360128 : Nat := 118140960795 + 1360128 * 2 ^ 59
def prefixEnd_1360128 : Nat := 4983230072969 + 3 ^ 40 * 1360128 * 2
def baseEnd_1360128 : Nat := 698399415638559726644891

theorem tailTrace_1360128 : CollatzResearch.WordTrace tailWord_1360128 prefixEnd_1360128 698399415638559726644891 := by
  unfold tailWord_1360128
  simp only [CollatzResearch.WordTrace]
  refine ⟨24803971808248011106924519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33071962410997348142566025 24803971808248011106924519)
  ·
    refine ⟨37205957712372016660386779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24803971808248011106924519 37205957712372016660386779)
    ·
      refine ⟨55808936568558024990580169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37205957712372016660386779 55808936568558024990580169)
      ·
        refine ⟨41856702426418518742935127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55808936568558024990580169 41856702426418518742935127)
        ·
          refine ⟨62785053639627778114402691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41856702426418518742935127 62785053639627778114402691)
          ·
            refine ⟨94177580459441667171604037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62785053639627778114402691 94177580459441667171604037)
            ·
              refine ⟨17658296336145312594675757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94177580459441667171604037 17658296336145312594675757)
              ·
                refine ⟨6621861126054492223003409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17658296336145312594675757 6621861126054492223003409)
                ·
                  refine ⟨4966395844540869167252557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6621861126054492223003409 4966395844540869167252557)
                  ·
                    refine ⟨1862398441702825937719709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4966395844540869167252557 1862398441702825937719709)
                    ·
                      refine ⟨698399415638559726644891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862398441702825937719709 698399415638559726644891)
                      ·
                        rfl

theorem cell23_1360128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_1360128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360128 prefixEnd_1360128 := by exact prefixLift 1360128
  have htrace : WordTrace (prefixWord ++ tailWord_1360128) baseStart_1360128 baseEnd_1360128 := by
    simpa [prefixWord, tailWord_1360128, baseEnd_1360128] using wordTrace_append hprefix tailTrace_1360128
  have hstable : (prefixWord ++ tailWord_1360128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360128).length < 2 ^ (prefixWord ++ tailWord_1360128).sum := by decide
  have hdescent : baseEnd_1360128 < baseStart_1360128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360228 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_1360228 : Nat := 118140960795 + 1360228 * 2 ^ 59
def prefixEnd_1360228 : Nat := 4983230072969 + 3 ^ 40 * 1360228 * 2
def baseEnd_1360228 : Nat := 698450763704009335394431

theorem tailTrace_1360228 : CollatzResearch.WordTrace tailWord_1360228 prefixEnd_1360228 698450763704009335394431 := by
  unfold tailWord_1360228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805795458066869646244669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33074393944089159528326225 24805795458066869646244669)
  ·
    refine ⟨9302173296775076117341751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24805795458066869646244669 9302173296775076117341751)
    ·
      refine ⟨13953259945162614176012627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302173296775076117341751 13953259945162614176012627)
      ·
        refine ⟨20929889917743921264018941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953259945162614176012627 20929889917743921264018941)
        ·
          refine ⟨7848708719153970474007103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20929889917743921264018941 7848708719153970474007103)
          ·
            refine ⟨11773063078730955711010655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848708719153970474007103 11773063078730955711010655)
            ·
              refine ⟨17659594618096433566515983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11773063078730955711010655 17659594618096433566515983)
              ·
                refine ⟨26489391927144650349773975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17659594618096433566515983 26489391927144650349773975)
                ·
                  refine ⟨39734087890716975524660963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26489391927144650349773975 39734087890716975524660963)
                  ·
                    refine ⟨59601131836075463286991445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39734087890716975524660963 59601131836075463286991445)
                    ·
                      refine ⟨698450763704009335394431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 59601131836075463286991445 698450763704009335394431)
                      ·
                        rfl

theorem cell23_1360228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_1360228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360228 prefixEnd_1360228 := by exact prefixLift 1360228
  have htrace : WordTrace (prefixWord ++ tailWord_1360228) baseStart_1360228 baseEnd_1360228 := by
    simpa [prefixWord, tailWord_1360228, baseEnd_1360228] using wordTrace_append hprefix tailTrace_1360228
  have hstable : (prefixWord ++ tailWord_1360228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360228).length < 2 ^ (prefixWord ++ tailWord_1360228).sum := by decide
  have hdescent : baseEnd_1360228 < baseStart_1360228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360235 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 3]
def baseStart_1360235 : Nat := 118140960795 + 1360235 * 2 ^ 59
def prefixEnd_1360235 : Nat := 4983230072969 + 3 ^ 40 * 1360235 * 2
def baseEnd_1360235 : Nat := 698454358068590808006899

theorem tailTrace_1360235 : CollatzResearch.WordTrace tailWord_1360235 prefixEnd_1360235 698454358068590808006899 := by
  unfold tailWord_1360235
  simp only [CollatzResearch.WordTrace]
  refine ⟨49611846227108379487994159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33074564151405586325329439 49611846227108379487994159)
  ·
    refine ⟨74417769340662569231991239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49611846227108379487994159 74417769340662569231991239)
    ·
      refine ⟨111626654010993853847986859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74417769340662569231991239 111626654010993853847986859)
      ·
        refine ⟨167439981016490780771980289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111626654010993853847986859 167439981016490780771980289)
        ·
          refine ⟨125579985762368085578985217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167439981016490780771980289 125579985762368085578985217)
          ·
            refine ⟨94184989321776064184238913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125579985762368085578985217 94184989321776064184238913)
            ·
              refine ⟨70638741991332048138179185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94184989321776064184238913 70638741991332048138179185)
              ·
                refine ⟨52979056493499036103634389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70638741991332048138179185 52979056493499036103634389)
                ·
                  refine ⟨1241696636566383658678931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52979056493499036103634389 1241696636566383658678931)
                  ·
                    refine ⟨1862544954849575488018397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1241696636566383658678931 1862544954849575488018397)
                    ·
                      refine ⟨698454358068590808006899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862544954849575488018397 698454358068590808006899)
                      ·
                        rfl

theorem cell23_1360235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 3].length) (baseStart_1360235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360235 prefixEnd_1360235 := by exact prefixLift 1360235
  have htrace : WordTrace (prefixWord ++ tailWord_1360235) baseStart_1360235 baseEnd_1360235 := by
    simpa [prefixWord, tailWord_1360235, baseEnd_1360235] using wordTrace_append hprefix tailTrace_1360235
  have hstable : (prefixWord ++ tailWord_1360235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360235).length < 2 ^ (prefixWord ++ tailWord_1360235).sum := by decide
  have hdescent : baseEnd_1360235 < baseStart_1360235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360242 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_1360242 : Nat := 118140960795 + 1360242 * 2 ^ 59
def prefixEnd_1360242 : Nat := 4983230072969 + 3 ^ 40 * 1360242 * 2
def baseEnd_1360242 : Nat := 77606439159241364513263

theorem tailTrace_1360242 : CollatzResearch.WordTrace tailWord_1360242 prefixEnd_1360242 77606439159241364513263 := by
  unfold tailWord_1360242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403025384520754920874745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33074734358722013122332653 12403025384520754920874745)
  ·
    refine ⟨9302269038390566190656059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12403025384520754920874745 9302269038390566190656059)
    ·
      refine ⟨13953403557585849285984089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302269038390566190656059 13953403557585849285984089)
      ·
        refine ⟨10465052668189386964488067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13953403557585849285984089 10465052668189386964488067)
        ·
          refine ⟨15697579002284080446732101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465052668189386964488067 15697579002284080446732101)
          ·
            refine ⟨2943296062928265083762269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15697579002284080446732101 2943296062928265083762269)
            ·
              refine ⟨1103736023598099406410851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2943296062928265083762269 1103736023598099406410851)
              ·
                refine ⟨1655604035397149109616277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103736023598099406410851 1655604035397149109616277)
                ·
                  refine ⟨77606439159241364513263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1655604035397149109616277 77606439159241364513263)
                  ·
                    rfl

theorem cell23_1360242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_1360242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360242 prefixEnd_1360242 := by exact prefixLift 1360242
  have htrace : WordTrace (prefixWord ++ tailWord_1360242) baseStart_1360242 baseEnd_1360242 := by
    simpa [prefixWord, tailWord_1360242, baseEnd_1360242] using wordTrace_append hprefix tailTrace_1360242
  have hstable : (prefixWord ++ tailWord_1360242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360242).length < 2 ^ (prefixWord ++ tailWord_1360242).sum := by decide
  have hdescent : baseEnd_1360242 < baseStart_1360242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360286 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1360286 : Nat := 118140960795 + 1360286 * 2 ^ 59
def prefixEnd_1360286 : Nat := 4983230072969 + 3 ^ 40 * 1360286 * 2
def baseEnd_1360286 : Nat := 698480545581970108469165

theorem tailTrace_1360286 : CollatzResearch.WordTrace tailWord_1360286 prefixEnd_1360286 698480545581970108469165 := by
  unfold tailWord_1360286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201713293740451899762589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33075804233282410132067141 6201713293740451899762589)
  ·
    refine ⟨2325642485152669462410971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6201713293740451899762589 2325642485152669462410971)
    ·
      refine ⟨3488463727729004193616457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325642485152669462410971 3488463727729004193616457)
      ·
        refine ⟨2616347795796753145212343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3488463727729004193616457 2616347795796753145212343)
        ·
          refine ⟨3924521693695129717818515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616347795796753145212343 3924521693695129717818515)
          ·
            refine ⟨5886782540542694576727773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924521693695129717818515 5886782540542694576727773)
            ·
              refine ⟨2207543452703510466272915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5886782540542694576727773 2207543452703510466272915)
              ·
                refine ⟨3311315179055265699409373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207543452703510466272915 3311315179055265699409373)
                ·
                  refine ⟨1241743192145724637278515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3311315179055265699409373 1241743192145724637278515)
                  ·
                    refine ⟨1862614788218586955917773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1241743192145724637278515 1862614788218586955917773)
                    ·
                      refine ⟨698480545581970108469165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862614788218586955917773 698480545581970108469165)
                      ·
                        rfl

theorem cell23_1360286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1360286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360286 prefixEnd_1360286 := by exact prefixLift 1360286
  have htrace : WordTrace (prefixWord ++ tailWord_1360286) baseStart_1360286 baseEnd_1360286 := by
    simpa [prefixWord, tailWord_1360286, baseEnd_1360286] using wordTrace_append hprefix tailTrace_1360286
  have hstable : (prefixWord ++ tailWord_1360286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360286).length < 2 ^ (prefixWord ++ tailWord_1360286).sum := by decide
  have hdescent : baseEnd_1360286 < baseStart_1360286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360305 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1360305 : Nat := 118140960795 + 1360305 * 2 ^ 59
def prefixEnd_1360305 : Nat := 4983230072969 + 3 ^ 40 * 1360305 * 2
def baseEnd_1360305 : Nat := 698490301714405534131577

theorem tailTrace_1360305 : CollatzResearch.WordTrace tailWord_1360305 prefixEnd_1360305 698490301714405534131577 := by
  unfold tailWord_1360305
  simp only [CollatzResearch.WordTrace]
  refine ⟨49614399336854781443042369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33076266224569854295361579 49614399336854781443042369)
  ·
    refine ⟨37210799502641086082281777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49614399336854781443042369 37210799502641086082281777)
    ·
      refine ⟨27908099626980814561711333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37210799502641086082281777 27908099626980814561711333)
      ·
        refine ⟨5232768680058902730320875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27908099626980814561711333 5232768680058902730320875)
        ·
          refine ⟨7849153020088354095481313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232768680058902730320875 7849153020088354095481313)
          ·
            refine ⟨5886864765066265571610985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7849153020088354095481313 5886864765066265571610985)
            ·
              refine ⟨4415148573799699178708239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5886864765066265571610985 4415148573799699178708239)
              ·
                refine ⟨6622722860699548768062359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415148573799699178708239 6622722860699548768062359)
                ·
                  refine ⟨9934084291049323152093539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622722860699548768062359 9934084291049323152093539)
                  ·
                    refine ⟨14901126436573984728140309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9934084291049323152093539 14901126436573984728140309)
                    ·
                      refine ⟨698490301714405534131577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14901126436573984728140309 698490301714405534131577)
                      ·
                        rfl

theorem cell23_1360305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1360305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360305 prefixEnd_1360305 := by exact prefixLift 1360305
  have htrace : WordTrace (prefixWord ++ tailWord_1360305) baseStart_1360305 baseEnd_1360305 := by
    simpa [prefixWord, tailWord_1360305, baseEnd_1360305] using wordTrace_append hprefix tailTrace_1360305
  have hstable : (prefixWord ++ tailWord_1360305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360305).length < 2 ^ (prefixWord ++ tailWord_1360305).sum := by decide
  have hdescent : baseEnd_1360305 < baseStart_1360305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360352 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2]
def baseStart_1360352 : Nat := 118140960795 + 1360352 * 2 ^ 59
def prefixEnd_1360352 : Nat := 4983230072969 + 3 ^ 40 * 1360352 * 2
def baseEnd_1360352 : Nat := 698514435305166850243861

theorem tailTrace_1360352 : CollatzResearch.WordTrace tailWord_1360352 prefixEnd_1360352 698514435305166850243861 := by
  unfold tailWord_1360352
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808056783842254235001655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33077409045123005646668873 24808056783842254235001655)
  ·
    refine ⟨37212085175763381352502483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24808056783842254235001655 37212085175763381352502483)
    ·
      refine ⟨55818127763645072028753725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37212085175763381352502483 55818127763645072028753725)
      ·
        refine ⟨20931797911366902010782647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55818127763645072028753725 20931797911366902010782647)
        ·
          refine ⟨31397696867050353016173971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20931797911366902010782647 31397696867050353016173971)
          ·
            refine ⟨47096545300575529524260957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31397696867050353016173971 47096545300575529524260957)
            ·
              refine ⟨17661204487715823571597859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47096545300575529524260957 17661204487715823571597859)
              ·
                refine ⟨26491806731573735357396789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17661204487715823571597859 26491806731573735357396789)
                ·
                  refine ⟨2483606881085037689755949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26491806731573735357396789 2483606881085037689755949)
                  ·
                    refine ⟨931352580406889133658481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2483606881085037689755949 931352580406889133658481)
                    ·
                      refine ⟨698514435305166850243861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931352580406889133658481 698514435305166850243861)
                      ·
                        rfl

theorem cell23_1360352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_1360352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360352 prefixEnd_1360352 := by exact prefixLift 1360352
  have htrace : WordTrace (prefixWord ++ tailWord_1360352) baseStart_1360352 baseEnd_1360352 := by
    simpa [prefixWord, tailWord_1360352, baseEnd_1360352] using wordTrace_append hprefix tailTrace_1360352
  have hstable : (prefixWord ++ tailWord_1360352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360352).length < 2 ^ (prefixWord ++ tailWord_1360352).sum := by decide
  have hdescent : baseEnd_1360352 < baseStart_1360352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360359 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1360359 : Nat := 118140960795 + 1360359 * 2 ^ 59
def prefixEnd_1360359 : Nat := 4983230072969 + 3 ^ 40 * 1360359 * 2
def baseEnd_1360359 : Nat := 698518029669748322856329

theorem tailTrace_1360359 : CollatzResearch.WordTrace tailWord_1360359 prefixEnd_1360359 698518029669748322856329 := by
  unfold tailWord_1360359
  simp only [CollatzResearch.WordTrace]
  refine ⟨49616368878659148665508131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33077579252439432443672087 49616368878659148665508131)
  ·
    refine ⟨74424553317988722998262197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49616368878659148665508131 74424553317988722998262197)
    ·
      refine ⟨6977301873561442781087081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74424553317988722998262197 6977301873561442781087081)
      ·
        refine ⟨5232976405171082085815311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6977301873561442781087081 5232976405171082085815311)
        ·
          refine ⟨7849464607756623128722967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232976405171082085815311 7849464607756623128722967)
          ·
            refine ⟨11774196911634934693084451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849464607756623128722967 11774196911634934693084451)
            ·
              refine ⟨17661295367452402039626677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11774196911634934693084451 17661295367452402039626677)
              ·
                refine ⟨1655746440698662691215001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17661295367452402039626677 1655746440698662691215001)
                ·
                  refine ⟨1241809830523997018411251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1655746440698662691215001 1241809830523997018411251)
                  ·
                    refine ⟨1862714745785995527616877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1241809830523997018411251 1862714745785995527616877)
                    ·
                      refine ⟨698518029669748322856329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862714745785995527616877 698518029669748322856329)
                      ·
                        rfl

theorem cell23_1360359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1360359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360359 prefixEnd_1360359 := by exact prefixLift 1360359
  have htrace : WordTrace (prefixWord ++ tailWord_1360359) baseStart_1360359 baseEnd_1360359 := by
    simpa [prefixWord, tailWord_1360359, baseEnd_1360359] using wordTrace_append hprefix tailTrace_1360359
  have hstable : (prefixWord ++ tailWord_1360359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360359).length < 2 ^ (prefixWord ++ tailWord_1360359).sum := by decide
  have hdescent : baseEnd_1360359 < baseStart_1360359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360369 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_1360369 : Nat := 118140960795 + 1360369 * 2 ^ 59
def prefixEnd_1360369 : Nat := 4983230072969 + 3 ^ 40 * 1360369 * 2
def baseEnd_1360369 : Nat := 698523164476293283731283

theorem tailTrace_1360369 : CollatzResearch.WordTrace tailWord_1360369 prefixEnd_1360369 698523164476293283731283 := by
  unfold tailWord_1360369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49616733608622920373372161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33077822405748613582248107 49616733608622920373372161)
  ·
    refine ⟨37212550206467190280029121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49616733608622920373372161 37212550206467190280029121)
    ·
      refine ⟨27909412654850392710021841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37212550206467190280029121 27909412654850392710021841)
      ·
        refine ⟨20932059491137794532516381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27909412654850392710021841 20932059491137794532516381)
        ·
          refine ⟨7849522309176672949693643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20932059491137794532516381 7849522309176672949693643)
          ·
            refine ⟨11774283463765009424540465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849522309176672949693643 11774283463765009424540465)
            ·
              refine ⟨8830712597823757068405349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11774283463765009424540465 8830712597823757068405349)
              ·
                refine ⟨1655758612091954450326003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8830712597823757068405349 1655758612091954450326003)
                ·
                  refine ⟨2483637918137931675489005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655758612091954450326003 2483637918137931675489005)
                  ·
                    refine ⟨931364219301724378308377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2483637918137931675489005 931364219301724378308377)
                    ·
                      refine ⟨698523164476293283731283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931364219301724378308377 698523164476293283731283)
                      ·
                        rfl

theorem cell23_1360369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_1360369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360369 prefixEnd_1360369 := by exact prefixLift 1360369
  have htrace : WordTrace (prefixWord ++ tailWord_1360369) baseStart_1360369 baseEnd_1360369 := by
    simpa [prefixWord, tailWord_1360369, baseEnd_1360369] using wordTrace_append hprefix tailTrace_1360369
  have hstable : (prefixWord ++ tailWord_1360369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360369).length < 2 ^ (prefixWord ++ tailWord_1360369).sum := by decide
  have hdescent : baseEnd_1360369 < baseStart_1360369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360412 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1360412 : Nat := 118140960795 + 1360412 * 2 ^ 59
def prefixEnd_1360412 : Nat := 4983230072969 + 3 ^ 40 * 1360412 * 2
def baseEnd_1360412 : Nat := 698545244144436615493585

theorem tailTrace_1360412 : CollatzResearch.WordTrace tailWord_1360412 prefixEnd_1360412 698545244144436615493585 := by
  unfold tailWord_1360412
  simp only [CollatzResearch.WordTrace]
  refine ⟨24809150973733569358593745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33078867964978092478124993 24809150973733569358593745)
  ·
    refine ⟨18606863230300177018945309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24809150973733569358593745 18606863230300177018945309)
    ·
      refine ⟨6977573711362566382104491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18606863230300177018945309 6977573711362566382104491)
      ·
        refine ⟨10466360567043849573156737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6977573711362566382104491 10466360567043849573156737)
        ·
          refine ⟨7849770425282887179867553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10466360567043849573156737 7849770425282887179867553)
          ·
            refine ⟨5887327818962165384900665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7849770425282887179867553 5887327818962165384900665)
            ·
              refine ⟨4415495864221624038675499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887327818962165384900665 4415495864221624038675499)
              ·
                refine ⟨6623243796332436058013249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415495864221624038675499 6623243796332436058013249)
                ·
                  refine ⟨4967432847249327043509937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623243796332436058013249 4967432847249327043509937)
                  ·
                    refine ⟨3725574635436995282632453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967432847249327043509937 3725574635436995282632453)
                    ·
                      refine ⟨698545244144436615493585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3725574635436995282632453 698545244144436615493585)
                      ·
                        rfl

theorem cell23_1360412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1360412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360412 prefixEnd_1360412 := by exact prefixLift 1360412
  have htrace : WordTrace (prefixWord ++ tailWord_1360412) baseStart_1360412 baseEnd_1360412 := by
    simpa [prefixWord, tailWord_1360412, baseEnd_1360412] using wordTrace_append hprefix tailTrace_1360412
  have hstable : (prefixWord ++ tailWord_1360412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360412).length < 2 ^ (prefixWord ++ tailWord_1360412).sum := by decide
  have hdescent : baseEnd_1360412 < baseStart_1360412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360435 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 7]
def baseStart_1360435 : Nat := 118140960795 + 1360435 * 2 ^ 59
def prefixEnd_1360435 : Nat := 4983230072969 + 3 ^ 40 * 1360435 * 2
def baseEnd_1360435 : Nat := 232852351399830008501993

theorem tailTrace_1360435 : CollatzResearch.WordTrace tailWord_1360435 prefixEnd_1360435 232852351399830008501993 := by
  unfold tailWord_1360435
  simp only [CollatzResearch.WordTrace]
  refine ⟨49619140826383813645274759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33079427217589209096849839 49619140826383813645274759)
  ·
    refine ⟨74428711239575720467912139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49619140826383813645274759 74428711239575720467912139)
    ·
      refine ⟨111643066859363580701868209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74428711239575720467912139 111643066859363580701868209)
      ·
        refine ⟨83732300144522685526401157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111643066859363580701868209 83732300144522685526401157)
        ·
          refine ⟨15699806277098003536200217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83732300144522685526401157 15699806277098003536200217)
          ·
            refine ⟨11774854707823502652150163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15699806277098003536200217 11774854707823502652150163)
            ·
              refine ⟨17662282061735253978225245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11774854707823502652150163 17662282061735253978225245)
              ·
                refine ⟨6623355773150720241834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17662282061735253978225245 6623355773150720241834467)
                ·
                  refine ⟨9935033659726080362751701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6623355773150720241834467 9935033659726080362751701)
                  ·
                    refine ⟨232852351399830008501993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9935033659726080362751701 232852351399830008501993)
                    ·
                      rfl

theorem cell23_1360435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_1360435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360435 prefixEnd_1360435 := by exact prefixLift 1360435
  have htrace : WordTrace (prefixWord ++ tailWord_1360435) baseStart_1360435 baseEnd_1360435 := by
    simpa [prefixWord, tailWord_1360435, baseEnd_1360435] using wordTrace_append hprefix tailTrace_1360435
  have hstable : (prefixWord ++ tailWord_1360435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360435).length < 2 ^ (prefixWord ++ tailWord_1360435).sum := by decide
  have hdescent : baseEnd_1360435 < baseStart_1360435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360436 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1360436 : Nat := 118140960795 + 1360436 * 2 ^ 59
def prefixEnd_1360436 : Nat := 4983230072969 + 3 ^ 40 * 1360436 * 2
def baseEnd_1360436 : Nat := 698557567680144521593475

theorem tailTrace_1360436 : CollatzResearch.WordTrace tailWord_1360436 prefixEnd_1360436 698557567680144521593475 := by
  unfold tailWord_1360436
  simp only [CollatzResearch.WordTrace]
  refine ⟨24809588649690095408030581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33079451532920127210707441 24809588649690095408030581)
  ·
    refine ⟨2325898935908446444502867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24809588649690095408030581 2325898935908446444502867)
    ·
      refine ⟨3488848403862669666754301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325898935908446444502867 3488848403862669666754301)
      ·
        refine ⟨1308318151448501125032863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3488848403862669666754301 1308318151448501125032863)
        ·
          refine ⟨1962477227172751687549295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308318151448501125032863 1962477227172751687549295)
          ·
            refine ⟨2943715840759127531323943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962477227172751687549295 2943715840759127531323943)
            ·
              refine ⟨4415573761138691296985915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943715840759127531323943 4415573761138691296985915)
              ·
                refine ⟨6623360641708036945478873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415573761138691296985915 6623360641708036945478873)
                ·
                  refine ⟨4967520481281027709109155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623360641708036945478873 4967520481281027709109155)
                  ·
                    refine ⟨7451280721921541563663733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967520481281027709109155 7451280721921541563663733)
                    ·
                      refine ⟨698557567680144521593475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7451280721921541563663733 698557567680144521593475)
                      ·
                        rfl

theorem cell23_1360436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1360436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360436 prefixEnd_1360436 := by exact prefixLift 1360436
  have htrace : WordTrace (prefixWord ++ tailWord_1360436) baseStart_1360436 baseEnd_1360436 := by
    simpa [prefixWord, tailWord_1360436, baseEnd_1360436] using wordTrace_append hprefix tailTrace_1360436
  have hstable : (prefixWord ++ tailWord_1360436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360436).length < 2 ^ (prefixWord ++ tailWord_1360436).sum := by decide
  have hdescent : baseEnd_1360436 < baseStart_1360436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360492 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1360492 : Nat := 118140960795 + 1360492 * 2 ^ 59
def prefixEnd_1360492 : Nat := 4983230072969 + 3 ^ 40 * 1360492 * 2
def baseEnd_1360492 : Nat := 698586322596796302493217

theorem tailTrace_1360492 : CollatzResearch.WordTrace tailWord_1360492 prefixEnd_1360492 698586322596796302493217 := by
  unfold tailWord_1360492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24810609893588656190049865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33080813191451541586733153 24810609893588656190049865)
  ·
    refine ⟨18607957420191492142537399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24810609893588656190049865 18607957420191492142537399)
    ·
      refine ⟨27911936130287238213806099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18607957420191492142537399 27911936130287238213806099)
      ·
        refine ⟨41867904195430857320709149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27911936130287238213806099 41867904195430857320709149)
        ·
          refine ⟨15700464073286571495265931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41867904195430857320709149 15700464073286571495265931)
          ·
            refine ⟨23550696109929857242898897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15700464073286571495265931 23550696109929857242898897)
            ·
              refine ⟨17663022082447392932174173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23550696109929857242898897 17663022082447392932174173)
              ·
                refine ⟨6623633280917772349565315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17663022082447392932174173 6623633280917772349565315)
                ·
                  refine ⟨9935449921376658524347973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6623633280917772349565315 9935449921376658524347973)
                  ·
                    refine ⟨1862896860258123473315245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9935449921376658524347973 1862896860258123473315245)
                    ·
                      refine ⟨698586322596796302493217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1862896860258123473315245 698586322596796302493217)
                      ·
                        rfl

theorem cell23_1360492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1360492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360492 prefixEnd_1360492 := by exact prefixLift 1360492
  have htrace : WordTrace (prefixWord ++ tailWord_1360492) baseStart_1360492 baseEnd_1360492 := by
    simpa [prefixWord, tailWord_1360492, baseEnd_1360492] using wordTrace_append hprefix tailTrace_1360492
  have hstable : (prefixWord ++ tailWord_1360492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360492).length < 2 ^ (prefixWord ++ tailWord_1360492).sum := by decide
  have hdescent : baseEnd_1360492 < baseStart_1360492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360495 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 10]
def baseStart_1360495 : Nat := 118140960795 + 1360495 * 2 ^ 59
def prefixEnd_1360495 : Nat := 4983230072969 + 3 ^ 40 * 1360495 * 2
def baseEnd_1360495 : Nat := 77620873670973310083967

theorem tailTrace_1360495 : CollatzResearch.WordTrace tailWord_1360495 prefixEnd_1360495 77620873670973310083967 := by
  unfold tailWord_1360495
  simp only [CollatzResearch.WordTrace]
  refine ⟨49621329206166443892458939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33080886137444295928305959 49621329206166443892458939)
  ·
    refine ⟨74431993809249665838688409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49621329206166443892458939 74431993809249665838688409)
    ·
      refine ⟨55823995356937249379016307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74431993809249665838688409 55823995356937249379016307)
      ·
        refine ⟨83735993035405874068524461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55823995356937249379016307 83735993035405874068524461)
        ·
          refine ⟨31400997388277202775696673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83735993035405874068524461 31400997388277202775696673)
          ·
            refine ⟨23550748041207902081772505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31400997388277202775696673 23550748041207902081772505)
            ·
              refine ⟨17663061030905926561329379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23550748041207902081772505 17663061030905926561329379)
              ·
                refine ⟨26494591546358889841994069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17663061030905926561329379 26494591546358889841994069)
                ·
                  refine ⟨77620873670973310083967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26494591546358889841994069 77620873670973310083967)
                  ·
                    rfl

theorem cell23_1360495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 10].length) (baseStart_1360495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360495 prefixEnd_1360495 := by exact prefixLift 1360495
  have htrace : WordTrace (prefixWord ++ tailWord_1360495) baseStart_1360495 baseEnd_1360495 := by
    simpa [prefixWord, tailWord_1360495, baseEnd_1360495] using wordTrace_append hprefix tailTrace_1360495
  have hstable : (prefixWord ++ tailWord_1360495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360495).length < 2 ^ (prefixWord ++ tailWord_1360495).sum := by decide
  have hdescent : baseEnd_1360495 < baseStart_1360495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360512 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 6]
def baseStart_1360512 : Nat := 118140960795 + 1360512 * 2 ^ 59
def prefixEnd_1360512 : Nat := 4983230072969 + 3 ^ 40 * 1360512 * 2
def baseEnd_1360512 : Nat := 77621843578876247138125

theorem tailTrace_1360512 : CollatzResearch.WordTrace tailWord_1360512 prefixEnd_1360512 77621843578876247138125 := by
  unfold tailWord_1360512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24810974623552427897913895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33081299498069903863885193 24810974623552427897913895)
  ·
    refine ⟨37216461935328641846870843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24810974623552427897913895 37216461935328641846870843)
    ·
      refine ⟨55824692902992962770306265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37216461935328641846870843 55824692902992962770306265)
      ·
        refine ⟨41868519677244722077729699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55824692902992962770306265 41868519677244722077729699)
        ·
          refine ⟨62802779515867083116594549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41868519677244722077729699 62802779515867083116594549)
          ·
            refine ⟨5887760579612539042180739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62802779515867083116594549 5887760579612539042180739)
            ·
              refine ⟨8831640869418808563271109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887760579612539042180739 8831640869418808563271109)
              ·
                refine ⟨1655932663016026605613333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8831640869418808563271109 1655932663016026605613333)
                ·
                  refine ⟨77621843578876247138125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1655932663016026605613333 77621843578876247138125)
                  ·
                    rfl

theorem cell23_1360512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_1360512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360512 prefixEnd_1360512 := by exact prefixLift 1360512
  have htrace : WordTrace (prefixWord ++ tailWord_1360512) baseStart_1360512 baseEnd_1360512 := by
    simpa [prefixWord, tailWord_1360512, baseEnd_1360512] using wordTrace_append hprefix tailTrace_1360512
  have hstable : (prefixWord ++ tailWord_1360512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360512).length < 2 ^ (prefixWord ++ tailWord_1360512).sum := by decide
  have hdescent : baseEnd_1360512 < baseStart_1360512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360559 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 1, 5]
def baseStart_1360559 : Nat := 118140960795 + 1360559 * 2 ^ 59
def prefixEnd_1360559 : Nat := 4983230072969 + 3 ^ 40 * 1360559 * 2
def baseEnd_1360559 : Nat := 232873575266882513451803

theorem tailTrace_1360559 : CollatzResearch.WordTrace tailWord_1360559 prefixEnd_1360559 232873575266882513451803 := by
  unfold tailWord_1360559
  simp only [CollatzResearch.WordTrace]
  refine ⟨49623663477934582822788731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33082442318623055215192487 49623663477934582822788731)
  ·
    refine ⟨74435495216901874234183097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49623663477934582822788731 74435495216901874234183097)
    ·
      refine ⟨55826621412676405675637323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74435495216901874234183097 55826621412676405675637323)
      ·
        refine ⟨83739932119014608513455985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55826621412676405675637323 83739932119014608513455985)
        ·
          refine ⟨62804949089260956385091989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83739932119014608513455985 62804949089260956385091989)
          ·
            refine ⟨2943981988559107330551187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62804949089260956385091989 2943981988559107330551187)
            ·
              refine ⟨4415972982838660995826781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943981988559107330551187 4415972982838660995826781)
              ·
                refine ⟨1655989868564497873435043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4415972982838660995826781 1655989868564497873435043)
                ·
                  refine ⟨2483984802846746810152565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655989868564497873435043 2483984802846746810152565)
                  ·
                    refine ⟨232873575266882513451803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2483984802846746810152565 232873575266882513451803)
                    ·
                      rfl

theorem cell23_1360559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_1360559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360559 prefixEnd_1360559 := by exact prefixLift 1360559
  have htrace : WordTrace (prefixWord ++ tailWord_1360559) baseStart_1360559 baseEnd_1360559 := by
    simpa [prefixWord, tailWord_1360559, baseEnd_1360559] using wordTrace_append hprefix tailTrace_1360559
  have hstable : (prefixWord ++ tailWord_1360559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360559).length < 2 ^ (prefixWord ++ tailWord_1360559).sum := by decide
  have hdescent : baseEnd_1360559 < baseStart_1360559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360573 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_1360573 : Nat := 118140960795 + 1360573 * 2 ^ 59
def prefixEnd_1360573 : Nat := 4983230072969 + 3 ^ 40 * 1360573 * 2
def baseEnd_1360573 : Nat := 698627914529810485580345

theorem tailTrace_1360573 : CollatzResearch.WordTrace tailWord_1360573 prefixEnd_1360573 698627914529810485580345 := by
  unfold tailWord_1360573
  simp only [CollatzResearch.WordTrace]
  refine ⟨49624174099883863213798373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33082782733255908809198915 49624174099883863213798373)
  ·
    refine ⟨9304532643728224352587195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49624174099883863213798373 9304532643728224352587195)
    ·
      refine ⟨13956798965592336528880793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9304532643728224352587195 13956798965592336528880793)
      ·
        refine ⟨10467599224194252396660595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13956798965592336528880793 10467599224194252396660595)
        ·
          refine ⟨15701398836291378594990893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467599224194252396660595 15701398836291378594990893)
          ·
            refine ⟨5888024563609266973121585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15701398836291378594990893 5888024563609266973121585)
            ·
              refine ⟨4416018422706950229841189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888024563609266973121585 4416018422706950229841189)
              ·
                refine ⟨828003454257553168095223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4416018422706950229841189 828003454257553168095223)
                ·
                  refine ⟨1242005181386329752142835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828003454257553168095223 1242005181386329752142835)
                  ·
                    refine ⟨1863007772079494628214253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1242005181386329752142835 1863007772079494628214253)
                    ·
                      refine ⟨698627914529810485580345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1863007772079494628214253 698627914529810485580345)
                      ·
                        rfl

theorem cell23_1360573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_1360573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360573 prefixEnd_1360573 := by exact prefixLift 1360573
  have htrace : WordTrace (prefixWord ++ tailWord_1360573) baseStart_1360573 baseEnd_1360573 := by
    simpa [prefixWord, tailWord_1360573, baseEnd_1360573] using wordTrace_append hprefix tailTrace_1360573
  have hstable : (prefixWord ++ tailWord_1360573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360573).length < 2 ^ (prefixWord ++ tailWord_1360573).sum := by decide
  have hdescent : baseEnd_1360573 < baseStart_1360573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360602 : List Nat := [3, 1, 1, 2, 2, 2, 3, 9]
def baseStart_1360602 : Nat := 118140960795 + 1360602 * 2 ^ 59
def prefixEnd_1360602 : Nat := 4983230072969 + 3 ^ 40 * 1360602 * 2
def baseEnd_1360602 : Nat := 25875659461807069337693

theorem tailTrace_1360602 : CollatzResearch.WordTrace tailWord_1360602 prefixEnd_1360602 25875659461807069337693 := by
  unfold tailWord_1360602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12406307954194700291651015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33083487877852534111069373 12406307954194700291651015)
  ·
    refine ⟨18609461931292050437476523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12406307954194700291651015 18609461931292050437476523)
    ·
      refine ⟨27914192896938075656214785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18609461931292050437476523 27914192896938075656214785)
      ·
        refine ⟨20935644672703556742161089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27914192896938075656214785 20935644672703556742161089)
        ·
          refine ⟨15701733504527667556620817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20935644672703556742161089 15701733504527667556620817)
          ·
            refine ⟨11776300128395750667465613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15701733504527667556620817 11776300128395750667465613)
            ·
              refine ⟨4416112548148406500299605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11776300128395750667465613 4416112548148406500299605)
              ·
                refine ⟨25875659461807069337693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4416112548148406500299605 25875659461807069337693)
                ·
                  rfl

theorem cell23_1360602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_1360602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360602 prefixEnd_1360602 := by exact prefixLift 1360602
  have htrace : WordTrace (prefixWord ++ tailWord_1360602) baseStart_1360602 baseEnd_1360602 := by
    simpa [prefixWord, tailWord_1360602, baseEnd_1360602] using wordTrace_append hprefix tailTrace_1360602
  have hstable : (prefixWord ++ tailWord_1360602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360602).length < 2 ^ (prefixWord ++ tailWord_1360602).sum := by decide
  have hdescent : baseEnd_1360602 < baseStart_1360602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360616 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1360616 : Nat := 118140960795 + 1360616 * 2 ^ 59
def prefixEnd_1360616 : Nat := 4983230072969 + 3 ^ 40 * 1360616 * 2
def baseEnd_1360616 : Nat := 698649994197953817342647

theorem tailTrace_1360616 : CollatzResearch.WordTrace tailWord_1360616 prefixEnd_1360616 698649994197953817342647 := by
  unfold tailWord_1360616
  simp only [CollatzResearch.WordTrace]
  refine ⟨24812871219364040778806851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33083828292485387705075801 24812871219364040778806851)
  ·
    refine ⟨37219306829046061168210277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24812871219364040778806851 37219306829046061168210277)
    ·
      refine ⟨6978620030446136469039427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37219306829046061168210277 6978620030446136469039427)
      ·
        refine ⟨10467930045669204703559141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6978620030446136469039427 10467930045669204703559141)
        ·
          refine ⟨1962736883562975881917339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10467930045669204703559141 1962736883562975881917339)
          ·
            refine ⟨2944105325344463822876009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962736883562975881917339 2944105325344463822876009)
            ·
              refine ⟨2208078994008347867157007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944105325344463822876009 2208078994008347867157007)
              ·
                refine ⟨3312118491012521800735511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208078994008347867157007 3312118491012521800735511)
                ·
                  refine ⟨4968177736518782701103267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312118491012521800735511 4968177736518782701103267)
                  ·
                    refine ⟨7452266604778174051654901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4968177736518782701103267 7452266604778174051654901)
                    ·
                      refine ⟨698649994197953817342647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7452266604778174051654901 698649994197953817342647)
                      ·
                        rfl

theorem cell23_1360616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1360616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360616 prefixEnd_1360616 := by exact prefixLift 1360616
  have htrace : WordTrace (prefixWord ++ tailWord_1360616) baseStart_1360616 baseEnd_1360616 := by
    simpa [prefixWord, tailWord_1360616, baseEnd_1360616] using wordTrace_append hprefix tailTrace_1360616
  have hstable : (prefixWord ++ tailWord_1360616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360616).length < 2 ^ (prefixWord ++ tailWord_1360616).sum := by decide
  have hdescent : baseEnd_1360616 < baseStart_1360616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360632 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_1360632 : Nat := 118140960795 + 1360632 * 2 ^ 59
def prefixEnd_1360632 : Nat := 4983230072969 + 3 ^ 40 * 1360632 * 2
def baseEnd_1360632 : Nat := 232886069962808584914191

theorem tailTrace_1360632 : CollatzResearch.WordTrace tailWord_1360632 prefixEnd_1360632 232886069962808584914191 := by
  unfold tailWord_1360632
  simp only [CollatzResearch.WordTrace]
  refine ⟨24813163003335058145098075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33084217337780077526797433 24813163003335058145098075)
  ·
    refine ⟨37219744505002587217647113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24813163003335058145098075 37219744505002587217647113)
    ·
      refine ⟨27914808378751940413235335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37219744505002587217647113 27914808378751940413235335)
      ·
        refine ⟨41872212568127910619853003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27914808378751940413235335 41872212568127910619853003)
        ·
          refine ⟨62808318852191865929779505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41872212568127910619853003 62808318852191865929779505)
          ·
            refine ⟨47106239139143899447334629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62808318852191865929779505 47106239139143899447334629)
            ·
              refine ⟨8832419838589481146375243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47106239139143899447334629 8832419838589481146375243)
              ·
                refine ⟨13248629757884221719562865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8832419838589481146375243 13248629757884221719562865)
                ·
                  refine ⟨9936472318413166289672149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13248629757884221719562865 9936472318413166289672149)
                  ·
                    refine ⟨232886069962808584914191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9936472318413166289672149 232886069962808584914191)
                    ·
                      rfl

theorem cell23_1360632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_1360632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360632 prefixEnd_1360632 := by exact prefixLift 1360632
  have htrace : WordTrace (prefixWord ++ tailWord_1360632) baseStart_1360632 baseEnd_1360632 := by
    simpa [prefixWord, tailWord_1360632, baseEnd_1360632] using wordTrace_append hprefix tailTrace_1360632
  have hstable : (prefixWord ++ tailWord_1360632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360632).length < 2 ^ (prefixWord ++ tailWord_1360632).sum := by decide
  have hdescent : baseEnd_1360632 < baseStart_1360632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360639 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 7, 2]
def baseStart_1360639 : Nat := 118140960795 + 1360639 * 2 ^ 59
def prefixEnd_1360639 : Nat := 4983230072969 + 3 ^ 40 * 1360639 * 2
def baseEnd_1360639 : Nat := 698661804253007227355041

theorem tailTrace_1360639 : CollatzResearch.WordTrace tailWord_1360639 prefixEnd_1360639 698661804253007227355041 := by
  unfold tailWord_1360639
  simp only [CollatzResearch.WordTrace]
  refine ⟨49626581317644756485700971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33084387545096504323800647 49626581317644756485700971)
  ·
    refine ⟨74439871976467134728551457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49626581317644756485700971 74439871976467134728551457)
    ·
      refine ⟨55829903982350351046413593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74439871976467134728551457 55829903982350351046413593)
      ·
        refine ⟨41872427986762763284810195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55829903982350351046413593 41872427986762763284810195)
        ·
          refine ⟨62808641980144144927215293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41872427986762763284810195 62808641980144144927215293)
          ·
            refine ⟨23553240742554054347705735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62808641980144144927215293 23553240742554054347705735)
            ·
              refine ⟨35329861113831081521558603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23553240742554054347705735 35329861113831081521558603)
              ·
                refine ⟨52994791670746622282337905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35329861113831081521558603 52994791670746622282337905)
                ·
                  refine ⟨39746093753059966711753429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52994791670746622282337905 39746093753059966711753429)
                  ·
                    refine ⟨931549072337342969806721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39746093753059966711753429 931549072337342969806721)
                    ·
                      refine ⟨698661804253007227355041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931549072337342969806721 698661804253007227355041)
                      ·
                        rfl

theorem cell23_1360639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_1360639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360639 prefixEnd_1360639 := by exact prefixLift 1360639
  have htrace : WordTrace (prefixWord ++ tailWord_1360639) baseStart_1360639 baseEnd_1360639 := by
    simpa [prefixWord, tailWord_1360639, baseEnd_1360639] using wordTrace_append hprefix tailTrace_1360639
  have hstable : (prefixWord ++ tailWord_1360639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360639).length < 2 ^ (prefixWord ++ tailWord_1360639).sum := by decide
  have hdescent : baseEnd_1360639 < baseStart_1360639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360652 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1360652 : Nat := 118140960795 + 1360652 * 2 ^ 59
def prefixEnd_1360652 : Nat := 4983230072969 + 3 ^ 40 * 1360652 * 2
def baseEnd_1360652 : Nat := 698668479501515676492481

theorem tailTrace_1360652 : CollatzResearch.WordTrace tailWord_1360652 prefixEnd_1360652 698668479501515676492481 := by
  unfold tailWord_1360652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24813527733298829852962105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33084703644398439803949473 24813527733298829852962105)
  ·
    refine ⟨18610145799974122389721579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24813527733298829852962105 18610145799974122389721579)
    ·
      refine ⟨27915218699961183584582369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18610145799974122389721579 27915218699961183584582369)
      ·
        refine ⟨20936414024970887688436777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27915218699961183584582369 20936414024970887688436777)
        ·
          refine ⟨15702310518728165766327583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20936414024970887688436777 15702310518728165766327583)
          ·
            refine ⟨23553465778092248649491375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15702310518728165766327583 23553465778092248649491375)
            ·
              refine ⟨35330198667138372974237063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23553465778092248649491375 35330198667138372974237063)
              ·
                refine ⟨52995298000707559461355595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35330198667138372974237063 52995298000707559461355595)
                ·
                  refine ⟨79492947001061339192033393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52995298000707559461355595 79492947001061339192033393)
                  ·
                    refine ⟨59619710250796004394025045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79492947001061339192033393 59619710250796004394025045)
                    ·
                      refine ⟨698668479501515676492481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 59619710250796004394025045 698668479501515676492481)
                      ·
                        rfl

theorem cell23_1360652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1360652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360652 prefixEnd_1360652 := by exact prefixLift 1360652
  have htrace : WordTrace (prefixWord ++ tailWord_1360652) baseStart_1360652 baseEnd_1360652 := by
    simpa [prefixWord, tailWord_1360652, baseEnd_1360652] using wordTrace_append hprefix tailTrace_1360652
  have hstable : (prefixWord ++ tailWord_1360652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360652).length < 2 ^ (prefixWord ++ tailWord_1360652).sum := by decide
  have hdescent : baseEnd_1360652 < baseStart_1360652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360686 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1360686 : Nat := 118140960795 + 1360686 * 2 ^ 59
def prefixEnd_1360686 : Nat := 4983230072969 + 3 ^ 40 * 1360686 * 2
def baseEnd_1360686 : Nat := 698685937843768543467325

theorem tailTrace_1360686 : CollatzResearch.WordTrace tailWord_1360686 prefixEnd_1360686 698685937843768543467325 := by
  unfold tailWord_1360686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203536943559310439082739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33085530365649655675107941 6203536943559310439082739)
  ·
    refine ⟨9305305415338965658624109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6203536943559310439082739 9305305415338965658624109)
    ·
      refine ⟨3489489530752112121984041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9305305415338965658624109 3489489530752112121984041)
      ·
        refine ⟨2617117148064084091488031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3489489530752112121984041 2617117148064084091488031)
        ·
          refine ⟨3925675722096126137232047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617117148064084091488031 3925675722096126137232047)
          ·
            refine ⟨5888513583144189205848071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925675722096126137232047 5888513583144189205848071)
            ·
              refine ⟨8832770374716283808772107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888513583144189205848071 8832770374716283808772107)
              ·
                refine ⟨13249155562074425713158161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8832770374716283808772107 13249155562074425713158161)
                ·
                  refine ⟨9936866671555819284868621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13249155562074425713158161 9936866671555819284868621)
                  ·
                    refine ⟨3726325001833432231825733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9936866671555819284868621 3726325001833432231825733)
                    ·
                      refine ⟨698685937843768543467325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3726325001833432231825733 698685937843768543467325)
                      ·
                        rfl

theorem cell23_1360686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1360686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360686 prefixEnd_1360686 := by exact prefixLift 1360686
  have htrace : WordTrace (prefixWord ++ tailWord_1360686) baseStart_1360686 baseEnd_1360686 := by
    simpa [prefixWord, tailWord_1360686, baseEnd_1360686] using wordTrace_append hprefix tailTrace_1360686
  have hstable : (prefixWord ++ tailWord_1360686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360686).length < 2 ^ (prefixWord ++ tailWord_1360686).sum := by decide
  have hdescent : baseEnd_1360686 < baseStart_1360686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360689 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1360689 : Nat := 118140960795 + 1360689 * 2 ^ 59
def prefixEnd_1360689 : Nat := 4983230072969 + 3 ^ 40 * 1360689 * 2
def baseEnd_1360689 : Nat := 698687478285732031729811

theorem tailTrace_1360689 : CollatzResearch.WordTrace tailWord_1360689 prefixEnd_1360689 698687478285732031729811 := by
  unfold tailWord_1360689
  simp only [CollatzResearch.WordTrace]
  refine ⟨49628404967463615025021121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33085603311642410016680747 49628404967463615025021121)
  ·
    refine ⟨37221303725597711268765841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49628404967463615025021121 37221303725597711268765841)
    ·
      refine ⟨27915977794198283451574381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37221303725597711268765841 27915977794198283451574381)
      ·
        refine ⟨10468491672824356294340393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27915977794198283451574381 10468491672824356294340393)
        ·
          refine ⟨7851368754618267220755295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10468491672824356294340393 7851368754618267220755295)
          ·
            refine ⟨11777053131927400831132943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851368754618267220755295 11777053131927400831132943)
            ·
              refine ⟨17665579697891101246699415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777053131927400831132943 17665579697891101246699415)
              ·
                refine ⟨26498369546836651870049123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17665579697891101246699415 26498369546836651870049123)
                ·
                  refine ⟨39747554320254977805073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26498369546836651870049123 39747554320254977805073685)
                  ·
                    refine ⟨1863166608761952084612829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39747554320254977805073685 1863166608761952084612829)
                    ·
                      refine ⟨698687478285732031729811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1863166608761952084612829 698687478285732031729811)
                      ·
                        rfl

theorem cell23_1360689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1360689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360689 prefixEnd_1360689 := by exact prefixLift 1360689
  have htrace : WordTrace (prefixWord ++ tailWord_1360689) baseStart_1360689 baseEnd_1360689 := by
    simpa [prefixWord, tailWord_1360689, baseEnd_1360689] using wordTrace_append hprefix tailTrace_1360689
  have hstable : (prefixWord ++ tailWord_1360689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360689).length < 2 ^ (prefixWord ++ tailWord_1360689).sum := by decide
  have hdescent : baseEnd_1360689 < baseStart_1360689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360703 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 1, 4, 2]
def baseStart_1360703 : Nat := 118140960795 + 1360703 * 2 ^ 59
def prefixEnd_1360703 : Nat := 4983230072969 + 3 ^ 40 * 1360703 * 2
def baseEnd_1360703 : Nat := 698694667014894976954747

theorem tailTrace_1360703 : CollatzResearch.WordTrace tailWord_1360703 prefixEnd_1360703 698694667014894976954747 := by
  unfold tailWord_1360703
  simp only [CollatzResearch.WordTrace]
  refine ⟨49628915589412895416030763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33085943726275263610687175 49628915589412895416030763)
  ·
    refine ⟨74443373384119343124046145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49628915589412895416030763 74443373384119343124046145)
    ·
      refine ⟨55832530038089507343034609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74443373384119343124046145 55832530038089507343034609)
      ·
        refine ⟨41874397528567130507275957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55832530038089507343034609 41874397528567130507275957)
        ·
          refine ⟨3925724768303168485057121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41874397528567130507275957 3925724768303168485057121)
          ·
            refine ⟨2944293576227376363792841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3925724768303168485057121 2944293576227376363792841)
            ·
              refine ⟨2208220182170532272844631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944293576227376363792841 2208220182170532272844631)
              ·
                refine ⟨3312330273255798409266947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208220182170532272844631 3312330273255798409266947)
                ·
                  refine ⟨4968495409883697613900421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312330273255798409266947 4968495409883697613900421)
                  ·
                    refine ⟨931592889353193302606329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4968495409883697613900421 931592889353193302606329)
                    ·
                      refine ⟨698694667014894976954747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931592889353193302606329 698694667014894976954747)
                      ·
                        rfl

theorem cell23_1360703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_1360703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360703 prefixEnd_1360703 := by exact prefixLift 1360703
  have htrace : WordTrace (prefixWord ++ tailWord_1360703) baseStart_1360703 baseEnd_1360703 := by
    simpa [prefixWord, tailWord_1360703, baseEnd_1360703] using wordTrace_append hprefix tailTrace_1360703
  have hstable : (prefixWord ++ tailWord_1360703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360703).length < 2 ^ (prefixWord ++ tailWord_1360703).sum := by decide
  have hdescent : baseEnd_1360703 < baseStart_1360703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360724 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_1360724 : Nat := 118140960795 + 1360724 * 2 ^ 59
def prefixEnd_1360724 : Nat := 4983230072969 + 3 ^ 40 * 1360724 * 2
def baseEnd_1360724 : Nat := 698705450108639394792151

theorem tailTrace_1360724 : CollatzResearch.WordTrace tailWord_1360724 prefixEnd_1360724 698705450108639394792151 := by
  unfold tailWord_1360724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24814840761168408001272613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33086454348224544001696817 24814840761168408001272613)
  ·
    refine ⟨4652782642719076500238615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24814840761168408001272613 4652782642719076500238615)
    ·
      refine ⟨6979173964078614750357923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652782642719076500238615 6979173964078614750357923)
      ·
        refine ⟨10468760946117922125536885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979173964078614750357923 10468760946117922125536885)
        ·
          refine ⟨981446338698555199269083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10468760946117922125536885 981446338698555199269083)
          ·
            refine ⟨1472169508047832798903625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981446338698555199269083 1472169508047832798903625)
            ·
              refine ⟨1104127131035874599177719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472169508047832798903625 1104127131035874599177719)
              ·
                refine ⟨1656190696553811898766579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104127131035874599177719 1656190696553811898766579)
                ·
                  refine ⟨2484286044830717848149869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656190696553811898766579 2484286044830717848149869)
                  ·
                    refine ⟨931607266811519193056201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484286044830717848149869 931607266811519193056201)
                    ·
                      refine ⟨698705450108639394792151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931607266811519193056201 698705450108639394792151)
                      ·
                        rfl

theorem cell23_1360724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_1360724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360724 prefixEnd_1360724 := by exact prefixLift 1360724
  have htrace : WordTrace (prefixWord ++ tailWord_1360724) baseStart_1360724 baseEnd_1360724 := by
    simpa [prefixWord, tailWord_1360724, baseEnd_1360724] using wordTrace_append hprefix tailTrace_1360724
  have hstable : (prefixWord ++ tailWord_1360724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360724).length < 2 ^ (prefixWord ++ tailWord_1360724).sum := by decide
  have hdescent : baseEnd_1360724 < baseStart_1360724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360749 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1360749 : Nat := 118140960795 + 1360749 * 2 ^ 59
def prefixEnd_1360749 : Nat := 4983230072969 + 3 ^ 40 * 1360749 * 2
def baseEnd_1360749 : Nat := 698718287125001796979535

theorem tailTrace_1360749 : CollatzResearch.WordTrace tailWord_1360749 prefixEnd_1360749 698718287125001796979535 := by
  unfold tailWord_1360749
  simp only [CollatzResearch.WordTrace]
  refine ⟨49630593347246245272205301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33087062231497496848136867 49630593347246245272205301)
  ·
    refine ⟨4652868126304335494269247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49630593347246245272205301 4652868126304335494269247)
    ·
      refine ⟨6979302189456503241403871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652868126304335494269247 6979302189456503241403871)
      ·
        refine ⟨10468953284184754862105807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979302189456503241403871 10468953284184754862105807)
        ·
          refine ⟨15703429926277132293158711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10468953284184754862105807 15703429926277132293158711)
          ·
            refine ⟨23555144889415698439738067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15703429926277132293158711 23555144889415698439738067)
            ·
              refine ⟨35332717334123547659607101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23555144889415698439738067 35332717334123547659607101)
              ·
                refine ⟨13249769000296330372352663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35332717334123547659607101 13249769000296330372352663)
                ·
                  refine ⟨19874653500444495558528995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13249769000296330372352663 19874653500444495558528995)
                  ·
                    refine ⟨29811980250666743337793493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19874653500444495558528995 29811980250666743337793493)
                    ·
                      refine ⟨698718287125001796979535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29811980250666743337793493 698718287125001796979535)
                      ·
                        rfl

theorem cell23_1360749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1360749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360749 prefixEnd_1360749 := by exact prefixLift 1360749
  have htrace : WordTrace (prefixWord ++ tailWord_1360749) baseStart_1360749 baseEnd_1360749 := by
    simpa [prefixWord, tailWord_1360749, baseEnd_1360749] using wordTrace_append hprefix tailTrace_1360749
  have hstable : (prefixWord ++ tailWord_1360749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360749).length < 2 ^ (prefixWord ++ tailWord_1360749).sum := by decide
  have hdescent : baseEnd_1360749 < baseStart_1360749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360776 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1360776 : Nat := 118140960795 + 1360776 * 2 ^ 59
def prefixEnd_1360776 : Nat := 4983230072969 + 3 ^ 40 * 1360776 * 2
def baseEnd_1360776 : Nat := 698732151102673191341911

theorem tailTrace_1360776 : CollatzResearch.WordTrace tailWord_1360776 prefixEnd_1360776 698732151102673191341911 := by
  unfold tailWord_1360776
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815789059074214441719091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33087718745432285922292121 24815789059074214441719091)
  ·
    refine ⟨37223683588611321662578637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24815789059074214441719091 37223683588611321662578637)
    ·
      refine ⟨13958881345729245623466989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37223683588611321662578637 13958881345729245623466989)
      ·
        refine ⟨5234580504648467108800121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13958881345729245623466989 5234580504648467108800121)
        ·
          refine ⟨3925935378486350331600091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234580504648467108800121 3925935378486350331600091)
          ·
            refine ⟨5888903067729525497400137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925935378486350331600091 5888903067729525497400137)
            ·
              refine ⟨4416677300797144123050103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888903067729525497400137 4416677300797144123050103)
              ·
                refine ⟨6625015951195716184575155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416677300797144123050103 6625015951195716184575155)
                ·
                  refine ⟨9937523926793574276862733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6625015951195716184575155 9937523926793574276862733)
                  ·
                    refine ⟨3726571472547590353823525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9937523926793574276862733 3726571472547590353823525)
                    ·
                      refine ⟨698732151102673191341911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3726571472547590353823525 698732151102673191341911)
                      ·
                        rfl

theorem cell23_1360776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1360776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360776 prefixEnd_1360776 := by exact prefixLift 1360776
  have htrace : WordTrace (prefixWord ++ tailWord_1360776) baseStart_1360776 baseEnd_1360776 := by
    simpa [prefixWord, tailWord_1360776, baseEnd_1360776] using wordTrace_append hprefix tailTrace_1360776
  have hstable : (prefixWord ++ tailWord_1360776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360776).length < 2 ^ (prefixWord ++ tailWord_1360776).sum := by decide
  have hdescent : baseEnd_1360776 < baseStart_1360776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360790 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1360790 : Nat := 118140960795 + 1360790 * 2 ^ 59
def prefixEnd_1360790 : Nat := 4983230072969 + 3 ^ 40 * 1360790 * 2
def baseEnd_1360790 : Nat := 232913113277278712188949

theorem tailTrace_1360790 : CollatzResearch.WordTrace tailWord_1360790 prefixEnd_1360790 232913113277278712188949 := by
  unfold tailWord_1360790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102005546256106829652989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33088059160065139516298549 3102005546256106829652989)
  ·
    refine ⟨1163252079846040061119871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3102005546256106829652989 1163252079846040061119871)
    ·
      refine ⟨1744878119769060091679807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163252079846040061119871 1744878119769060091679807)
      ·
        refine ⟨2617317179653590137519711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744878119769060091679807 2617317179653590137519711)
        ·
          refine ⟨3925975769480385206279567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617317179653590137519711 3925975769480385206279567)
          ·
            refine ⟨5888963654220577809419351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925975769480385206279567 5888963654220577809419351)
            ·
              refine ⟨8833445481330866714129027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888963654220577809419351 8833445481330866714129027)
              ·
                refine ⟨13250168221996300071193541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8833445481330866714129027 13250168221996300071193541)
                ·
                  refine ⟨2484406541624306263348789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13250168221996300071193541 2484406541624306263348789)
                  ·
                    refine ⟨232913113277278712188949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2484406541624306263348789 232913113277278712188949)
                    ·
                      rfl

theorem cell23_1360790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1360790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360790 prefixEnd_1360790 := by exact prefixLift 1360790
  have htrace : WordTrace (prefixWord ++ tailWord_1360790) baseStart_1360790 baseEnd_1360790 := by
    simpa [prefixWord, tailWord_1360790, baseEnd_1360790] using wordTrace_append hprefix tailTrace_1360790
  have hstable : (prefixWord ++ tailWord_1360790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360790).length < 2 ^ (prefixWord ++ tailWord_1360790).sum := by decide
  have hdescent : baseEnd_1360790 < baseStart_1360790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360803 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 1, 4]
def baseStart_1360803 : Nat := 118140960795 + 1360803 * 2 ^ 59
def prefixEnd_1360803 : Nat := 4983230072969 + 3 ^ 40 * 1360803 * 2
def baseEnd_1360803 : Nat := 232915338360114861901429

theorem tailTrace_1360803 : CollatzResearch.WordTrace tailWord_1360803 prefixEnd_1360803 232915338360114861901429 := by
  unfold tailWord_1360803
  simp only [CollatzResearch.WordTrace]
  refine ⟨49632562889050612494671063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33088375259367074996447375 49632562889050612494671063)
  ·
    refine ⟨74448844333575918742006595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49632562889050612494671063 74448844333575918742006595)
    ·
      refine ⟨111673266500363878113009893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74448844333575918742006595 111673266500363878113009893)
      ·
        refine ⟨20938737468818227146189355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111673266500363878113009893 20938737468818227146189355)
        ·
          refine ⟨31408106203227340719284033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20938737468818227146189355 31408106203227340719284033)
          ·
            refine ⟨23556079652420505539463025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31408106203227340719284033 23556079652420505539463025)
            ·
              refine ⟨17667059739315379154597269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23556079652420505539463025 17667059739315379154597269)
              ·
                refine ⟨828143425280408397871747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17667059739315379154597269 828143425280408397871747)
                ·
                  refine ⟨1242215137920612596807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828143425280408397871747 1242215137920612596807621)
                  ·
                    refine ⟨232915338360114861901429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242215137920612596807621 232915338360114861901429)
                    ·
                      rfl

theorem cell23_1360803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 4].length) (baseStart_1360803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360803 prefixEnd_1360803 := by exact prefixLift 1360803
  have htrace : WordTrace (prefixWord ++ tailWord_1360803) baseStart_1360803 baseEnd_1360803 := by
    simpa [prefixWord, tailWord_1360803, baseEnd_1360803] using wordTrace_append hprefix tailTrace_1360803
  have hstable : (prefixWord ++ tailWord_1360803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360803).length < 2 ^ (prefixWord ++ tailWord_1360803).sum := by decide
  have hdescent : baseEnd_1360803 < baseStart_1360803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360854 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1360854 : Nat := 118140960795 + 1360854 * 2 ^ 59
def prefixEnd_1360854 : Nat := 4983230072969 + 3 ^ 40 * 1360854 * 2
def baseEnd_1360854 : Nat := 232924067531241295388851

theorem tailTrace_1360854 : CollatzResearch.WordTrace tailWord_1360854 prefixEnd_1360854 232924067531241295388851 := by
  unfold tailWord_1360854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102151438241615512798601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33089615341243898803185077 3102151438241615512798601)
  ·
    refine ⟨2326613578681211634598951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3102151438241615512798601 2326613578681211634598951)
    ·
      refine ⟨3489920368021817451898427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326613578681211634598951 3489920368021817451898427)
      ·
        refine ⟨5234880552032726177847641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489920368021817451898427 5234880552032726177847641)
        ·
          refine ⟨3926160414024544633385731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234880552032726177847641 3926160414024544633385731)
          ·
            refine ⟨5889240621036816950078597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926160414024544633385731 5889240621036816950078597)
            ·
              refine ⟨1104232616444403178139737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5889240621036816950078597 1104232616444403178139737)
              ·
                refine ⟨828174462333302383604803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104232616444403178139737 828174462333302383604803)
                ·
                  refine ⟨1242261693499953575407205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828174462333302383604803 1242261693499953575407205)
                  ·
                    refine ⟨232924067531241295388851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242261693499953575407205 232924067531241295388851)
                    ·
                      rfl

theorem cell23_1360854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1360854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360854 prefixEnd_1360854 := by exact prefixLift 1360854
  have htrace : WordTrace (prefixWord ++ tailWord_1360854) baseStart_1360854 baseEnd_1360854 := by
    simpa [prefixWord, tailWord_1360854, baseEnd_1360854] using wordTrace_append hprefix tailTrace_1360854
  have hstable : (prefixWord ++ tailWord_1360854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360854).length < 2 ^ (prefixWord ++ tailWord_1360854).sum := by decide
  have hdescent : baseEnd_1360854 < baseStart_1360854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360876 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_1360876 : Nat := 118140960795 + 1360876 * 2 ^ 59
def prefixEnd_1360876 : Nat := 4983230072969 + 3 ^ 40 * 1360876 * 2
def baseEnd_1360876 : Nat := 232927833056040933363817

theorem tailTrace_1360876 : CollatzResearch.WordTrace tailWord_1360876 prefixEnd_1360876 232927833056040933363817 := by
  unfold tailWord_1360876
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817612708893072981039241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33090150278524097308052321 24817612708893072981039241)
  ·
    refine ⟨18613209531669804735779431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24817612708893072981039241 18613209531669804735779431)
    ·
      refine ⟨27919814297504707103669147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18613209531669804735779431 27919814297504707103669147)
      ·
        refine ⟨41879721446257060655503721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27919814297504707103669147 41879721446257060655503721)
        ·
          refine ⟨31409791084692795491627791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41879721446257060655503721 31409791084692795491627791)
          ·
            refine ⟨47114686627039193237441687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31409791084692795491627791 47114686627039193237441687)
            ·
              refine ⟨70672029940558789856162531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47114686627039193237441687 70672029940558789856162531)
              ·
                refine ⟨106008044910838184784243797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70672029940558789856162531 106008044910838184784243797)
                ·
                  refine ⟨1242281776298884977940357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 106008044910838184784243797 1242281776298884977940357)
                  ·
                    refine ⟨232927833056040933363817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242281776298884977940357 232927833056040933363817)
                    ·
                      rfl

theorem cell23_1360876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_1360876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360876 prefixEnd_1360876 := by exact prefixLift 1360876
  have htrace : WordTrace (prefixWord ++ tailWord_1360876) baseStart_1360876 baseEnd_1360876 := by
    simpa [prefixWord, tailWord_1360876, baseEnd_1360876] using wordTrace_append hprefix tailTrace_1360876
  have hstable : (prefixWord ++ tailWord_1360876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360876).length < 2 ^ (prefixWord ++ tailWord_1360876).sum := by decide
  have hdescent : baseEnd_1360876 < baseStart_1360876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360906 : List Nat := [3, 1, 2, 2, 3, 2, 10]
def baseStart_1360906 : Nat := 118140960795 + 1360906 * 2 ^ 59
def prefixEnd_1360906 : Nat := 4983230072969 + 3 ^ 40 * 1360906 * 2
def baseEnd_1360906 : Nat := 8627146957873551638473

theorem tailTrace_1360906 : CollatzResearch.WordTrace tailWord_1360906 prefixEnd_1360906 8627146957873551638473 := by
  unfold tailWord_1360906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409079901919365271417643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33090879738451640723780381 12409079901919365271417643)
  ·
    refine ⟨18613619852879047907126465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12409079901919365271417643 18613619852879047907126465)
    ·
      refine ⟨13960214889659285930344849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18613619852879047907126465 13960214889659285930344849)
      ·
        refine ⟨10470161167244464447758637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13960214889659285930344849 10470161167244464447758637)
        ·
          refine ⟨3926310437716674167909489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10470161167244464447758637 3926310437716674167909489)
          ·
            refine ⟨2944732828287505625932117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3926310437716674167909489 2944732828287505625932117)
            ·
              refine ⟨8627146957873551638473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2944732828287505625932117 8627146957873551638473)
              ·
                rfl

theorem cell23_1360906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 10].length) (baseStart_1360906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360906 prefixEnd_1360906 := by exact prefixLift 1360906
  have htrace : WordTrace (prefixWord ++ tailWord_1360906) baseStart_1360906 baseEnd_1360906 := by
    simpa [prefixWord, tailWord_1360906, baseEnd_1360906] using wordTrace_append hprefix tailTrace_1360906
  have hstable : (prefixWord ++ tailWord_1360906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360906).length < 2 ^ (prefixWord ++ tailWord_1360906).sum := by decide
  have hdescent : baseEnd_1360906 < baseStart_1360906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360910 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1360910 : Nat := 118140960795 + 1360910 * 2 ^ 59
def prefixEnd_1360910 : Nat := 4983230072969 + 3 ^ 40 * 1360910 * 2
def baseEnd_1360910 : Nat := 232933652503458555688765

theorem tailTrace_1360910 : CollatzResearch.WordTrace tailWord_1360910 prefixEnd_1360910 232933652503458555688765 := by
  unfold tailWord_1360910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204558187457871221102023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33090976999775313179210789 6204558187457871221102023)
  ·
    refine ⟨9306837281186806831653035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204558187457871221102023 9306837281186806831653035)
    ·
      refine ⟨13960255921780210247479553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9306837281186806831653035 13960255921780210247479553)
      ·
        refine ⟨10470191941335157685609665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13960255921780210247479553 10470191941335157685609665)
        ·
          refine ⟨7852643956001368264207249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10470191941335157685609665 7852643956001368264207249)
          ·
            refine ⟨5889482967001026198155437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7852643956001368264207249 5889482967001026198155437)
            ·
              refine ⟨2208556112625384824308289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5889482967001026198155437 2208556112625384824308289)
              ·
                refine ⟨1656417084469038618231217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208556112625384824308289 1656417084469038618231217)
                ·
                  refine ⟨1242312813351778963673413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1656417084469038618231217 1242312813351778963673413)
                  ·
                    refine ⟨232933652503458555688765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242312813351778963673413 232933652503458555688765)
                    ·
                      rfl

theorem cell23_1360910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1360910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360910 prefixEnd_1360910 := by exact prefixLift 1360910
  have htrace : WordTrace (prefixWord ++ tailWord_1360910) baseStart_1360910 baseEnd_1360910 := by
    simpa [prefixWord, tailWord_1360910, baseEnd_1360910] using wordTrace_append hprefix tailTrace_1360910
  have hstable : (prefixWord ++ tailWord_1360910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360910).length < 2 ^ (prefixWord ++ tailWord_1360910).sum := by decide
  have hdescent : baseEnd_1360910 < baseStart_1360910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360917 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_1360917 : Nat := 118140960795 + 1360917 * 2 ^ 59
def prefixEnd_1360917 : Nat := 4983230072969 + 3 ^ 40 * 1360917 * 2
def baseEnd_1360917 : Nat := 698804551874957139678763

theorem tailTrace_1360917 : CollatzResearch.WordTrace tailWord_1360917 prefixEnd_1360917 698804551874957139678763 := by
  unfold tailWord_1360917
  simp only [CollatzResearch.WordTrace]
  refine ⟨49636720810637609964321005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33091147207091739976214003 49636720810637609964321005)
  ·
    refine ⟨18613770303989103736620377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49636720810637609964321005 18613770303989103736620377)
    ·
      refine ⟨13960327727991827802465283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18613770303989103736620377 13960327727991827802465283)
      ·
        refine ⟨20940491591987741703697925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13960327727991827802465283 20940491591987741703697925)
        ·
          refine ⟨3926342173497701569443361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20940491591987741703697925 3926342173497701569443361)
          ·
            refine ⟨2944756630123276177082521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3926342173497701569443361 2944756630123276177082521)
            ·
              refine ⟨2208567472592457132811891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944756630123276177082521 2208567472592457132811891)
              ·
                refine ⟨3312851208888685699217837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208567472592457132811891 3312851208888685699217837)
                ·
                  refine ⟨1242319203333257137206689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3312851208888685699217837 1242319203333257137206689)
                  ·
                    refine ⟨931739402499942852905017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1242319203333257137206689 931739402499942852905017)
                    ·
                      refine ⟨698804551874957139678763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931739402499942852905017 698804551874957139678763)
                      ·
                        rfl

theorem cell23_1360917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_1360917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360917 prefixEnd_1360917 := by exact prefixLift 1360917
  have htrace : WordTrace (prefixWord ++ tailWord_1360917) baseStart_1360917 baseEnd_1360917 := by
    simpa [prefixWord, tailWord_1360917, baseEnd_1360917] using wordTrace_append hprefix tailTrace_1360917
  have hstable : (prefixWord ++ tailWord_1360917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360917).length < 2 ^ (prefixWord ++ tailWord_1360917).sum := by decide
  have hdescent : baseEnd_1360917 < baseStart_1360917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360930 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1360930 : Nat := 118140960795 + 1360930 * 2 ^ 59
def prefixEnd_1360930 : Nat := 4983230072969 + 3 ^ 40 * 1360930 * 2
def baseEnd_1360930 : Nat := 698811227123465588816203

theorem tailTrace_1360930 : CollatzResearch.WordTrace tailWord_1360930 prefixEnd_1360930 698811227123465588816203 := by
  unfold tailWord_1360930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409298739897628296136061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33091463306393675456362829 12409298739897628296136061)
  ·
    refine ⟨4653487027461610611051023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12409298739897628296136061 4653487027461610611051023)
    ·
      refine ⟨6980230541192415916576535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653487027461610611051023 6980230541192415916576535)
      ·
        refine ⟨10470345811788623874864803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6980230541192415916576535 10470345811788623874864803)
        ·
          refine ⟨15705518717682935812297205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10470345811788623874864803 15705518717682935812297205)
          ·
            refine ⟨1472392379782775232402863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15705518717682935812297205 1472392379782775232402863)
            ·
              refine ⟨2208588569674162848604295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472392379782775232402863 2208588569674162848604295)
              ·
                refine ⟨3312882854511244272906443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208588569674162848604295 3312882854511244272906443)
                ·
                  refine ⟨4969324281766866409359665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312882854511244272906443 4969324281766866409359665)
                  ·
                    refine ⟨3726993211325149807019749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4969324281766866409359665 3726993211325149807019749)
                    ·
                      refine ⟨698811227123465588816203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3726993211325149807019749 698811227123465588816203)
                      ·
                        rfl

theorem cell23_1360930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1360930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360930 prefixEnd_1360930 := by exact prefixLift 1360930
  have htrace : WordTrace (prefixWord ++ tailWord_1360930) baseStart_1360930 baseEnd_1360930 := by
    simpa [prefixWord, tailWord_1360930, baseEnd_1360930] using wordTrace_append hprefix tailTrace_1360930
  have hstable : (prefixWord ++ tailWord_1360930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360930).length < 2 ^ (prefixWord ++ tailWord_1360930).sum := by decide
  have hdescent : baseEnd_1360930 < baseStart_1360930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360943 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 7, 3, 2]
def baseStart_1360943 : Nat := 118140960795 + 1360943 * 2 ^ 59
def prefixEnd_1360943 : Nat := 4983230072969 + 3 ^ 40 * 1360943 * 2
def baseEnd_1360943 : Nat := 698817902371974037953643

theorem tailTrace_1360943 : CollatzResearch.WordTrace tailWord_1360943 prefixEnd_1360943 698817902371974037953643 := by
  unfold tailWord_1360943
  simp only [CollatzResearch.WordTrace]
  refine ⟨49637669108543416404767483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33091779405695610936511655 49637669108543416404767483)
  ·
    refine ⟨74456503662815124607151225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49637669108543416404767483 74456503662815124607151225)
    ·
      refine ⟨55842377747111343455363419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74456503662815124607151225 55842377747111343455363419)
      ·
        refine ⟨83763566620667015183045129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55842377747111343455363419 83763566620667015183045129)
        ·
          refine ⟨62822674965500261387283847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83763566620667015183045129 62822674965500261387283847)
          ·
            refine ⟨94234012448250392080925771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62822674965500261387283847 94234012448250392080925771)
            ·
              refine ⟨141351018672375588121388657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94234012448250392080925771 141351018672375588121388657)
              ·
                refine ⟨106013264004281691091041493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141351018672375588121388657 106013264004281691091041493)
                ·
                  refine ⟨2484685875100352134946285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 106013264004281691091041493 2484685875100352134946285)
                  ·
                    refine ⟨931757203162632050604857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484685875100352134946285 931757203162632050604857)
                    ·
                      refine ⟨698817902371974037953643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931757203162632050604857 698817902371974037953643)
                      ·
                        rfl

theorem cell23_1360943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3, 2].length) (baseStart_1360943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360943 prefixEnd_1360943 := by exact prefixLift 1360943
  have htrace : WordTrace (prefixWord ++ tailWord_1360943) baseStart_1360943 baseEnd_1360943 := by
    simpa [prefixWord, tailWord_1360943, baseEnd_1360943] using wordTrace_append hprefix tailTrace_1360943
  have hstable : (prefixWord ++ tailWord_1360943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360943).length < 2 ^ (prefixWord ++ tailWord_1360943).sum := by decide
  have hdescent : baseEnd_1360943 < baseStart_1360943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360946 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1360946 : Nat := 118140960795 + 1360946 * 2 ^ 59
def prefixEnd_1360946 : Nat := 4983230072969 + 3 ^ 40 * 1360946 * 2
def baseEnd_1360946 : Nat := 698819442813937526216129

theorem tailTrace_1360946 : CollatzResearch.WordTrace tailWord_1360946 prefixEnd_1360946 698819442813937526216129 := by
  unfold tailWord_1360946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409444631883136979281673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33091852351688365278084461 12409444631883136979281673)
  ·
    refine ⟨9307083473912352734461255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12409444631883136979281673 9307083473912352734461255)
    ·
      refine ⟨13960625210868529101691883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9307083473912352734461255 13960625210868529101691883)
      ·
        refine ⟨20940937816302793652537825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13960625210868529101691883 20940937816302793652537825)
        ·
          refine ⟨15705703362227095239403369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20940937816302793652537825 15705703362227095239403369)
          ·
            refine ⟨11779277521670321429552527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15705703362227095239403369 11779277521670321429552527)
            ·
              refine ⟨17668916282505482144328791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779277521670321429552527 17668916282505482144328791)
              ·
                refine ⟨26503374423758223216493187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17668916282505482144328791 26503374423758223216493187)
                ·
                  refine ⟨39755061635637334824739781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26503374423758223216493187 39755061635637334824739781)
                  ·
                    refine ⟨7454074056682000279638709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39755061635637334824739781 7454074056682000279638709)
                    ·
                      refine ⟨698819442813937526216129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7454074056682000279638709 698819442813937526216129)
                      ·
                        rfl

theorem cell23_1360946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1360946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360946 prefixEnd_1360946 := by exact prefixLift 1360946
  have htrace : WordTrace (prefixWord ++ tailWord_1360946) baseStart_1360946 baseEnd_1360946 := by
    simpa [prefixWord, tailWord_1360946, baseEnd_1360946] using wordTrace_append hprefix tailTrace_1360946
  have hstable : (prefixWord ++ tailWord_1360946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360946).length < 2 ^ (prefixWord ++ tailWord_1360946).sum := by decide
  have hdescent : baseEnd_1360946 < baseStart_1360946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360960 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2]
def baseStart_1360960 : Nat := 118140960795 + 1360960 * 2 ^ 59
def prefixEnd_1360960 : Nat := 4983230072969 + 3 ^ 40 * 1360960 * 2
def baseEnd_1360960 : Nat := 698826631543100471441065

theorem tailTrace_1360960 : CollatzResearch.WordTrace tailWord_1360960 prefixEnd_1360960 698826631543100471441065 := by
  unfold tailWord_1360960
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819144574740914154068167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33092192766321218872090889 24819144574740914154068167)
  ·
    refine ⟨37228716862111371231102251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24819144574740914154068167 37228716862111371231102251)
    ·
      refine ⟨55843075293167056846653377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37228716862111371231102251 55843075293167056846653377)
      ·
        refine ⟨41882306469875292634990033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55843075293167056846653377 41882306469875292634990033)
        ·
          refine ⟨31411729852406469476242525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41882306469875292634990033 31411729852406469476242525)
          ·
            refine ⟨11779398694652426053590947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31411729852406469476242525 11779398694652426053590947)
            ·
              refine ⟨17669098041978639080386421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11779398694652426053590947 17669098041978639080386421)
              ·
                refine ⟨1656477941435497413786227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17669098041978639080386421 1656477941435497413786227)
                ·
                  refine ⟨2484716912153246120679341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656477941435497413786227 2484716912153246120679341)
                  ·
                    refine ⟨931768842057467295254753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484716912153246120679341 931768842057467295254753)
                    ·
                      refine ⟨698826631543100471441065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931768842057467295254753 698826631543100471441065)
                      ·
                        rfl

theorem cell23_1360960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_1360960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360960 prefixEnd_1360960 := by exact prefixLift 1360960
  have htrace : WordTrace (prefixWord ++ tailWord_1360960) baseStart_1360960 baseEnd_1360960 := by
    simpa [prefixWord, tailWord_1360960, baseEnd_1360960] using wordTrace_append hprefix tailTrace_1360960
  have hstable : (prefixWord ++ tailWord_1360960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360960).length < 2 ^ (prefixWord ++ tailWord_1360960).sum := by decide
  have hdescent : baseEnd_1360960 < baseStart_1360960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360994 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1360994 : Nat := 118140960795 + 1360994 * 2 ^ 59
def prefixEnd_1360994 : Nat := 4983230072969 + 3 ^ 40 * 1360994 * 2
def baseEnd_1360994 : Nat := 698844089885353338415909

theorem tailTrace_1360994 : CollatzResearch.WordTrace tailWord_1360994 prefixEnd_1360994 698844089885353338415909 := by
  unfold tailWord_1360994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409882307839663028718509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33093019487572434743249357 12409882307839663028718509)
  ·
    refine ⟨4653705865439873635769441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12409882307839663028718509 4653705865439873635769441)
    ·
      refine ⟨3490279399079905226827081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4653705865439873635769441 3490279399079905226827081)
      ·
        refine ⟨2617709549309928920120311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3490279399079905226827081 2617709549309928920120311)
        ·
          refine ⟨3926564323964893380180467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617709549309928920120311 3926564323964893380180467)
          ·
            refine ⟨5889846485947340070270701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926564323964893380180467 5889846485947340070270701)
            ·
              refine ⟨2208692432230252526351513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5889846485947340070270701 2208692432230252526351513)
              ·
                refine ⟨1656519324172689394763635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208692432230252526351513 1656519324172689394763635)
                ·
                  refine ⟨2484778986259034092145453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656519324172689394763635 2484778986259034092145453)
                  ·
                    refine ⟨931792119847137784554545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2484778986259034092145453 931792119847137784554545)
                    ·
                      refine ⟨698844089885353338415909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 931792119847137784554545 698844089885353338415909)
                      ·
                        rfl

theorem cell23_1360994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1360994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360994 prefixEnd_1360994 := by exact prefixLift 1360994
  have htrace : WordTrace (prefixWord ++ tailWord_1360994) baseStart_1360994 baseEnd_1360994 := by
    simpa [prefixWord, tailWord_1360994, baseEnd_1360994] using wordTrace_append hprefix tailTrace_1360994
  have hstable : (prefixWord ++ tailWord_1360994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360994).length < 2 ^ (prefixWord ++ tailWord_1360994).sum := by decide
  have hdescent : baseEnd_1360994 < baseStart_1360994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360996 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 9]
def baseStart_1360996 : Nat := 118140960795 + 1360996 * 2 ^ 59
def prefixEnd_1360996 : Nat := 4983230072969 + 3 ^ 40 * 1360996 * 2
def baseEnd_1360996 : Nat := 77649457427406925621211

theorem tailTrace_1360996 : CollatzResearch.WordTrace tailWord_1360996 prefixEnd_1360996 77649457427406925621211 := by
  unfold tailWord_1360996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819801088675703228223421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33093068118234270970964561 24819801088675703228223421)
  ·
    refine ⟨9307425408253388710583783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24819801088675703228223421 9307425408253388710583783)
    ·
      refine ⟨13961138112380083065875675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9307425408253388710583783 13961138112380083065875675)
      ·
        refine ⟨20941707168570124598813513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13961138112380083065875675 20941707168570124598813513)
        ·
          refine ⟨15706280376427593449110135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20941707168570124598813513 15706280376427593449110135)
          ·
            refine ⟨23559420564641390173665203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15706280376427593449110135 23559420564641390173665203)
            ·
              refine ⟨35339130846962085260497805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23559420564641390173665203 35339130846962085260497805)
              ·
                refine ⟨13252174067610781972686677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35339130846962085260497805 13252174067610781972686677)
                ·
                  refine ⟨77649457427406925621211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13252174067610781972686677 77649457427406925621211)
                  ·
                    rfl

theorem cell23_1360996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_1360996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1360996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1360996 prefixEnd_1360996 := by exact prefixLift 1360996
  have htrace : WordTrace (prefixWord ++ tailWord_1360996) baseStart_1360996 baseEnd_1360996 := by
    simpa [prefixWord, tailWord_1360996, baseEnd_1360996] using wordTrace_append hprefix tailTrace_1360996
  have hstable : (prefixWord ++ tailWord_1360996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360996).length < 2 ^ (prefixWord ++ tailWord_1360996).sum := by decide
  have hdescent : baseEnd_1360996 < baseStart_1360996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361060 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_1361060 : Nat := 118140960795 + 1361060 * 2 ^ 59
def prefixEnd_1361060 : Nat := 4983230072969 + 3 ^ 40 * 1361060 * 2
def baseEnd_1361060 : Nat := 232959326536183360063535

theorem tailTrace_1361060 : CollatzResearch.WordTrace tailWord_1361060 prefixEnd_1361060 232959326536183360063535 := by
  unfold tailWord_1361060
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820968224559772693388317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33094624299413030257851089 24820968224559772693388317)
  ·
    refine ⟨9307863084209914760020619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24820968224559772693388317 9307863084209914760020619)
    ·
      refine ⟨13961794626314872140030929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9307863084209914760020619 13961794626314872140030929)
      ·
        refine ⟨10471345969736154105023197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13961794626314872140030929 10471345969736154105023197)
        ·
          refine ⟨3926754738651057789383699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10471345969736154105023197 3926754738651057789383699)
          ·
            refine ⟨5890132107976586684075549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926754738651057789383699 5890132107976586684075549)
            ·
              refine ⟨2208799540491220006528331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5890132107976586684075549 2208799540491220006528331)
              ·
                refine ⟨3313199310736830009792497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208799540491220006528331 3313199310736830009792497)
                ·
                  refine ⟨2484899483052622507344373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313199310736830009792497 2484899483052622507344373)
                  ·
                    refine ⟨232959326536183360063535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2484899483052622507344373 232959326536183360063535)
                    ·
                      rfl

theorem cell23_1361060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_1361060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361060 prefixEnd_1361060 := by exact prefixLift 1361060
  have htrace : WordTrace (prefixWord ++ tailWord_1361060) baseStart_1361060 baseEnd_1361060 := by
    simpa [prefixWord, tailWord_1361060, baseEnd_1361060] using wordTrace_append hprefix tailTrace_1361060
  have hstable : (prefixWord ++ tailWord_1361060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361060).length < 2 ^ (prefixWord ++ tailWord_1361060).sum := by decide
  have hdescent : baseEnd_1361060 < baseStart_1361060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361113 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_1361113 : Nat := 118140960795 + 1361113 * 2 ^ 59
def prefixEnd_1361113 : Nat := 4983230072969 + 3 ^ 40 * 1361113 * 2
def baseEnd_1361113 : Nat := 698905194083238372827861

theorem tailTrace_1361113 : CollatzResearch.WordTrace tailWord_1361113 prefixEnd_1361113 698905194083238372827861 := by
  unfold tailWord_1361113
  simp only [CollatzResearch.WordTrace]
  refine ⟨49643869517927535438455993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33095913011951690292303995 49643869517927535438455993)
  ·
    refine ⟨37232902138445651578841995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49643869517927535438455993 37232902138445651578841995)
    ·
      refine ⟨55849353207668477368262993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37232902138445651578841995 55849353207668477368262993)
      ·
        refine ⟨41887014905751358026197245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55849353207668477368262993 41887014905751358026197245)
        ·
          refine ⟨15707630589656759259823967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41887014905751358026197245 15707630589656759259823967)
          ·
            refine ⟨23561445884485138889735951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15707630589656759259823967 23561445884485138889735951)
            ·
              refine ⟨35342168826727708334603927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23561445884485138889735951 35342168826727708334603927)
              ·
                refine ⟨53013253240091562501905891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35342168826727708334603927 53013253240091562501905891)
                ·
                  refine ⟨79519879860137343752858837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53013253240091562501905891 79519879860137343752858837)
                  ·
                    refine ⟨1863747184221968994207629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79519879860137343752858837 1863747184221968994207629)
                    ·
                      refine ⟨698905194083238372827861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1863747184221968994207629 698905194083238372827861)
                      ·
                        rfl

theorem cell23_1361113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_1361113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361113 prefixEnd_1361113 := by exact prefixLift 1361113
  have htrace : WordTrace (prefixWord ++ tailWord_1361113) baseStart_1361113 baseEnd_1361113 := by
    simpa [prefixWord, tailWord_1361113, baseEnd_1361113] using wordTrace_append hprefix tailTrace_1361113
  have hstable : (prefixWord ++ tailWord_1361113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361113).length < 2 ^ (prefixWord ++ tailWord_1361113).sum := by decide
  have hdescent : baseEnd_1361113 < baseStart_1361113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361180 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1361180 : Nat := 118140960795 + 1361180 * 2 ^ 59
def prefixEnd_1361180 : Nat := 4983230072969 + 3 ^ 40 * 1361180 * 2
def baseEnd_1361180 : Nat := 232979865762363203563351

theorem tailTrace_1361180 : CollatzResearch.WordTrace tailWord_1361180 prefixEnd_1361180 232979865762363203563351 := by
  unfold tailWord_1361180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823156604342402940572497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33097542139123203920763329 24823156604342402940572497)
  ·
    refine ⟨18617367453256802205429373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24823156604342402940572497 18617367453256802205429373)
    ·
      refine ⟨6981512794971300827036015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18617367453256802205429373 6981512794971300827036015)
      ·
        refine ⟨10472269192456951240554023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981512794971300827036015 10472269192456951240554023)
        ·
          refine ⟨15708403788685426860831035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10472269192456951240554023 15708403788685426860831035)
          ·
            refine ⟨23562605683028140291246553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15708403788685426860831035 23562605683028140291246553)
            ·
              refine ⟨17671954262271105218434915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23562605683028140291246553 17671954262271105218434915)
              ·
                refine ⟨26507931393406657827652373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17671954262271105218434915 26507931393406657827652373)
                ·
                  refine ⟨1242559284065937085671205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26507931393406657827652373 1242559284065937085671205)
                  ·
                    refine ⟨232979865762363203563351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242559284065937085671205 232979865762363203563351)
                    ·
                      rfl

theorem cell23_1361180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1361180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361180 prefixEnd_1361180 := by exact prefixLift 1361180
  have htrace : WordTrace (prefixWord ++ tailWord_1361180) baseStart_1361180 baseEnd_1361180 := by
    simpa [prefixWord, tailWord_1361180, baseEnd_1361180] using wordTrace_append hprefix tailTrace_1361180
  have hstable : (prefixWord ++ tailWord_1361180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361180).length < 2 ^ (prefixWord ++ tailWord_1361180).sum := by decide
  have hdescent : baseEnd_1361180 < baseStart_1361180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361184 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 1, 5]
def baseStart_1361184 : Nat := 118140960795 + 1361184 * 2 ^ 59
def prefixEnd_1361184 : Nat := 4983230072969 + 3 ^ 40 * 1361184 * 2
def baseEnd_1361184 : Nat := 232980550403235865013345

theorem tailTrace_1361184 : CollatzResearch.WordTrace tailWord_1361184 prefixEnd_1361184 232980550403235865013345 := by
  unfold tailWord_1361184
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823229550335157282145303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33097639400446876376193737 24823229550335157282145303)
  ·
    refine ⟨37234844325502735923217955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24823229550335157282145303 37234844325502735923217955)
    ·
      refine ⟨55852266488254103884826933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37234844325502735923217955 55852266488254103884826933)
      ·
        refine ⟨5236149983273822239202525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55852266488254103884826933 5236149983273822239202525)
        ·
          refine ⟨1963556243727683339700947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5236149983273822239202525 1963556243727683339700947)
          ·
            refine ⟨2945334365591525009551421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963556243727683339700947 2945334365591525009551421)
            ·
              refine ⟨1104500387096821878581783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2945334365591525009551421 1104500387096821878581783)
              ·
                refine ⟨1656750580645232817872675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104500387096821878581783 1656750580645232817872675)
                ·
                  refine ⟨2485125870967849226809013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656750580645232817872675 2485125870967849226809013)
                  ·
                    refine ⟨232980550403235865013345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2485125870967849226809013 232980550403235865013345)
                    ·
                      rfl

theorem cell23_1361184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_1361184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361184 prefixEnd_1361184 := by exact prefixLift 1361184
  have htrace : WordTrace (prefixWord ++ tailWord_1361184) baseStart_1361184 baseEnd_1361184 := by
    simpa [prefixWord, tailWord_1361184, baseEnd_1361184] using wordTrace_append hprefix tailTrace_1361184
  have hstable : (prefixWord ++ tailWord_1361184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361184).length < 2 ^ (prefixWord ++ tailWord_1361184).sum := by decide
  have hdescent : baseEnd_1361184 < baseStart_1361184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361217 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1361217 : Nat := 118140960795 + 1361217 * 2 ^ 59
def prefixEnd_1361217 : Nat := 4983230072969 + 3 ^ 40 * 1361217 * 2
def baseEnd_1361217 : Nat := 698958596071305965927383

theorem tailTrace_1361217 : CollatzResearch.WordTrace tailWord_1361217 prefixEnd_1361217 698958596071305965927383 := by
  unfold tailWord_1361217
  simp only [CollatzResearch.WordTrace]
  refine ⟨49647662709550761200241905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33098441806367174133494603 49647662709550761200241905)
  ·
    refine ⟨37235747032163070900181429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49647662709550761200241905 37235747032163070900181429)
    ·
      refine ⟨3490851284265287896892009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37235747032163070900181429 3490851284265287896892009)
      ·
        refine ⟨2618138463198965922669007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3490851284265287896892009 2618138463198965922669007)
        ·
          refine ⟨3927207694798448884003511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618138463198965922669007 3927207694798448884003511)
          ·
            refine ⟨5890811542197673326005267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927207694798448884003511 5890811542197673326005267)
            ·
              refine ⟨8836217313296509989007901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890811542197673326005267 8836217313296509989007901)
              ·
                refine ⟨3313581492486191245877963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8836217313296509989007901 3313581492486191245877963)
                ·
                  refine ⟨4970372238729286868816945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313581492486191245877963 4970372238729286868816945)
                  ·
                    refine ⟨3727779179046965151612709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4970372238729286868816945 3727779179046965151612709)
                    ·
                      refine ⟨698958596071305965927383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3727779179046965151612709 698958596071305965927383)
                      ·
                        rfl

theorem cell23_1361217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1361217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361217 prefixEnd_1361217 := by exact prefixLift 1361217
  have htrace : WordTrace (prefixWord ++ tailWord_1361217) baseStart_1361217 baseEnd_1361217 := by
    simpa [prefixWord, tailWord_1361217, baseEnd_1361217] using wordTrace_append hprefix tailTrace_1361217
  have hstable : (prefixWord ++ tailWord_1361217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361217).length < 2 ^ (prefixWord ++ tailWord_1361217).sum := by decide
  have hdescent : baseEnd_1361217 < baseStart_1361217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361237 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1361237 : Nat := 118140960795 + 1361237 * 2 ^ 59
def prefixEnd_1361237 : Nat := 4983230072969 + 3 ^ 40 * 1361237 * 2
def baseEnd_1361237 : Nat := 698968865684395887677291

theorem tailTrace_1361237 : CollatzResearch.WordTrace tailWord_1361237 prefixEnd_1361237 698968865684395887677291 := by
  unfold tailWord_1361237
  simp only [CollatzResearch.WordTrace]
  refine ⟨49648392169478304615969965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33098928112985536410646643 49648392169478304615969965)
  ·
    refine ⟨18618147063554364230988737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49648392169478304615969965 18618147063554364230988737)
    ·
      refine ⟨13963610297665773173241553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18618147063554364230988737 13963610297665773173241553)
      ·
        refine ⟨10472707723249329879931165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13963610297665773173241553 10472707723249329879931165)
        ·
          refine ⟨3927265396218498704974187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10472707723249329879931165 3927265396218498704974187)
          ·
            refine ⟨5890898094327748057461281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927265396218498704974187 5890898094327748057461281)
            ·
              refine ⟨4418173570745811043095961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890898094327748057461281 4418173570745811043095961)
              ·
                refine ⟨3313630178059358282321971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418173570745811043095961 3313630178059358282321971)
                ·
                  refine ⟨4970445267089037423482957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313630178059358282321971 4970445267089037423482957)
                  ·
                    refine ⟨1863916975158389033806109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4970445267089037423482957 1863916975158389033806109)
                    ·
                      refine ⟨698968865684395887677291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1863916975158389033806109 698968865684395887677291)
                      ·
                        rfl

theorem cell23_1361237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1361237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361237 prefixEnd_1361237 := by exact prefixLift 1361237
  have htrace : WordTrace (prefixWord ++ tailWord_1361237) baseStart_1361237 baseEnd_1361237 := by
    simpa [prefixWord, tailWord_1361237, baseEnd_1361237] using wordTrace_append hprefix tailTrace_1361237
  have hstable : (prefixWord ++ tailWord_1361237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361237).length < 2 ^ (prefixWord ++ tailWord_1361237).sum := by decide
  have hdescent : baseEnd_1361237 < baseStart_1361237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361278 : List Nat := [4, 2, 3, 2, 2, 1, 2, 7]
def baseStart_1361278 : Nat := 118140960795 + 1361278 * 2 ^ 59
def prefixEnd_1361278 : Nat := 4983230072969 + 3 ^ 40 * 1361278 * 2
def baseEnd_1361278 : Nat := 25888515495971489898689

theorem tailTrace_1361278 : CollatzResearch.WordTrace tailWord_1361278 prefixEnd_1361278 25888515495971489898689 := by
  unfold tailWord_1361278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206235945291221077276561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33099925041553179078808325 6206235945291221077276561)
  ·
    refine ⟨4654676958968415807957421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6206235945291221077276561 4654676958968415807957421)
    ·
      refine ⟨1745503859613155927984033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4654676958968415807957421 1745503859613155927984033)
      ·
        refine ⟨1309127894709866945988025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745503859613155927984033 1309127894709866945988025)
        ·
          refine ⟨981845921032400209491019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309127894709866945988025 981845921032400209491019)
          ·
            refine ⟨1472768881548600314236529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981845921032400209491019 1472768881548600314236529)
            ·
              refine ⟨1104576661161450235677397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472768881548600314236529 1104576661161450235677397)
              ·
                refine ⟨25888515495971489898689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1104576661161450235677397 25888515495971489898689)
                ·
                  rfl

theorem cell23_1361278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_1361278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361278 prefixEnd_1361278 := by exact prefixLift 1361278
  have htrace : WordTrace (prefixWord ++ tailWord_1361278) baseStart_1361278 baseEnd_1361278 := by
    simpa [prefixWord, tailWord_1361278, baseEnd_1361278] using wordTrace_append hprefix tailTrace_1361278
  have hstable : (prefixWord ++ tailWord_1361278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361278).length < 2 ^ (prefixWord ++ tailWord_1361278).sum := by decide
  have hdescent : baseEnd_1361278 < baseStart_1361278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361280 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_1361280 : Nat := 118140960795 + 1361280 * 2 ^ 59
def prefixEnd_1361280 : Nat := 4983230072969 + 3 ^ 40 * 1361280 * 2
def baseEnd_1361280 : Nat := 698990945352539219439593

theorem tailTrace_1361280 : CollatzResearch.WordTrace tailWord_1361280 prefixEnd_1361280 698990945352539219439593 := by
  unfold tailWord_1361280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24824980254161261479892647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33099973672215015306523529 24824980254161261479892647)
  ·
    refine ⟨37237470381241892219838971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24824980254161261479892647 37237470381241892219838971)
    ·
      refine ⟨55856205571862838329758457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37237470381241892219838971 55856205571862838329758457)
      ·
        refine ⟨41892154178897128747318843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55856205571862838329758457 41892154178897128747318843)
        ·
          refine ⟨62838231268345693120978265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41892154178897128747318843 62838231268345693120978265)
          ·
            refine ⟨47128673451259269840733699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62838231268345693120978265 47128673451259269840733699)
            ·
              refine ⟨70693010176888904761100549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47128673451259269840733699 70693010176888904761100549)
              ·
                refine ⟨13254939408166669642706353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70693010176888904761100549 13254939408166669642706353)
                ·
                  refine ⟨9941204556125002232029765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13254939408166669642706353 9941204556125002232029765)
                  ·
                    refine ⟨1863975854273437918505581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9941204556125002232029765 1863975854273437918505581)
                    ·
                      refine ⟨698990945352539219439593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1863975854273437918505581 698990945352539219439593)
                      ·
                        rfl

theorem cell23_1361280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_1361280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361280 prefixEnd_1361280 := by exact prefixLift 1361280
  have htrace : WordTrace (prefixWord ++ tailWord_1361280) baseStart_1361280 baseEnd_1361280 := by
    simpa [prefixWord, tailWord_1361280, baseEnd_1361280] using wordTrace_append hprefix tailTrace_1361280
  have hstable : (prefixWord ++ tailWord_1361280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361280).length < 2 ^ (prefixWord ++ tailWord_1361280).sum := by decide
  have hdescent : baseEnd_1361280 < baseStart_1361280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361330 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1361330 : Nat := 118140960795 + 1361330 * 2 ^ 59
def prefixEnd_1361330 : Nat := 4983230072969 + 3 ^ 40 * 1361330 * 2
def baseEnd_1361330 : Nat := 233005539795088007938121

theorem tailTrace_1361330 : CollatzResearch.WordTrace tailWord_1361330 prefixEnd_1361330 233005539795088007938121 := by
  unfold tailWord_1361330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412946039535345374776361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33101189438760920999403629 12412946039535345374776361)
  ·
    refine ⟨9309709529651509031082271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12412946039535345374776361 9309709529651509031082271)
    ·
      refine ⟨13964564294477263546623407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9309709529651509031082271 13964564294477263546623407)
      ·
        refine ⟨20946846441715895319935111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13964564294477263546623407 20946846441715895319935111)
        ·
          refine ⟨31420269662573842979902667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20946846441715895319935111 31420269662573842979902667)
          ·
            refine ⟨47130404493860764469854001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31420269662573842979902667 47130404493860764469854001)
            ·
              refine ⟨35347803370395573352390501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47130404493860764469854001 35347803370395573352390501)
              ·
                refine ⟨6627713131949170003573219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35347803370395573352390501 6627713131949170003573219)
                ·
                  refine ⟨9941569697923755005359829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627713131949170003573219 9941569697923755005359829)
                  ·
                    refine ⟨233005539795088007938121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9941569697923755005359829 233005539795088007938121)
                    ·
                      rfl

theorem cell23_1361330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1361330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361330 prefixEnd_1361330 := by exact prefixLift 1361330
  have htrace : WordTrace (prefixWord ++ tailWord_1361330) baseStart_1361330 baseEnd_1361330 := by
    simpa [prefixWord, tailWord_1361330, baseEnd_1361330] using wordTrace_append hprefix tailTrace_1361330
  have hstable : (prefixWord ++ tailWord_1361330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361330).length < 2 ^ (prefixWord ++ tailWord_1361330).sum := by decide
  have hdescent : baseEnd_1361330 < baseStart_1361330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361367 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_1361367 : Nat := 118140960795 + 1361367 * 2 ^ 59
def prefixEnd_1361367 : Nat := 4983230072969 + 3 ^ 40 * 1361367 * 2
def baseEnd_1361367 : Nat := 699035618169480379051693

theorem tailTrace_1361367 : CollatzResearch.WordTrace tailWord_1361367 prefixEnd_1361367 699035618169480379051693 := by
  unfold tailWord_1361367
  simp only [CollatzResearch.WordTrace]
  refine ⟨49653133659007336818202355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33102089106004891212134903 49653133659007336818202355)
  ·
    refine ⟨74479700488511005227303533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49653133659007336818202355 74479700488511005227303533)
    ·
      refine ⟨27929887683191626960238825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74479700488511005227303533 27929887683191626960238825)
      ·
        refine ⟨20947415762393720220179119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27929887683191626960238825 20947415762393720220179119)
        ·
          refine ⟨31421123643590580330268679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20947415762393720220179119 31421123643590580330268679)
          ·
            refine ⟨47131685465385870495403019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31421123643590580330268679 47131685465385870495403019)
            ·
              refine ⟨70697528198078805743104529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47131685465385870495403019 70697528198078805743104529)
              ·
                refine ⟨53023146148559104307328397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70697528198078805743104529 53023146148559104307328397)
                ·
                  refine ⟨19883679805709664115248149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53023146148559104307328397 19883679805709664115248149)
                  ·
                    refine ⟨932047490892640505402257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19883679805709664115248149 932047490892640505402257)
                    ·
                      refine ⟨699035618169480379051693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932047490892640505402257 699035618169480379051693)
                      ·
                        rfl

theorem cell23_1361367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_1361367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361367 prefixEnd_1361367 := by exact prefixLift 1361367
  have htrace : WordTrace (prefixWord ++ tailWord_1361367) baseStart_1361367 baseEnd_1361367 := by
    simpa [prefixWord, tailWord_1361367, baseEnd_1361367] using wordTrace_append hprefix tailTrace_1361367
  have hstable : (prefixWord ++ tailWord_1361367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361367).length < 2 ^ (prefixWord ++ tailWord_1361367).sum := by decide
  have hdescent : baseEnd_1361367 < baseStart_1361367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361384 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_1361384 : Nat := 118140960795 + 1361384 * 2 ^ 59
def prefixEnd_1361384 : Nat := 4983230072969 + 3 ^ 40 * 1361384 * 2
def baseEnd_1361384 : Nat := 699044347340606812539115

theorem tailTrace_1361384 : CollatzResearch.WordTrace tailWord_1361384 prefixEnd_1361384 699044347340606812539115 := by
  unfold tailWord_1361384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24826876849972874360785603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33102502466630499147714137 24826876849972874360785603)
  ·
    refine ⟨37240315274959311541178405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24826876849972874360785603 37240315274959311541178405)
    ·
      refine ⟨6982559114054870913970951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37240315274959311541178405 6982559114054870913970951)
      ·
        refine ⟨10473838671082306370956427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982559114054870913970951 10473838671082306370956427)
        ·
          refine ⟨15710758006623459556434641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10473838671082306370956427 15710758006623459556434641)
          ·
            refine ⟨11783068504967594667325981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15710758006623459556434641 11783068504967594667325981)
            ·
              refine ⟨4418650689362848000247243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11783068504967594667325981 4418650689362848000247243)
              ·
                refine ⟨6627976034044272000370865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418650689362848000247243 6627976034044272000370865)
                ·
                  refine ⟨4970982025533204000278149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6627976034044272000370865 4970982025533204000278149)
                  ·
                    refine ⟨932059129787475750052153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970982025533204000278149 932059129787475750052153)
                    ·
                      refine ⟨699044347340606812539115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932059129787475750052153 699044347340606812539115)
                      ·
                        rfl

theorem cell23_1361384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_1361384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361384 prefixEnd_1361384 := by exact prefixLift 1361384
  have htrace : WordTrace (prefixWord ++ tailWord_1361384) baseStart_1361384 baseEnd_1361384 := by
    simpa [prefixWord, tailWord_1361384, baseEnd_1361384] using wordTrace_append hprefix tailTrace_1361384
  have hstable : (prefixWord ++ tailWord_1361384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361384).length < 2 ^ (prefixWord ++ tailWord_1361384).sum := by decide
  have hdescent : baseEnd_1361384 < baseStart_1361384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361394 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_1361394 : Nat := 118140960795 + 1361394 * 2 ^ 59
def prefixEnd_1361394 : Nat := 4983230072969 + 3 ^ 40 * 1361394 * 2
def baseEnd_1361394 : Nat := 233016494049050591138023

theorem tailTrace_1361394 : CollatzResearch.WordTrace tailWord_1361394 prefixEnd_1361394 233016494049050591138023 := by
  unfold tailWord_1361394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413529607477380107358809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33102745619939680286290157 12413529607477380107358809)
  ·
    refine ⟨9310147205608035080519107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12413529607477380107358809 9310147205608035080519107)
    ·
      refine ⟨13965220808412052620778661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9310147205608035080519107 13965220808412052620778661)
      ·
        refine ⟨2618478901577259866395999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13965220808412052620778661 2618478901577259866395999)
        ·
          refine ⟨3927718352365889799593999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618478901577259866395999 3927718352365889799593999)
          ·
            refine ⟨5891577528548834699390999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927718352365889799593999 5891577528548834699390999)
            ·
              refine ⟨8837366292823252049086499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891577528548834699390999 8837366292823252049086499)
              ·
                refine ⟨13256049439234878073629749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837366292823252049086499 13256049439234878073629749)
                ·
                  refine ⟨1242754634928269819402789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13256049439234878073629749 1242754634928269819402789)
                  ·
                    refine ⟨233016494049050591138023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242754634928269819402789 233016494049050591138023)
                    ·
                      rfl

theorem cell23_1361394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_1361394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361394 prefixEnd_1361394 := by exact prefixLift 1361394
  have htrace : WordTrace (prefixWord ++ tailWord_1361394) baseStart_1361394 baseEnd_1361394 := by
    simpa [prefixWord, tailWord_1361394, baseEnd_1361394] using wordTrace_append hprefix tailTrace_1361394
  have hstable : (prefixWord ++ tailWord_1361394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361394).length < 2 ^ (prefixWord ++ tailWord_1361394).sum := by decide
  have hdescent : baseEnd_1361394 < baseStart_1361394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361404 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_1361404 : Nat := 118140960795 + 1361404 * 2 ^ 59
def prefixEnd_1361404 : Nat := 4983230072969 + 3 ^ 40 * 1361404 * 2
def baseEnd_1361404 : Nat := 699054616953696734289023

theorem tailTrace_1361404 : CollatzResearch.WordTrace tailWord_1361404 prefixEnd_1361404 699054616953696734289023 := by
  unfold tailWord_1361404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827241579936646068649633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33102988773248861424866177 24827241579936646068649633)
  ·
    refine ⟨18620431184952484551487225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24827241579936646068649633 18620431184952484551487225)
    ·
      refine ⟨13965323388714363413615419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18620431184952484551487225 13965323388714363413615419)
      ·
        refine ⟨20947985083071545120423129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13965323388714363413615419 20947985083071545120423129)
        ·
          refine ⟨15710988812303658840317347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20947985083071545120423129 15710988812303658840317347)
          ·
            refine ⟨23566483218455488260476021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15710988812303658840317347 23566483218455488260476021)
            ·
              refine ⟨2209357801730202024419627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23566483218455488260476021 2209357801730202024419627)
              ·
                refine ⟨3314036702595303036629441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209357801730202024419627 3314036702595303036629441)
                ·
                  refine ⟨2485527526946477277472081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3314036702595303036629441 2485527526946477277472081)
                  ·
                    refine ⟨1864145645209857958104061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485527526946477277472081 1864145645209857958104061)
                    ·
                      refine ⟨699054616953696734289023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1864145645209857958104061 699054616953696734289023)
                      ·
                        rfl

theorem cell23_1361404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_1361404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361404 prefixEnd_1361404 := by exact prefixLift 1361404
  have htrace : WordTrace (prefixWord ++ tailWord_1361404) baseStart_1361404 baseEnd_1361404 := by
    simpa [prefixWord, tailWord_1361404, baseEnd_1361404] using wordTrace_append hprefix tailTrace_1361404
  have hstable : (prefixWord ++ tailWord_1361404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361404).length < 2 ^ (prefixWord ++ tailWord_1361404).sum := by decide
  have hdescent : baseEnd_1361404 < baseStart_1361404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361428 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1361428 : Nat := 118140960795 + 1361428 * 2 ^ 59
def prefixEnd_1361428 : Nat := 4983230072969 + 3 ^ 40 * 1361428 * 2
def baseEnd_1361428 : Nat := 233022313496468213462971

theorem tailTrace_1361428 : CollatzResearch.WordTrace tailWord_1361428 prefixEnd_1361428 233022313496468213462971 := by
  unfold tailWord_1361428
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827679255893172118086469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33103572341190896157448625 24827679255893172118086469)
  ·
    refine ⟨4655189860479969772141213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24827679255893172118086469 4655189860479969772141213)
    ·
      refine ⟨1745696197679988664552955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4655189860479969772141213 1745696197679988664552955)
      ·
        refine ⟨2618544296519982996829433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745696197679988664552955 2618544296519982996829433)
        ·
          refine ⟨1963908222389987247622075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2618544296519982996829433 1963908222389987247622075)
          ·
            refine ⟨2945862333584980871433113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963908222389987247622075 2945862333584980871433113)
            ·
              refine ⟨2209396750188735653574835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945862333584980871433113 2209396750188735653574835)
              ·
                refine ⟨3314095125283103480362253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209396750188735653574835 3314095125283103480362253)
                ·
                  refine ⟨1242785671981163805135845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3314095125283103480362253 1242785671981163805135845)
                  ·
                    refine ⟨233022313496468213462971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242785671981163805135845 233022313496468213462971)
                    ·
                      rfl

theorem cell23_1361428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1361428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361428 prefixEnd_1361428 := by exact prefixLift 1361428
  have htrace : WordTrace (prefixWord ++ tailWord_1361428) baseStart_1361428 baseEnd_1361428 := by
    simpa [prefixWord, tailWord_1361428, baseEnd_1361428] using wordTrace_append hprefix tailTrace_1361428
  have hstable : (prefixWord ++ tailWord_1361428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361428).length < 2 ^ (prefixWord ++ tailWord_1361428).sum := by decide
  have hdescent : baseEnd_1361428 < baseStart_1361428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361462 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1361462 : Nat := 118140960795 + 1361462 * 2 ^ 59
def prefixEnd_1361462 : Nat := 4983230072969 + 3 ^ 40 * 1361462 * 2
def baseEnd_1361462 : Nat := 233028132943885835787919

theorem tailTrace_1361462 : CollatzResearch.WordTrace tailWord_1361462 prefixEnd_1361462 233028132943885835787919 := by
  unfold tailWord_1361462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3103537412103948002681915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33104399062442112028607093 3103537412103948002681915)
  ·
    refine ⟨4655306118155922004022873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3103537412103948002681915 4655306118155922004022873)
    ·
      refine ⟨3491479588616941503017155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4655306118155922004022873 3491479588616941503017155)
      ·
        refine ⟨5237219382925412254525733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491479588616941503017155 5237219382925412254525733)
        ·
          refine ⟨981978634298514797723575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5237219382925412254525733 981978634298514797723575)
          ·
            refine ⟨1472967951447772196585363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981978634298514797723575 1472967951447772196585363)
            ·
              refine ⟨2209451927171658294878045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472967951447772196585363 2209451927171658294878045)
              ·
                refine ⟨828544472689371860579267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209451927171658294878045 828544472689371860579267)
                ·
                  refine ⟨1242816709034057790868901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828544472689371860579267 1242816709034057790868901)
                  ·
                    refine ⟨233028132943885835787919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242816709034057790868901 233028132943885835787919)
                    ·
                      rfl

theorem cell23_1361462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1361462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361462 prefixEnd_1361462 := by exact prefixLift 1361462
  have htrace : WordTrace (prefixWord ++ tailWord_1361462) baseStart_1361462 baseEnd_1361462 := by
    simpa [prefixWord, tailWord_1361462, baseEnd_1361462] using wordTrace_append hprefix tailTrace_1361462
  have hstable : (prefixWord ++ tailWord_1361462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361462).length < 2 ^ (prefixWord ++ tailWord_1361462).sum := by decide
  have hdescent : baseEnd_1361462 < baseStart_1361462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361484 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_1361484 : Nat := 118140960795 + 1361484 * 2 ^ 59
def prefixEnd_1361484 : Nat := 4983230072969 + 3 ^ 40 * 1361484 * 2
def baseEnd_1361484 : Nat := 233031898468685473762885

theorem tailTrace_1361484 : CollatzResearch.WordTrace tailWord_1361484 prefixEnd_1361484 233031898468685473762885 := by
  unfold tailWord_1361484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828700499791732900105753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33104933999722310533474337 24828700499791732900105753)
  ·
    refine ⟨18621525374843799675079315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24828700499791732900105753 18621525374843799675079315)
    ·
      refine ⟨27932288062265699512618973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18621525374843799675079315 27932288062265699512618973)
      ·
        refine ⟨10474608023349637317232115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27932288062265699512618973 10474608023349637317232115)
        ·
          refine ⟨15711912035024455975848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474608023349637317232115 15711912035024455975848173)
          ·
            refine ⟨5891967013134170990943065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15711912035024455975848173 5891967013134170990943065)
            ·
              refine ⟨4418975259850628243207299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5891967013134170990943065 4418975259850628243207299)
              ·
                refine ⟨6628462889775942364810949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418975259850628243207299 6628462889775942364810949)
                ·
                  refine ⟨1242836791832989193402053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6628462889775942364810949 1242836791832989193402053)
                  ·
                    refine ⟨233031898468685473762885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242836791832989193402053 233031898468685473762885)
                    ·
                      rfl

theorem cell23_1361484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_1361484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361484 prefixEnd_1361484 := by exact prefixLift 1361484
  have htrace : WordTrace (prefixWord ++ tailWord_1361484) baseStart_1361484 baseEnd_1361484 := by
    simpa [prefixWord, tailWord_1361484, baseEnd_1361484] using wordTrace_append hprefix tailTrace_1361484
  have hstable : (prefixWord ++ tailWord_1361484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361484).length < 2 ^ (prefixWord ++ tailWord_1361484).sum := by decide
  have hdescent : baseEnd_1361484 < baseStart_1361484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361485 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1361485 : Nat := 118140960795 + 1361485 * 2 ^ 59
def prefixEnd_1361485 : Nat := 4983230072969 + 3 ^ 40 * 1361485 * 2
def baseEnd_1361485 : Nat := 699096208886710917376151

theorem tailTrace_1361485 : CollatzResearch.WordTrace tailWord_1361485 prefixEnd_1361485 699096208886710917376151 := by
  unfold tailWord_1361485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49657437472579842970997909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33104958315053228647331939 49657437472579842970997909)
  ·
    refine ⟨2327692381527180139265527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49657437472579842970997909 2327692381527180139265527)
    ·
      refine ⟨3491538572290770208898291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2327692381527180139265527 3491538572290770208898291)
      ·
        refine ⟨5237307858436155313347437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491538572290770208898291 5237307858436155313347437)
        ·
          refine ⟨1963990446913558242505289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5237307858436155313347437 1963990446913558242505289)
          ·
            refine ⟨1472992835185168681878967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1963990446913558242505289 1472992835185168681878967)
            ·
              refine ⟨2209489252777753022818451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472992835185168681878967 2209489252777753022818451)
              ·
                refine ⟨3314233879166629534227677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209489252777753022818451 3314233879166629534227677)
                ·
                  refine ⟨1242837704687486075335379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3314233879166629534227677 1242837704687486075335379)
                  ·
                    refine ⟨1864256557031229113003069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1242837704687486075335379 1864256557031229113003069)
                    ·
                      refine ⟨699096208886710917376151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1864256557031229113003069 699096208886710917376151)
                      ·
                        rfl

theorem cell23_1361485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1361485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361485 prefixEnd_1361485 := by exact prefixLift 1361485
  have htrace : WordTrace (prefixWord ++ tailWord_1361485) baseStart_1361485 baseEnd_1361485 := by
    simpa [prefixWord, tailWord_1361485, baseEnd_1361485] using wordTrace_append hprefix tailTrace_1361485
  have hstable : (prefixWord ++ tailWord_1361485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361485).length < 2 ^ (prefixWord ++ tailWord_1361485).sum := by decide
  have hdescent : baseEnd_1361485 < baseStart_1361485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361511 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1361511 : Nat := 118140960795 + 1361511 * 2 ^ 59
def prefixEnd_1361511 : Nat := 4983230072969 + 3 ^ 40 * 1361511 * 2
def baseEnd_1361511 : Nat := 699109559383727815651031

theorem tailTrace_1361511 : CollatzResearch.WordTrace tailWord_1361511 prefixEnd_1361511 699109559383727815651031 := by
  unfold tailWord_1361511
  simp only [CollatzResearch.WordTrace]
  refine ⟨49658385770485649411444387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33105590513657099607629591 49658385770485649411444387)
  ·
    refine ⟨74487578655728474117166581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49658385770485649411444387 74487578655728474117166581)
    ·
      refine ⟨6983210498974544448484367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74487578655728474117166581 6983210498974544448484367)
      ·
        refine ⟨10474815748461816672726551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983210498974544448484367 10474815748461816672726551)
        ·
          refine ⟨15712223622692725009089827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474815748461816672726551 15712223622692725009089827)
          ·
            refine ⟨23568335434039087513634741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15712223622692725009089827 23568335434039087513634741)
            ·
              refine ⟨2209531446941164454403257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23568335434039087513634741 2209531446941164454403257)
              ·
                refine ⟨1657148585205873340802443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209531446941164454403257 1657148585205873340802443)
                ·
                  refine ⟨2485722877808810011203665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657148585205873340802443 2485722877808810011203665)
                  ·
                    refine ⟨1864292158356607508402749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485722877808810011203665 1864292158356607508402749)
                    ·
                      refine ⟨699109559383727815651031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1864292158356607508402749 699109559383727815651031)
                      ·
                        rfl

theorem cell23_1361511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1361511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361511 prefixEnd_1361511 := by exact prefixLift 1361511
  have htrace : WordTrace (prefixWord ++ tailWord_1361511) baseStart_1361511 baseEnd_1361511 := by
    simpa [prefixWord, tailWord_1361511, baseEnd_1361511] using wordTrace_append hprefix tailTrace_1361511
  have hstable : (prefixWord ++ tailWord_1361511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361511).length < 2 ^ (prefixWord ++ tailWord_1361511).sum := by decide
  have hdescent : baseEnd_1361511 < baseStart_1361511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361547 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_1361547 : Nat := 118140960795 + 1361547 * 2 ^ 59
def prefixEnd_1361547 : Nat := 4983230072969 + 3 ^ 40 * 1361547 * 2
def baseEnd_1361547 : Nat := 699128044687289674800865

theorem tailTrace_1361547 : CollatzResearch.WordTrace tailWord_1361547 prefixEnd_1361547 699128044687289674800865 := by
  unfold tailWord_1361547
  simp only [CollatzResearch.WordTrace]
  refine ⟨49659698798355227559754895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33106465865570151706503263 49659698798355227559754895)
  ·
    refine ⟨74489548197532841339632343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49659698798355227559754895 74489548197532841339632343)
    ·
      refine ⟨111734322296299262009448515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74489548197532841339632343 111734322296299262009448515)
      ·
        refine ⟨167601483444448893014172773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111734322296299262009448515 167601483444448893014172773)
        ·
          refine ⟨31425278145834167440157395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167601483444448893014172773 31425278145834167440157395)
          ·
            refine ⟨47137917218751251160236093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31425278145834167440157395 47137917218751251160236093)
            ·
              refine ⟨17676718957031719185088535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47137917218751251160236093 17676718957031719185088535)
              ·
                refine ⟨26515078435547578777632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17676718957031719185088535 26515078435547578777632803)
                ·
                  refine ⟨39772617653321368166449205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26515078435547578777632803 39772617653321368166449205)
                  ·
                    refine ⟨3728682904998878265604613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39772617653321368166449205 3728682904998878265604613)
                    ·
                      refine ⟨699128044687289674800865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3728682904998878265604613 699128044687289674800865)
                      ·
                        rfl

theorem cell23_1361547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_1361547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361547 prefixEnd_1361547 := by exact prefixLift 1361547
  have htrace : WordTrace (prefixWord ++ tailWord_1361547) baseStart_1361547 baseEnd_1361547 := by
    simpa [prefixWord, tailWord_1361547, baseEnd_1361547] using wordTrace_append hprefix tailTrace_1361547
  have hstable : (prefixWord ++ tailWord_1361547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361547).length < 2 ^ (prefixWord ++ tailWord_1361547).sum := by decide
  have hdescent : baseEnd_1361547 < baseStart_1361547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361576 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1361576 : Nat := 118140960795 + 1361576 * 2 ^ 59
def prefixEnd_1361576 : Nat := 4983230072969 + 3 ^ 40 * 1361576 * 2
def baseEnd_1361576 : Nat := 699142935626270061338233

theorem tailTrace_1361576 : CollatzResearch.WordTrace tailWord_1361576 prefixEnd_1361576 699142935626270061338233 := by
  unfold tailWord_1361576
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830378257625082756280291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33107171010166777008373721 24830378257625082756280291)
  ·
    refine ⟨37245567386437624134420437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24830378257625082756280291 37245567386437624134420437)
    ·
      refine ⟨872942985619631815650479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37245567386437624134420437 872942985619631815650479)
      ·
        refine ⟨1309414478429447723475719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872942985619631815650479 1309414478429447723475719)
        ·
          refine ⟨1964121717644171585213579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309414478429447723475719 1964121717644171585213579)
          ·
            refine ⟨2946182576466257377820369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964121717644171585213579 2946182576466257377820369)
            ·
              refine ⟨2209636932349693033365277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946182576466257377820369 2209636932349693033365277)
              ·
                refine ⟨828613849631134887511979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209636932349693033365277 828613849631134887511979)
                ·
                  refine ⟨1242920774446702331267969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828613849631134887511979 1242920774446702331267969)
                  ·
                    refine ⟨932190580835026748450977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1242920774446702331267969 932190580835026748450977)
                    ·
                      refine ⟨699142935626270061338233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932190580835026748450977 699142935626270061338233)
                      ·
                        rfl

theorem cell23_1361576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1361576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361576 prefixEnd_1361576 := by exact prefixLift 1361576
  have htrace : WordTrace (prefixWord ++ tailWord_1361576) baseStart_1361576 baseEnd_1361576 := by
    simpa [prefixWord, tailWord_1361576, baseEnd_1361576] using wordTrace_append hprefix tailTrace_1361576
  have hstable : (prefixWord ++ tailWord_1361576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361576).length < 2 ^ (prefixWord ++ tailWord_1361576).sum := by decide
  have hdescent : baseEnd_1361576 < baseStart_1361576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361587 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 9]
def baseStart_1361587 : Nat := 118140960795 + 1361587 * 2 ^ 59
def prefixEnd_1361587 : Nat := 4983230072969 + 3 ^ 40 * 1361587 * 2
def baseEnd_1361587 : Nat := 77683175990385502033409

theorem tailTrace_1361587 : CollatzResearch.WordTrace tailWord_1361587 prefixEnd_1361587 77683175990385502033409 := by
  unfold tailWord_1361587
  simp only [CollatzResearch.WordTrace]
  refine ⟨49661157718210314391211015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33107438478806876260807343 49661157718210314391211015)
  ·
    refine ⟨74491736577315471586816523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49661157718210314391211015 74491736577315471586816523)
    ·
      refine ⟨111737604865973207380224785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74491736577315471586816523 111737604865973207380224785)
      ·
        refine ⟨83803203649479905535168589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111737604865973207380224785 83803203649479905535168589)
        ·
          refine ⟨31426201368554964575688221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83803203649479905535168589 31426201368554964575688221)
          ·
            refine ⟨11784825513208111715883083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31426201368554964575688221 11784825513208111715883083)
            ·
              refine ⟨17677238269812167573824625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11784825513208111715883083 17677238269812167573824625)
              ·
                refine ⟨13257928702359125680368469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17677238269812167573824625 13257928702359125680368469)
                ·
                  refine ⟨77683175990385502033409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13257928702359125680368469 77683175990385502033409)
                  ·
                    rfl

theorem cell23_1361587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 9].length) (baseStart_1361587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361587 prefixEnd_1361587 := by exact prefixLift 1361587
  have htrace : WordTrace (prefixWord ++ tailWord_1361587) baseStart_1361587 baseEnd_1361587 := by
    simpa [prefixWord, tailWord_1361587, baseEnd_1361587] using wordTrace_append hprefix tailTrace_1361587
  have hstable : (prefixWord ++ tailWord_1361587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361587).length < 2 ^ (prefixWord ++ tailWord_1361587).sum := by decide
  have hdescent : baseEnd_1361587 < baseStart_1361587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361594 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1361594 : Nat := 118140960795 + 1361594 * 2 ^ 59
def prefixEnd_1361594 : Nat := 4983230072969 + 3 ^ 40 * 1361594 * 2
def baseEnd_1361594 : Nat := 699152178278050990913149

theorem tailTrace_1361594 : CollatzResearch.WordTrace tailWord_1361594 prefixEnd_1361594 699152178278050990913149 := by
  unfold tailWord_1361594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415353257296238646678959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33107608686123303057810557 12415353257296238646678959)
  ·
    refine ⟨18623029885944357970018439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12415353257296238646678959 18623029885944357970018439)
    ·
      refine ⟨27934544828916536955027659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18623029885944357970018439 27934544828916536955027659)
      ·
        refine ⟨41901817243374805432541489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27934544828916536955027659 41901817243374805432541489)
        ·
          refine ⟨31426362932531104074406117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41901817243374805432541489 31426362932531104074406117)
          ·
            refine ⟨5892443049849582013951147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31426362932531104074406117 5892443049849582013951147)
            ·
              refine ⟨8838664574774373020926721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5892443049849582013951147 8838664574774373020926721)
              ·
                refine ⟨6628998431080779765695041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8838664574774373020926721 6628998431080779765695041)
                ·
                  refine ⟨4971748823310584824271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6628998431080779765695041 4971748823310584824271281)
                  ·
                    refine ⟨3728811617482938618203461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4971748823310584824271281 3728811617482938618203461)
                    ·
                      refine ⟨699152178278050990913149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3728811617482938618203461 699152178278050990913149)
                      ·
                        rfl

theorem cell23_1361594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1361594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361594 prefixEnd_1361594 := by exact prefixLift 1361594
  have htrace : WordTrace (prefixWord ++ tailWord_1361594) baseStart_1361594 baseEnd_1361594 := by
    simpa [prefixWord, tailWord_1361594, baseEnd_1361594] using wordTrace_append hprefix tailTrace_1361594
  have hstable : (prefixWord ++ tailWord_1361594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361594).length < 2 ^ (prefixWord ++ tailWord_1361594).sum := by decide
  have hdescent : baseEnd_1361594 < baseStart_1361594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361670 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1361670 : Nat := 118140960795 + 1361670 * 2 ^ 59
def prefixEnd_1361670 : Nat := 4983230072969 + 3 ^ 40 * 1361670 * 2
def baseEnd_1361670 : Nat := 699191202807792693562801

theorem tailTrace_1361670 : CollatzResearch.WordTrace tailWord_1361670 prefixEnd_1361670 699191202807792693562801 := by
  unfold tailWord_1361670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552005780528425611452577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33109456651273079710988309 1552005780528425611452577)
  ·
    refine ⟨1164004335396319208589433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1552005780528425611452577 1164004335396319208589433)
    ·
      refine ⟨873003251547239406442075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164004335396319208589433 873003251547239406442075)
      ·
        refine ⟨1309504877320859109663113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873003251547239406442075 1309504877320859109663113)
        ·
          refine ⟨982128657990644332247335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309504877320859109663113 982128657990644332247335)
          ·
            refine ⟨1473192986985966498371003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982128657990644332247335 1473192986985966498371003)
            ·
              refine ⟨2209789480478949747556505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473192986985966498371003 2209789480478949747556505)
              ·
                refine ⟨1657342110359212310667379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209789480478949747556505 1657342110359212310667379)
                ·
                  refine ⟨2486013165538818466001069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657342110359212310667379 2486013165538818466001069)
                  ·
                    refine ⟨932254937077056924750401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486013165538818466001069 932254937077056924750401)
                    ·
                      refine ⟨699191202807792693562801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932254937077056924750401 699191202807792693562801)
                      ·
                        rfl

theorem cell23_1361670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1361670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361670 prefixEnd_1361670 := by exact prefixLift 1361670
  have htrace : WordTrace (prefixWord ++ tailWord_1361670) baseStart_1361670 baseEnd_1361670 := by
    simpa [prefixWord, tailWord_1361670, baseEnd_1361670] using wordTrace_append hprefix tailTrace_1361670
  have hstable : (prefixWord ++ tailWord_1361670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361670).length < 2 ^ (prefixWord ++ tailWord_1361670).sum := by decide
  have hdescent : baseEnd_1361670 < baseStart_1361670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361715 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 1, 4]
def baseStart_1361715 : Nat := 118140960795 + 1361715 * 2 ^ 59
def prefixEnd_1361715 : Nat := 4983230072969 + 3 ^ 40 * 1361715 * 2
def baseEnd_1361715 : Nat := 233071436479081672500031

theorem tailTrace_1361715 : CollatzResearch.WordTrace tailWord_1361715 prefixEnd_1361715 233071436479081672500031 := by
  unfold tailWord_1361715
  simp only [CollatzResearch.WordTrace]
  refine ⟨49665826261746592251870599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33110550841164394834580399 49665826261746592251870599)
  ·
    refine ⟨74498739392619888377805899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49665826261746592251870599 74498739392619888377805899)
    ·
      refine ⟨111748109088929832566708849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74498739392619888377805899 111748109088929832566708849)
      ·
        refine ⟨83811081816697374425031637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111748109088929832566708849 83811081816697374425031637)
        ·
          refine ⟨1964322230078844713086679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 83811081816697374425031637 1964322230078844713086679)
          ·
            refine ⟨2946483345118267069630019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964322230078844713086679 2946483345118267069630019)
            ·
              refine ⟨4419725017677400604445029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946483345118267069630019 4419725017677400604445029)
              ·
                refine ⟨828698440814512613333443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4419725017677400604445029 828698440814512613333443)
                ·
                  refine ⟨1243047661221768920000165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828698440814512613333443 1243047661221768920000165)
                  ·
                    refine ⟨233071436479081672500031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243047661221768920000165 233071436479081672500031)
                    ·
                      rfl

theorem cell23_1361715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 4].length) (baseStart_1361715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361715 prefixEnd_1361715 := by exact prefixLift 1361715
  have htrace : WordTrace (prefixWord ++ tailWord_1361715) baseStart_1361715 baseEnd_1361715 := by
    simpa [prefixWord, tailWord_1361715, baseEnd_1361715] using wordTrace_append hprefix tailTrace_1361715
  have hstable : (prefixWord ++ tailWord_1361715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361715).length < 2 ^ (prefixWord ++ tailWord_1361715).sum := by decide
  have hdescent : baseEnd_1361715 < baseStart_1361715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361738 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_1361738 : Nat := 118140960795 + 1361738 * 2 ^ 59
def prefixEnd_1361738 : Nat := 4983230072969 + 3 ^ 40 * 1361738 * 2
def baseEnd_1361738 : Nat := 699226119492298427512487

theorem tailTrace_1361738 : CollatzResearch.WordTrace tailWord_1361738 prefixEnd_1361738 699226119492298427512487 := by
  unfold tailWord_1361738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416666285165816794989467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33111110093775511453305245 12416666285165816794989467)
  ·
    refine ⟨18624999427748725192484201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12416666285165816794989467 18624999427748725192484201)
    ·
      refine ⟨13968749570811543894363151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18624999427748725192484201 13968749570811543894363151)
      ·
        refine ⟨20953124356217315841544727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13968749570811543894363151 20953124356217315841544727)
        ·
          refine ⟨31429686534325973762317091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20953124356217315841544727 31429686534325973762317091)
          ·
            refine ⟨47144529801488960643475637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31429686534325973762317091 47144529801488960643475637)
            ·
              refine ⟨4419799668889590060325841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47144529801488960643475637 4419799668889590060325841)
              ·
                refine ⟨3314849751667192545244381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4419799668889590060325841 3314849751667192545244381)
                ·
                  refine ⟨1243068656875197204466643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3314849751667192545244381 1243068656875197204466643)
                  ·
                    refine ⟨1864602985312795806699965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1243068656875197204466643 1864602985312795806699965)
                    ·
                      refine ⟨699226119492298427512487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1864602985312795806699965 699226119492298427512487)
                      ·
                        rfl

theorem cell23_1361738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_1361738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361738 prefixEnd_1361738 := by exact prefixLift 1361738
  have htrace : WordTrace (prefixWord ++ tailWord_1361738) baseStart_1361738 baseEnd_1361738 := by
    simpa [prefixWord, tailWord_1361738, baseEnd_1361738] using wordTrace_append hprefix tailTrace_1361738
  have hstable : (prefixWord ++ tailWord_1361738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361738).length < 2 ^ (prefixWord ++ tailWord_1361738).sum := by decide
  have hdescent : baseEnd_1361738 < baseStart_1361738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361795 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 3, 2, 2]
def baseStart_1361795 : Nat := 118140960795 + 1361795 * 2 ^ 59
def prefixEnd_1361795 : Nat := 4983230072969 + 3 ^ 40 * 1361795 * 2
def baseEnd_1361795 : Nat := 699255387889604704499725

theorem tailTrace_1361795 : CollatzResearch.WordTrace tailWord_1361795 prefixEnd_1361795 699255387889604704499725 := by
  unfold tailWord_1361795
  simp only [CollatzResearch.WordTrace]
  refine ⟨49668744101456765914782839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33112496067637843943188559 49668744101456765914782839)
  ·
    refine ⟨74503116152185148872174259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49668744101456765914782839 74503116152185148872174259)
    ·
      refine ⟨111754674228277723308261389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74503116152185148872174259 111754674228277723308261389)
      ·
        refine ⟨41908002835604146240598021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111754674228277723308261389 41908002835604146240598021)
        ·
          refine ⟨7857750531675777420112129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41908002835604146240598021 7857750531675777420112129)
          ·
            refine ⟨5893312898756833065084097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7857750531675777420112129 5893312898756833065084097)
            ·
              refine ⟨4419984674067624798813073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5893312898756833065084097 4419984674067624798813073)
              ·
                refine ⟨3314988505550718599109805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4419984674067624798813073 3314988505550718599109805)
                ·
                  refine ⟨1243120689581519474666177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3314988505550718599109805 1243120689581519474666177)
                  ·
                    refine ⟨932340517186139605999633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1243120689581519474666177 932340517186139605999633)
                    ·
                      refine ⟨699255387889604704499725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932340517186139605999633 699255387889604704499725)
                      ·
                        rfl

theorem cell23_1361795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_1361795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361795 prefixEnd_1361795 := by exact prefixLift 1361795
  have htrace : WordTrace (prefixWord ++ tailWord_1361795) baseStart_1361795 baseEnd_1361795 := by
    simpa [prefixWord, tailWord_1361795, baseEnd_1361795] using wordTrace_append hprefix tailTrace_1361795
  have hstable : (prefixWord ++ tailWord_1361795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361795).length < 2 ^ (prefixWord ++ tailWord_1361795).sum := by decide
  have hdescent : baseEnd_1361795 < baseStart_1361795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361806 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1361806 : Nat := 118140960795 + 1361806 * 2 ^ 59
def prefixEnd_1361806 : Nat := 4983230072969 + 3 ^ 40 * 1361806 * 2
def baseEnd_1361806 : Nat := 699261036176804161462175

theorem tailTrace_1361806 : CollatzResearch.WordTrace tailWord_1361806 prefixEnd_1361806 699261036176804161462175 := by
  unfold tailWord_1361806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208643163052114349179159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33112763536277943195622181 6208643163052114349179159)
  ·
    refine ⟨9312964744578171523768739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208643163052114349179159 9312964744578171523768739)
    ·
      refine ⟨13969447116867257285653109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9312964744578171523768739 13969447116867257285653109)
      ·
        refine ⟨1309635667206305370529979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13969447116867257285653109 1309635667206305370529979)
        ·
          refine ⟨1964453500809458055794969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309635667206305370529979 1964453500809458055794969)
          ·
            refine ⟨1473340125607093541846227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964453500809458055794969 1473340125607093541846227)
            ·
              refine ⟨2210010188410640312769341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473340125607093541846227 2210010188410640312769341)
              ·
                refine ⟨828753820653990117288503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2210010188410640312769341 828753820653990117288503)
                ·
                  refine ⟨1243130730980985175932755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828753820653990117288503 1243130730980985175932755)
                  ·
                    refine ⟨1864696096471477763899133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1243130730980985175932755 1864696096471477763899133)
                    ·
                      refine ⟨699261036176804161462175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1864696096471477763899133 699261036176804161462175)
                      ·
                        rfl

theorem cell23_1361806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1361806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361806 prefixEnd_1361806 := by exact prefixLift 1361806
  have htrace : WordTrace (prefixWord ++ tailWord_1361806) baseStart_1361806 baseEnd_1361806 := by
    simpa [prefixWord, tailWord_1361806, baseEnd_1361806] using wordTrace_append hprefix tailTrace_1361806
  have hstable : (prefixWord ++ tailWord_1361806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361806).length < 2 ^ (prefixWord ++ tailWord_1361806).sum := by decide
  have hdescent : baseEnd_1361806 < baseStart_1361806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361871 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_1361871 : Nat := 118140960795 + 1361871 * 2 ^ 59
def prefixEnd_1361871 : Nat := 4983230072969 + 3 ^ 40 * 1361871 * 2
def baseEnd_1361871 : Nat := 699294412419346407149375

theorem tailTrace_1361871 : CollatzResearch.WordTrace tailWord_1361871 prefixEnd_1361871 699294412419346407149375 := by
  unfold tailWord_1361871
  simp only [CollatzResearch.WordTrace]
  refine ⟨49671516049181430894549467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33114344032787620596366311 49671516049181430894549467)
  ·
    refine ⟨74507274073772146341824201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49671516049181430894549467 74507274073772146341824201)
    ·
      refine ⟨55880455555329109756368151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74507274073772146341824201 55880455555329109756368151)
      ·
        refine ⟨83820683332993664634552227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55880455555329109756368151 83820683332993664634552227)
        ·
          refine ⟨125731024999490496951828341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83820683332993664634552227 125731024999490496951828341)
          ·
            refine ⟨11787283593702234089233907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125731024999490496951828341 11787283593702234089233907)
            ·
              refine ⟨17680925390553351133850861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787283593702234089233907 17680925390553351133850861)
              ·
                refine ⟨6630347021457506675194073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17680925390553351133850861 6630347021457506675194073)
                ·
                  refine ⟨4972760266093130006395555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6630347021457506675194073 4972760266093130006395555)
                  ·
                    refine ⟨7459140399139695009593333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972760266093130006395555 7459140399139695009593333)
                    ·
                      refine ⟨699294412419346407149375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7459140399139695009593333 699294412419346407149375)
                      ·
                        rfl

theorem cell23_1361871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_1361871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361871 prefixEnd_1361871 := by exact prefixLift 1361871
  have htrace : WordTrace (prefixWord ++ tailWord_1361871) baseStart_1361871 baseEnd_1361871 := by
    simpa [prefixWord, tailWord_1361871, baseEnd_1361871] using wordTrace_append hprefix tailTrace_1361871
  have hstable : (prefixWord ++ tailWord_1361871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361871).length < 2 ^ (prefixWord ++ tailWord_1361871).sum := by decide
  have hdescent : baseEnd_1361871 < baseStart_1361871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361898 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1361898 : Nat := 118140960795 + 1361898 * 2 ^ 59
def prefixEnd_1361898 : Nat := 4983230072969 + 3 ^ 40 * 1361898 * 2
def baseEnd_1361898 : Nat := 699308276397017801511751

theorem tailTrace_1361898 : CollatzResearch.WordTrace tailWord_1361898 prefixEnd_1361898 699308276397017801511751 := by
  unfold tailWord_1361898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418125205020903626445587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33115000546722409670521565 12418125205020903626445587)
  ·
    refine ⟨18627187807531355439668381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12418125205020903626445587 18627187807531355439668381)
    ·
      refine ⟨6985195427824258289875643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18627187807531355439668381 6985195427824258289875643)
      ·
        refine ⟨10477793141736387434813465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985195427824258289875643 10477793141736387434813465)
        ·
          refine ⟨7858344856302290576110099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10477793141736387434813465 7858344856302290576110099)
          ·
            refine ⟨11787517284453435864165149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858344856302290576110099 11787517284453435864165149)
            ·
              refine ⟨4420318981670038449061931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11787517284453435864165149 4420318981670038449061931)
              ·
                refine ⟨6630478472505057673592897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4420318981670038449061931 6630478472505057673592897)
                ·
                  refine ⟨4972858854378793255194673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6630478472505057673592897 4972858854378793255194673)
                  ·
                    refine ⟨3729644140784094941396005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4972858854378793255194673 3729644140784094941396005)
                    ·
                      refine ⟨699308276397017801511751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3729644140784094941396005 699308276397017801511751)
                      ·
                        rfl

theorem cell23_1361898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1361898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361898 prefixEnd_1361898 := by exact prefixLift 1361898
  have htrace : WordTrace (prefixWord ++ tailWord_1361898) baseStart_1361898 baseEnd_1361898 := by
    simpa [prefixWord, tailWord_1361898, baseEnd_1361898] using wordTrace_append hprefix tailTrace_1361898
  have hstable : (prefixWord ++ tailWord_1361898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361898).length < 2 ^ (prefixWord ++ tailWord_1361898).sum := by decide
  have hdescent : baseEnd_1361898 < baseStart_1361898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361902 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_1361902 : Nat := 118140960795 + 1361902 * 2 ^ 59
def prefixEnd_1361902 : Nat := 4983230072969 + 3 ^ 40 * 1361902 * 2
def baseEnd_1361902 : Nat := 699310330319635785861733

theorem tailTrace_1361902 : CollatzResearch.WordTrace tailWord_1361902 prefixEnd_1361902 699310330319635785861733 := by
  unfold tailWord_1361902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209080839008640398615995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33115097808046082125951973 6209080839008640398615995)
  ·
    refine ⟨9313621258512960597923993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6209080839008640398615995 9313621258512960597923993)
    ·
      refine ⟨6985215943884720448442995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9313621258512960597923993 6985215943884720448442995)
      ·
        refine ⟨10477823915827080672664493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985215943884720448442995 10477823915827080672664493)
        ·
          refine ⟨3929183968435155252249185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10477823915827080672664493 3929183968435155252249185)
          ·
            refine ⟨2946887976326366439186889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929183968435155252249185 2946887976326366439186889)
            ·
              refine ⟨2210165982244774829390167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946887976326366439186889 2210165982244774829390167)
              ·
                refine ⟨3315248973367162244085251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210165982244774829390167 3315248973367162244085251)
                ·
                  refine ⟨4972873460050743366127877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315248973367162244085251 4972873460050743366127877)
                  ·
                    refine ⟨932413773759514381148977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972873460050743366127877 932413773759514381148977)
                    ·
                      refine ⟨699310330319635785861733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932413773759514381148977 699310330319635785861733)
                      ·
                        rfl

theorem cell23_1361902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_1361902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361902 prefixEnd_1361902 := by exact prefixLift 1361902
  have htrace : WordTrace (prefixWord ++ tailWord_1361902) baseStart_1361902 baseEnd_1361902 := by
    simpa [prefixWord, tailWord_1361902, baseEnd_1361902] using wordTrace_append hprefix tailTrace_1361902
  have hstable : (prefixWord ++ tailWord_1361902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361902).length < 2 ^ (prefixWord ++ tailWord_1361902).sum := by decide
  have hdescent : baseEnd_1361902 < baseStart_1361902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361925 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 5]
def baseStart_1361925 : Nat := 118140960795 + 1361925 * 2 ^ 59
def prefixEnd_1361925 : Nat := 4983230072969 + 3 ^ 40 * 1361925 * 2
def baseEnd_1361925 : Nat := 77702460041632132874903

theorem tailTrace_1361925 : CollatzResearch.WordTrace tailWord_1361925 prefixEnd_1361925 77702460041632132874903 := by
  unfold tailWord_1361925
  simp only [CollatzResearch.WordTrace]
  refine ⟨49673485590985798117015229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33115657060657198744676819 49673485590985798117015229)
  ·
    refine ⟨18627557096619674293880711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49673485590985798117015229 18627557096619674293880711)
    ·
      refine ⟨27941335644929511440821067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18627557096619674293880711 27941335644929511440821067)
      ·
        refine ⟨41912003467394267161231601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27941335644929511440821067 41912003467394267161231601)
        ·
          refine ⟨31434002600545700370923701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41912003467394267161231601 31434002600545700370923701)
          ·
            refine ⟨2946937743801159409774097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31434002600545700370923701 2946937743801159409774097)
            ·
              refine ⟨2210203307850869557330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946937743801159409774097 2210203307850869557330573)
              ·
                refine ⟨828826240444076083998965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2210203307850869557330573 828826240444076083998965)
                ·
                  refine ⟨77702460041632132874903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 828826240444076083998965 77702460041632132874903)
                  ·
                    rfl

theorem cell23_1361925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_1361925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361925 prefixEnd_1361925 := by exact prefixLift 1361925
  have htrace : WordTrace (prefixWord ++ tailWord_1361925) baseStart_1361925 baseEnd_1361925 := by
    simpa [prefixWord, tailWord_1361925, baseEnd_1361925] using wordTrace_append hprefix tailTrace_1361925
  have hstable : (prefixWord ++ tailWord_1361925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361925).length < 2 ^ (prefixWord ++ tailWord_1361925).sum := by decide
  have hdescent : baseEnd_1361925 < baseStart_1361925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361961 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_1361961 : Nat := 118140960795 + 1361961 * 2 ^ 59
def prefixEnd_1361961 : Nat := 4983230072969 + 3 ^ 40 * 1361961 * 2
def baseEnd_1361961 : Nat := 699340625678251055023961

theorem tailTrace_1361961 : CollatzResearch.WordTrace tailWord_1361961 prefixEnd_1361961 699340625678251055023961 := by
  unfold tailWord_1361961
  simp only [CollatzResearch.WordTrace]
  refine ⟨49674798618855376265325737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33116532412570250843550491 49674798618855376265325737)
  ·
    refine ⟨37256098964141532198994303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49674798618855376265325737 37256098964141532198994303)
    ·
      refine ⟨55884148446212298298491455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37256098964141532198994303 55884148446212298298491455)
      ·
        refine ⟨83826222669318447447737183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55884148446212298298491455 83826222669318447447737183)
        ·
          refine ⟨125739334003977671171605775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83826222669318447447737183 125739334003977671171605775)
          ·
            refine ⟨188609001005966506757408663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125739334003977671171605775 188609001005966506757408663)
            ·
              refine ⟨282913501508949760136112995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188609001005966506757408663 282913501508949760136112995)
              ·
                refine ⟨424370252263424640204169493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282913501508949760136112995 424370252263424640204169493)
                ·
                  refine ⟨19892355574848030009570445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 424370252263424640204169493 19892355574848030009570445)
                  ·
                    refine ⟨7459633340568011253588917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19892355574848030009570445 7459633340568011253588917)
                    ·
                      refine ⟨699340625678251055023961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7459633340568011253588917 699340625678251055023961)
                      ·
                        rfl

theorem cell23_1361961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_1361961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361961 prefixEnd_1361961 := by exact prefixLift 1361961
  have htrace : WordTrace (prefixWord ++ tailWord_1361961) baseStart_1361961 baseEnd_1361961 := by
    simpa [prefixWord, tailWord_1361961, baseEnd_1361961] using wordTrace_append hprefix tailTrace_1361961
  have hstable : (prefixWord ++ tailWord_1361961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361961).length < 2 ^ (prefixWord ++ tailWord_1361961).sum := by decide
  have hdescent : baseEnd_1361961 < baseStart_1361961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361998 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_1361998 : Nat := 118140960795 + 1361998 * 2 ^ 59
def prefixEnd_1361998 : Nat := 4983230072969 + 3 ^ 40 * 1361998 * 2
def baseEnd_1361998 : Nat := 77706624940274156695699

theorem tailTrace_1361998 : CollatzResearch.WordTrace tailWord_1361998 prefixEnd_1361998 77706624940274156695699 := by
  unfold tailWord_1361998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209518514965166448052831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33117432079814221056281765 6209518514965166448052831)
  ·
    refine ⟨9314277772447749672079247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6209518514965166448052831 9314277772447749672079247)
    ·
      refine ⟨13971416658671624508118871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9314277772447749672079247 13971416658671624508118871)
      ·
        refine ⟨20957124988007436762178307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13971416658671624508118871 20957124988007436762178307)
        ·
          refine ⟨31435687482011155143267461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20957124988007436762178307 31435687482011155143267461)
          ·
            refine ⟨5894191402877091589362649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31435687482011155143267461 5894191402877091589362649)
            ·
              refine ⟨4420643552157818692021987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894191402877091589362649 4420643552157818692021987)
              ·
                refine ⟨6630965328236728038032981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4420643552157818692021987 6630965328236728038032981)
                ·
                  refine ⟨77706624940274156695699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6630965328236728038032981 77706624940274156695699)
                  ·
                    rfl

theorem cell23_1361998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_1361998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1361998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1361998 prefixEnd_1361998 := by exact prefixLift 1361998
  have htrace : WordTrace (prefixWord ++ tailWord_1361998) baseStart_1361998 baseEnd_1361998 := by
    simpa [prefixWord, tailWord_1361998, baseEnd_1361998] using wordTrace_append hprefix tailTrace_1361998
  have hstable : (prefixWord ++ tailWord_1361998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361998).length < 2 ^ (prefixWord ++ tailWord_1361998).sum := by decide
  have hdescent : baseEnd_1361998 < baseStart_1361998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362025 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 3]
def baseStart_1362025 : Nat := 118140960795 + 1362025 * 2 ^ 59
def prefixEnd_1362025 : Nat := 4983230072969 + 3 ^ 40 * 1362025 * 2
def baseEnd_1362025 : Nat := 699373488440138804623667

theorem tailTrace_1362025 : CollatzResearch.WordTrace tailWord_1362025 prefixEnd_1362025 699373488440138804623667 := by
  unfold tailWord_1362025
  simp only [CollatzResearch.WordTrace]
  refine ⟨49677132890623515195655529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33118088593749010130437019 49677132890623515195655529)
  ·
    refine ⟨37257849667967636396741647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49677132890623515195655529 37257849667967636396741647)
    ·
      refine ⟨55886774501951454595112471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37257849667967636396741647 55886774501951454595112471)
      ·
        refine ⟨83830161752927181892668707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55886774501951454595112471 83830161752927181892668707)
        ·
          refine ⟨125745242629390772839003061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83830161752927181892668707 125745242629390772839003061)
          ·
            refine ⟨11788616496505384953656537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125745242629390772839003061 11788616496505384953656537)
            ·
              refine ⟨8841462372379038715242403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11788616496505384953656537 8841462372379038715242403)
              ·
                refine ⟨13262193558568558072863605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8841462372379038715242403 13262193558568558072863605)
                ·
                  refine ⟨1243330646115802319330963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13262193558568558072863605 1243330646115802319330963)
                  ·
                    refine ⟨1864995969173703478996445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1243330646115802319330963 1864995969173703478996445)
                    ·
                      refine ⟨699373488440138804623667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1864995969173703478996445 699373488440138804623667)
                      ·
                        rfl

theorem cell23_1362025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_1362025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362025 prefixEnd_1362025 := by exact prefixLift 1362025
  have htrace : WordTrace (prefixWord ++ tailWord_1362025) baseStart_1362025 baseEnd_1362025 := by
    simpa [prefixWord, tailWord_1362025, baseEnd_1362025] using wordTrace_append hprefix tailTrace_1362025
  have hstable : (prefixWord ++ tailWord_1362025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362025).length < 2 ^ (prefixWord ++ tailWord_1362025).sum := by decide
  have hdescent : baseEnd_1362025 < baseStart_1362025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362052 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_1362052 : Nat := 118140960795 + 1362052 * 2 ^ 59
def prefixEnd_1362052 : Nat := 4983230072969 + 3 ^ 40 * 1362052 * 2
def baseEnd_1362052 : Nat := 699387352417810198986043

theorem tailTrace_1362052 : CollatzResearch.WordTrace tailWord_1362052 prefixEnd_1362052 699387352417810198986043 := by
  unfold tailWord_1362052
  simp only [CollatzResearch.WordTrace]
  refine ⟨24839058830762849403444205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33118745107683799204592273 24839058830762849403444205)
  ·
    refine ⟨9314647061536068526291577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24839058830762849403444205 9314647061536068526291577)
    ·
      refine ⟨6985985296152051394718683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9314647061536068526291577 6985985296152051394718683)
      ·
        refine ⟨10478977944228077092078025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985985296152051394718683 10478977944228077092078025)
        ·
          refine ⟨7859233458171057819058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10478977944228077092078025 7859233458171057819058519)
          ·
            refine ⟨11788850187256586728587779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7859233458171057819058519 11788850187256586728587779)
            ·
              refine ⟨17683275280884880092881669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11788850187256586728587779 17683275280884880092881669)
              ·
                refine ⟨3315614115165915017415313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17683275280884880092881669 3315614115165915017415313)
                ·
                  refine ⟨2486710586374436263061485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3315614115165915017415313 2486710586374436263061485)
                  ·
                    refine ⟨932516469890413598648057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486710586374436263061485 932516469890413598648057)
                    ·
                      refine ⟨699387352417810198986043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932516469890413598648057 699387352417810198986043)
                      ·
                        rfl

theorem cell23_1362052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_1362052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362052 prefixEnd_1362052 := by exact prefixLift 1362052
  have htrace : WordTrace (prefixWord ++ tailWord_1362052) baseStart_1362052 baseEnd_1362052 := by
    simpa [prefixWord, tailWord_1362052, baseEnd_1362052] using wordTrace_append hprefix tailTrace_1362052
  have hstable : (prefixWord ++ tailWord_1362052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362052).length < 2 ^ (prefixWord ++ tailWord_1362052).sum := by decide
  have hdescent : baseEnd_1362052 < baseStart_1362052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 2, 4]
def baseStart_1362075 : Nat := 118140960795 + 1362075 * 2 ^ 59
def prefixEnd_1362075 : Nat := 4983230072969 + 3 ^ 40 * 1362075 * 2
def baseEnd_1362075 : Nat := 233133054157621202999479

theorem tailTrace_1362075 : CollatzResearch.WordTrace tailWord_1362075 prefixEnd_1362075 233133054157621202999479 := by
  unfold tailWord_1362075
  simp only [CollatzResearch.WordTrace]
  refine ⟨49678956540442373734975679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33119304360294915823317119 49678956540442373734975679)
  ·
    refine ⟨74518434810663560602463519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49678956540442373734975679 74518434810663560602463519)
    ·
      refine ⟨111777652215995340903695279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74518434810663560602463519 111777652215995340903695279)
      ·
        refine ⟨167666478323993011355542919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111777652215995340903695279 167666478323993011355542919)
        ·
          refine ⟨251499717485989517033314379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167666478323993011355542919 251499717485989517033314379)
          ·
            refine ⟨377249576228984275549971569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251499717485989517033314379 377249576228984275549971569)
            ·
              refine ⟨282937182171738206662478677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377249576228984275549971569 282937182171738206662478677)
              ·
                refine ⟨1657835051787528554662961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 282937182171738206662478677 1657835051787528554662961)
                ·
                  refine ⟨1243376288840646415997221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1657835051787528554662961 1243376288840646415997221)
                  ·
                    refine ⟨233133054157621202999479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243376288840646415997221 233133054157621202999479)
                    ·
                      rfl

theorem cell23_1362075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 4].length) (baseStart_1362075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362075 prefixEnd_1362075 := by exact prefixLift 1362075
  have htrace : WordTrace (prefixWord ++ tailWord_1362075) baseStart_1362075 baseEnd_1362075 := by
    simpa [prefixWord, tailWord_1362075, baseEnd_1362075] using wordTrace_append hprefix tailTrace_1362075
  have hstable : (prefixWord ++ tailWord_1362075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362075).length < 2 ^ (prefixWord ++ tailWord_1362075).sum := by decide
  have hdescent : baseEnd_1362075 < baseStart_1362075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362082 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1362082 : Nat := 118140960795 + 1362082 * 2 ^ 59
def prefixEnd_1362082 : Nat := 4983230072969 + 3 ^ 40 * 1362082 * 2
def baseEnd_1362082 : Nat := 699402756837445081610905

theorem tailTrace_1362082 : CollatzResearch.WordTrace tailWord_1362082 prefixEnd_1362082 699402756837445081610905 := by
  unfold tailWord_1362082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419802962854253482620125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33119474567611342620320333 12419802962854253482620125)
  ·
    refine ⟨4657426111070345055982547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12419802962854253482620125 4657426111070345055982547)
    ·
      refine ⟨6986139166605517583973821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657426111070345055982547 6986139166605517583973821)
      ·
        refine ⟨2619802187477069093990183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6986139166605517583973821 2619802187477069093990183)
        ·
          refine ⟨3929703281215603640985275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619802187477069093990183 3929703281215603640985275)
          ·
            refine ⟨5894554921823405461477913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929703281215603640985275 5894554921823405461477913)
            ·
              refine ⟨4420916191367554096108435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894554921823405461477913 4420916191367554096108435)
              ·
                refine ⟨6631374287051331144162653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4420916191367554096108435 6631374287051331144162653)
                ·
                  refine ⟨2486765357644249179060995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6631374287051331144162653 2486765357644249179060995)
                  ·
                    refine ⟨3730148036466373768591493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2486765357644249179060995 3730148036466373768591493)
                    ·
                      refine ⟨699402756837445081610905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3730148036466373768591493 699402756837445081610905)
                      ·
                        rfl

theorem cell23_1362082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1362082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362082 prefixEnd_1362082 := by exact prefixLift 1362082
  have htrace : WordTrace (prefixWord ++ tailWord_1362082) baseStart_1362082 baseEnd_1362082 := by
    simpa [prefixWord, tailWord_1362082, baseEnd_1362082] using wordTrace_append hprefix tailTrace_1362082
  have hstable : (prefixWord ++ tailWord_1362082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362082).length < 2 ^ (prefixWord ++ tailWord_1362082).sum := by decide
  have hdescent : baseEnd_1362082 < baseStart_1362082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362085 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_1362085 : Nat := 118140960795 + 1362085 * 2 ^ 59
def prefixEnd_1362085 : Nat := 4983230072969 + 3 ^ 40 * 1362085 * 2
def baseEnd_1362085 : Nat := 699404297279408569873391

theorem tailTrace_1362085 : CollatzResearch.WordTrace tailWord_1362085 prefixEnd_1362085 699404297279408569873391 := by
  unfold tailWord_1362085
  simp only [CollatzResearch.WordTrace]
  refine ⟨49679321270406145442839709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33119547513604096961893139 49679321270406145442839709)
  ·
    refine ⟨18629745476402304541064891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49679321270406145442839709 18629745476402304541064891)
    ·
      refine ⟨27944618214603456811597337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18629745476402304541064891 27944618214603456811597337)
      ·
        refine ⟨20958463660952592608698003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27944618214603456811597337 20958463660952592608698003)
        ·
          refine ⟨31437695491428888913047005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20958463660952592608698003 31437695491428888913047005)
          ·
            refine ⟨11789135809285833342392627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31437695491428888913047005 11789135809285833342392627)
            ·
              refine ⟨17683703713928750013588941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11789135809285833342392627 17683703713928750013588941)
              ·
                refine ⟨6631388892723281255095853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17683703713928750013588941 6631388892723281255095853)
                ·
                  refine ⟨2486770834771230470660945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6631388892723281255095853 2486770834771230470660945)
                  ·
                    refine ⟨1865078126078422852995709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2486770834771230470660945 1865078126078422852995709)
                    ·
                      refine ⟨699404297279408569873391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1865078126078422852995709 699404297279408569873391)
                      ·
                        rfl

theorem cell23_1362085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_1362085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362085 prefixEnd_1362085 := by exact prefixLift 1362085
  have htrace : WordTrace (prefixWord ++ tailWord_1362085) baseStart_1362085 baseEnd_1362085 := by
    simpa [prefixWord, tailWord_1362085, baseEnd_1362085] using wordTrace_append hprefix tailTrace_1362085
  have hstable : (prefixWord ++ tailWord_1362085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362085).length < 2 ^ (prefixWord ++ tailWord_1362085).sum := by decide
  have hdescent : baseEnd_1362085 < baseStart_1362085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362116 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_1362116 : Nat := 118140960795 + 1362116 * 2 ^ 59
def prefixEnd_1362116 : Nat := 4983230072969 + 3 ^ 40 * 1362116 * 2
def baseEnd_1362116 : Nat := 699420215179697948585749

theorem tailTrace_1362116 : CollatzResearch.WordTrace tailWord_1362116 prefixEnd_1362116 699420215179697948585749 := by
  unfold tailWord_1362116
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840225966646918868609101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33120301288862558491478801 24840225966646918868609101)
  ·
    refine ⟨9315084737492594575728413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24840225966646918868609101 9315084737492594575728413)
    ·
      refine ⟨3493156776559722965898155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9315084737492594575728413 3493156776559722965898155)
      ·
        refine ⟨5239735164839584448847233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3493156776559722965898155 5239735164839584448847233)
        ·
          refine ⟨3929801373629688336635425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5239735164839584448847233 3929801373629688336635425)
          ·
            refine ⟨2947351030222266252476569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929801373629688336635425 2947351030222266252476569)
            ·
              refine ⟨2210513272666699689357427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947351030222266252476569 2210513272666699689357427)
              ·
                refine ⟨3315769909000049534036141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210513272666699689357427 3315769909000049534036141)
                ·
                  refine ⟨1243413715875018575263553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3315769909000049534036141 1243413715875018575263553)
                  ·
                    refine ⟨932560286906263931447665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1243413715875018575263553 932560286906263931447665)
                    ·
                      refine ⟨699420215179697948585749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932560286906263931447665 699420215179697948585749)
                      ·
                        rfl

theorem cell23_1362116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_1362116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362116 prefixEnd_1362116 := by exact prefixLift 1362116
  have htrace : WordTrace (prefixWord ++ tailWord_1362116) baseStart_1362116 baseEnd_1362116 := by
    simpa [prefixWord, tailWord_1362116, baseEnd_1362116] using wordTrace_append hprefix tailTrace_1362116
  have hstable : (prefixWord ++ tailWord_1362116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362116).length < 2 ^ (prefixWord ++ tailWord_1362116).sum := by decide
  have hdescent : baseEnd_1362116 < baseStart_1362116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362128 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1362128 : Nat := 118140960795 + 1362128 * 2 ^ 59
def prefixEnd_1362128 : Nat := 4983230072969 + 3 ^ 40 * 1362128 * 2
def baseEnd_1362128 : Nat := 699426376947551901635693

theorem tailTrace_1362128 : CollatzResearch.WordTrace tailWord_1362128 prefixEnd_1362128 699426376947551901635693 := by
  unfold tailWord_1362128
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840444804625181893327519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33120593072833575857770025 24840444804625181893327519)
  ·
    refine ⟨37260667206937772839991279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24840444804625181893327519 37260667206937772839991279)
    ·
      refine ⟨55891000810406659259986919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37260667206937772839991279 55891000810406659259986919)
      ·
        refine ⟨83836501215609988889980379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55891000810406659259986919 83836501215609988889980379)
        ·
          refine ⟨125754751823414983334970569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83836501215609988889980379 125754751823414983334970569)
          ·
            refine ⟨94316063867561237501227927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125754751823414983334970569 94316063867561237501227927)
            ·
              refine ⟨141474095801341856251841891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94316063867561237501227927 141474095801341856251841891)
              ·
                refine ⟨212211143702012784377762837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141474095801341856251841891 212211143702012784377762837)
                ·
                  refine ⟨9947397361031849267707633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212211143702012784377762837 9947397361031849267707633)
                  ·
                    refine ⟨7460548020773886950780725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9947397361031849267707633 7460548020773886950780725)
                    ·
                      refine ⟨699426376947551901635693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7460548020773886950780725 699426376947551901635693)
                      ·
                        rfl

theorem cell23_1362128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1362128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362128 prefixEnd_1362128 := by exact prefixLift 1362128
  have htrace : WordTrace (prefixWord ++ tailWord_1362128) baseStart_1362128 baseEnd_1362128 := by
    simpa [prefixWord, tailWord_1362128, baseEnd_1362128] using wordTrace_append hprefix tailTrace_1362128
  have hstable : (prefixWord ++ tailWord_1362128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362128).length < 2 ^ (prefixWord ++ tailWord_1362128).sum := by decide
  have hdescent : baseEnd_1362128 < baseStart_1362128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362159 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 1, 3, 2]
def baseStart_1362159 : Nat := 118140960795 + 1362159 * 2 ^ 59
def prefixEnd_1362159 : Nat := 4983230072969 + 3 ^ 40 * 1362159 * 2
def baseEnd_1362159 : Nat := 699442294847841280348051

theorem tailTrace_1362159 : CollatzResearch.WordTrace tailWord_1362159 prefixEnd_1362159 699442294847841280348051 := by
  unfold tailWord_1362159
  simp only [CollatzResearch.WordTrace]
  refine ⟨49682020272138056081033531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33121346848092037387355687 49682020272138056081033531)
  ·
    refine ⟨74523030408207084121550297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49682020272138056081033531 74523030408207084121550297)
    ·
      refine ⟨55892272806155313091162723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74523030408207084121550297 55892272806155313091162723)
      ·
        refine ⟨83838409209232969636744085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55892272806155313091162723 83838409209232969636744085)
        ·
          refine ⟨3929925431682795451722379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83838409209232969636744085 3929925431682795451722379)
          ·
            refine ⟨5894888147524193177583569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929925431682795451722379 5894888147524193177583569)
            ·
              refine ⟨4421166110643144883187677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894888147524193177583569 4421166110643144883187677)
              ·
                refine ⟨1657937291491179331195379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4421166110643144883187677 1657937291491179331195379)
                ·
                  refine ⟨2486905937236768996793069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657937291491179331195379 2486905937236768996793069)
                  ·
                    refine ⟨932589726463788373797401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486905937236768996793069 932589726463788373797401)
                    ·
                      refine ⟨699442294847841280348051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932589726463788373797401 699442294847841280348051)
                      ·
                        rfl

theorem cell23_1362159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3, 2].length) (baseStart_1362159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362159 prefixEnd_1362159 := by exact prefixLift 1362159
  have htrace : WordTrace (prefixWord ++ tailWord_1362159) baseStart_1362159 baseEnd_1362159 := by
    simpa [prefixWord, tailWord_1362159, baseEnd_1362159] using wordTrace_append hprefix tailTrace_1362159
  have hstable : (prefixWord ++ tailWord_1362159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362159).length < 2 ^ (prefixWord ++ tailWord_1362159).sum := by decide
  have hdescent : baseEnd_1362159 < baseStart_1362159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362175 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_1362175 : Nat := 118140960795 + 1362175 * 2 ^ 59
def prefixEnd_1362175 : Nat := 4983230072969 + 3 ^ 40 * 1362175 * 2
def baseEnd_1362175 : Nat := 699450510538313217747977

theorem tailTrace_1362175 : CollatzResearch.WordTrace tailWord_1362175 prefixEnd_1362175 699450510538313217747977 := by
  unfold tailWord_1362175
  simp only [CollatzResearch.WordTrace]
  refine ⟨49682603840080090813615979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33121735893386727209077319 49682603840080090813615979)
  ·
    refine ⟨74523905760120136220423969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49682603840080090813615979 74523905760120136220423969)
    ·
      refine ⟨55892929320090102165317977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74523905760120136220423969 55892929320090102165317977)
      ·
        refine ⟨41919696990067576623988483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55892929320090102165317977 41919696990067576623988483)
        ·
          refine ⟨62879545485101364935982725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41919696990067576623988483 62879545485101364935982725)
          ·
            refine ⟨11789914778456505925496761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62879545485101364935982725 11789914778456505925496761)
            ·
              refine ⟨8842436083842379444122571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11789914778456505925496761 8842436083842379444122571)
              ·
                refine ⟨13263654125763569166183857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8842436083842379444122571 13263654125763569166183857)
                ·
                  refine ⟨9947740594322676874637893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13263654125763569166183857 9947740594322676874637893)
                  ·
                    refine ⟨1865201361435501913994605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9947740594322676874637893 1865201361435501913994605)
                    ·
                      refine ⟨699450510538313217747977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1865201361435501913994605 699450510538313217747977)
                      ·
                        rfl

theorem cell23_1362175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_1362175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362175 prefixEnd_1362175 := by exact prefixLift 1362175
  have htrace : WordTrace (prefixWord ++ tailWord_1362175) baseStart_1362175 baseEnd_1362175 := by
    simpa [prefixWord, tailWord_1362175, baseEnd_1362175] using wordTrace_append hprefix tailTrace_1362175
  have hstable : (prefixWord ++ tailWord_1362175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362175).length < 2 ^ (prefixWord ++ tailWord_1362175).sum := by decide
  have hdescent : baseEnd_1362175 < baseStart_1362175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362206 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1362206 : Nat := 118140960795 + 1362206 * 2 ^ 59
def prefixEnd_1362206 : Nat := 4983230072969 + 3 ^ 40 * 1362206 * 2
def baseEnd_1362206 : Nat := 699466428438602596460335

theorem tailTrace_1362206 : CollatzResearch.WordTrace tailWord_1362206 prefixEnd_1362206 699466428438602596460335 := by
  unfold tailWord_1362206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210466812870972888499309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33122489668645188738662981 6210466812870972888499309)
  ·
    refine ⟨2328925054826614833187241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6210466812870972888499309 2328925054826614833187241)
    ·
      refine ⟨1746693791119961124890431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2328925054826614833187241 1746693791119961124890431)
      ·
        refine ⟨2620040686679941687335647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746693791119961124890431 2620040686679941687335647)
        ·
          refine ⟨3930061030019912531003471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620040686679941687335647 3930061030019912531003471)
          ·
            refine ⟨5895091545029868796505207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930061030019912531003471 5895091545029868796505207)
            ·
              refine ⟨8842637317544803194757811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895091545029868796505207 8842637317544803194757811)
              ·
                refine ⟨13263955976317204792136717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8842637317544803194757811 13263955976317204792136717)
                ·
                  refine ⟨4973983491118951797051269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13263955976317204792136717 4973983491118951797051269)
                  ·
                    refine ⟨932621904584803461947113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973983491118951797051269 932621904584803461947113)
                    ·
                      refine ⟨699466428438602596460335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932621904584803461947113 699466428438602596460335)
                      ·
                        rfl

theorem cell23_1362206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1362206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362206 prefixEnd_1362206 := by exact prefixLift 1362206
  have htrace : WordTrace (prefixWord ++ tailWord_1362206) baseStart_1362206 baseEnd_1362206 := by
    simpa [prefixWord, tailWord_1362206, baseEnd_1362206] using wordTrace_append hprefix tailTrace_1362206
  have hstable : (prefixWord ++ tailWord_1362206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362206).length < 2 ^ (prefixWord ++ tailWord_1362206).sum := by decide
  have hdescent : baseEnd_1362206 < baseStart_1362206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362232 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_1362232 : Nat := 118140960795 + 1362232 * 2 ^ 59
def prefixEnd_1362232 : Nat := 4983230072969 + 3 ^ 40 * 1362232 * 2
def baseEnd_1362232 : Nat := 699479778935619494735215

theorem tailTrace_1362232 : CollatzResearch.WordTrace tailWord_1362232 prefixEnd_1362232 699479778935619494735215 := by
  unfold tailWord_1362232
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842341400436794774220475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33123121867249059698960633 24842341400436794774220475)
  ·
    refine ⟨37263512100655192161330713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24842341400436794774220475 37263512100655192161330713)
    ·
      refine ⟨27947634075491394120998035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37263512100655192161330713 27947634075491394120998035)
      ·
        refine ⟨41921451113237091181497053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27947634075491394120998035 41921451113237091181497053)
        ·
          refine ⟨15720544167463909193061395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41921451113237091181497053 15720544167463909193061395)
          ·
            refine ⟨23580816251195863789592093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15720544167463909193061395 23580816251195863789592093)
            ·
              refine ⟨8842806094198448921097035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23580816251195863789592093 8842806094198448921097035)
              ·
                refine ⟨13264209141297673381645553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8842806094198448921097035 13264209141297673381645553)
                ·
                  refine ⟨9948156855973255036234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13264209141297673381645553 9948156855973255036234165)
                  ·
                    refine ⟨932639705247492659646953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9948156855973255036234165 932639705247492659646953)
                    ·
                      refine ⟨699479778935619494735215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932639705247492659646953 699479778935619494735215)
                      ·
                        rfl

theorem cell23_1362232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_1362232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362232 prefixEnd_1362232 := by exact prefixLift 1362232
  have htrace : WordTrace (prefixWord ++ tailWord_1362232) baseStart_1362232 baseEnd_1362232 := by
    simpa [prefixWord, tailWord_1362232, baseEnd_1362232] using wordTrace_append hprefix tailTrace_1362232
  have hstable : (prefixWord ++ tailWord_1362232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362232).length < 2 ^ (prefixWord ++ tailWord_1362232).sum := by decide
  have hdescent : baseEnd_1362232 < baseStart_1362232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362275 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1362275 : Nat := 118140960795 + 1362275 * 2 ^ 59
def prefixEnd_1362275 : Nat := 4983230072969 + 3 ^ 40 * 1362275 * 2
def baseEnd_1362275 : Nat := 699501858603762826497517

theorem tailTrace_1362275 : CollatzResearch.WordTrace tailWord_1362275 prefixEnd_1362275 699501858603762826497517 := by
  unfold tailWord_1362275
  simp only [CollatzResearch.WordTrace]
  refine ⟨49686251139717807892256279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33124167426478538594837519 49686251139717807892256279)
  ·
    refine ⟨74529376709576711838384419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49686251139717807892256279 74529376709576711838384419)
    ·
      refine ⟨111794065064365067757576629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74529376709576711838384419 111794065064365067757576629)
      ·
        refine ⟨10480693599784225102272809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111794065064365067757576629 10480693599784225102272809)
        ·
          refine ⟨7860520199838168826704607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10480693599784225102272809 7860520199838168826704607)
          ·
            refine ⟨11790780299757253240056911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860520199838168826704607 11790780299757253240056911)
            ·
              refine ⟨17686170449635879860085367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11790780299757253240056911 17686170449635879860085367)
              ·
                refine ⟨26529255674453819790128051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17686170449635879860085367 26529255674453819790128051)
                ·
                  refine ⟨39793883511680729685192077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26529255674453819790128051 39793883511680729685192077)
                  ·
                    refine ⟨14922706316880273631947029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39793883511680729685192077 14922706316880273631947029)
                    ·
                      refine ⟨699501858603762826497517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14922706316880273631947029 699501858603762826497517)
                      ·
                        rfl

theorem cell23_1362275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1362275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362275 prefixEnd_1362275 := by exact prefixLift 1362275
  have htrace : WordTrace (prefixWord ++ tailWord_1362275) baseStart_1362275 baseEnd_1362275 := by
    simpa [prefixWord, tailWord_1362275, baseEnd_1362275] using wordTrace_append hprefix tailTrace_1362275
  have hstable : (prefixWord ++ tailWord_1362275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362275).length < 2 ^ (prefixWord ++ tailWord_1362275).sum := by decide
  have hdescent : baseEnd_1362275 < baseStart_1362275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362279 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_1362279 : Nat := 118140960795 + 1362279 * 2 ^ 59
def prefixEnd_1362279 : Nat := 4983230072969 + 3 ^ 40 * 1362279 * 2
def baseEnd_1362279 : Nat := 699503912526380810847499

theorem tailTrace_1362279 : CollatzResearch.WordTrace tailWord_1362279 prefixEnd_1362279 699503912526380810847499 := by
  unfold tailWord_1362279
  simp only [CollatzResearch.WordTrace]
  refine ⟨49686397031703316575401891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33124264687802211050267927 49686397031703316575401891)
  ·
    refine ⟨74529595547554974863102837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49686397031703316575401891 74529595547554974863102837)
    ·
      refine ⟨6987149582583278893415891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74529595547554974863102837 6987149582583278893415891)
      ·
        refine ⟨10480724373874918340123837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987149582583278893415891 10480724373874918340123837)
        ·
          refine ⟨3930271640203094377546439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10480724373874918340123837 3930271640203094377546439)
          ·
            refine ⟨5895407460304641566319659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930271640203094377546439 5895407460304641566319659)
            ·
              refine ⟨8843111190456962349479489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895407460304641566319659 8843111190456962349479489)
              ·
                refine ⟨6632333392842721762109617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843111190456962349479489 6632333392842721762109617)
                ·
                  refine ⟨4974250044632041321582213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6632333392842721762109617 4974250044632041321582213)
                  ·
                    refine ⟨932671883368507747796665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974250044632041321582213 932671883368507747796665)
                    ·
                      refine ⟨699503912526380810847499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932671883368507747796665 699503912526380810847499)
                      ·
                        rfl

theorem cell23_1362279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_1362279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362279 prefixEnd_1362279 := by exact prefixLift 1362279
  have htrace : WordTrace (prefixWord ++ tailWord_1362279) baseStart_1362279 baseEnd_1362279 := by
    simpa [prefixWord, tailWord_1362279, baseEnd_1362279] using wordTrace_append hprefix tailTrace_1362279
  have hstable : (prefixWord ++ tailWord_1362279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362279).length < 2 ^ (prefixWord ++ tailWord_1362279).sum := by decide
  have hdescent : baseEnd_1362279 < baseStart_1362279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362312 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1362312 : Nat := 118140960795 + 1362312 * 2 ^ 59
def prefixEnd_1362312 : Nat := 4983230072969 + 3 ^ 40 * 1362312 * 2
def baseEnd_1362312 : Nat := 699520857387979181734847

theorem tailTrace_1362312 : CollatzResearch.WordTrace tailWord_1362312 prefixEnd_1362312 699520857387979181734847 := by
  unfold tailWord_1362312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24843800320291881605676595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33125067093722508807568793 24843800320291881605676595)
  ·
    refine ⟨37265700480437822408514893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24843800320291881605676595 37265700480437822408514893)
    ·
      refine ⟨13974637680164183403193085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37265700480437822408514893 13974637680164183403193085)
      ·
        refine ⟨5240489130061568776197407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13974637680164183403193085 5240489130061568776197407)
        ·
          refine ⟨7860733695092353164296111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5240489130061568776197407 7860733695092353164296111)
          ·
            refine ⟨11791100542638529746444167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860733695092353164296111 11791100542638529746444167)
            ·
              refine ⟨17686650813957794619666251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11791100542638529746444167 17686650813957794619666251)
              ·
                refine ⟨26529976220936691929499377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17686650813957794619666251 26529976220936691929499377)
                ·
                  refine ⟨19897482165702518947124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26529976220936691929499377 19897482165702518947124533)
                  ·
                    refine ⟨1865388953034611151292925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19897482165702518947124533 1865388953034611151292925)
                    ·
                      refine ⟨699520857387979181734847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1865388953034611151292925 699520857387979181734847)
                      ·
                        rfl

theorem cell23_1362312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1362312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362312 prefixEnd_1362312 := by exact prefixLift 1362312
  have htrace : WordTrace (prefixWord ++ tailWord_1362312) baseStart_1362312 baseEnd_1362312 := by
    simpa [prefixWord, tailWord_1362312, baseEnd_1362312] using wordTrace_append hprefix tailTrace_1362312
  have hstable : (prefixWord ++ tailWord_1362312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362312).length < 2 ^ (prefixWord ++ tailWord_1362312).sum := by decide
  have hdescent : baseEnd_1362312 < baseStart_1362312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362339 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 4, 3, 2]
def baseStart_1362339 : Nat := 118140960795 + 1362339 * 2 ^ 59
def prefixEnd_1362339 : Nat := 4983230072969 + 3 ^ 40 * 1362339 * 2
def baseEnd_1362339 : Nat := 699534721365650576097223

theorem tailTrace_1362339 : CollatzResearch.WordTrace tailWord_1362339 prefixEnd_1362339 699534721365650576097223 := by
  unfold tailWord_1362339
  simp only [CollatzResearch.WordTrace]
  refine ⟨49688585411485946822586071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33125723607657297881724047 49688585411485946822586071)
  ·
    refine ⟨74532878117228920233879107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49688585411485946822586071 74532878117228920233879107)
    ·
      refine ⟨111799317175843380350818661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74532878117228920233879107 111799317175843380350818661)
      ·
        refine ⟨20962371970470633815778499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111799317175843380350818661 20962371970470633815778499)
        ·
          refine ⟨31443557955705950723667749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20962371970470633815778499 31443557955705950723667749)
          ·
            refine ⟨5895667116694865760687703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31443557955705950723667749 5895667116694865760687703)
            ·
              refine ⟨8843500675042298641031555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895667116694865760687703 8843500675042298641031555)
              ·
                refine ⟨13265251012563447961547333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8843500675042298641031555 13265251012563447961547333)
                ·
                  refine ⟨2487234564855646492790125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13265251012563447961547333 2487234564855646492790125)
                  ·
                    refine ⟨932712961820867434796297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487234564855646492790125 932712961820867434796297)
                    ·
                      refine ⟨699534721365650576097223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932712961820867434796297 699534721365650576097223)
                      ·
                        rfl

theorem cell23_1362339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_1362339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362339 prefixEnd_1362339 := by exact prefixLift 1362339
  have htrace : WordTrace (prefixWord ++ tailWord_1362339) baseStart_1362339 baseEnd_1362339 := by
    simpa [prefixWord, tailWord_1362339, baseEnd_1362339] using wordTrace_append hprefix tailTrace_1362339
  have hstable : (prefixWord ++ tailWord_1362339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362339).length < 2 ^ (prefixWord ++ tailWord_1362339).sum := by decide
  have hdescent : baseEnd_1362339 < baseStart_1362339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362389 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1362389 : Nat := 118140960795 + 1362389 * 2 ^ 59
def prefixEnd_1362389 : Nat := 4983230072969 + 3 ^ 40 * 1362389 * 2
def baseEnd_1362389 : Nat := 699560395398375380471993

theorem tailTrace_1362389 : CollatzResearch.WordTrace tailWord_1362389 prefixEnd_1362389 699560395398375380471993 := by
  unfold tailWord_1362389
  simp only [CollatzResearch.WordTrace]
  refine ⟨49690409061304805361906221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33126939374203203574604147 49690409061304805361906221)
  ·
    refine ⟨18633903397989302010714833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49690409061304805361906221 18633903397989302010714833)
    ·
      refine ⟨13975427548491976508036125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18633903397989302010714833 13975427548491976508036125)
      ·
        refine ⟨5240785330684491190513547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13975427548491976508036125 5240785330684491190513547)
        ·
          refine ⟨7861177996026736785770321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5240785330684491190513547 7861177996026736785770321)
          ·
            refine ⟨5895883497020052589327741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7861177996026736785770321 5895883497020052589327741)
            ·
              refine ⟨2210956311382519720997903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5895883497020052589327741 2210956311382519720997903)
              ·
                refine ⟨3316434467073779581496855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210956311382519720997903 3316434467073779581496855)
                ·
                  refine ⟨4974651700610669372245283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316434467073779581496855 4974651700610669372245283)
                  ·
                    refine ⟨7461977550916004058367925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4974651700610669372245283 7461977550916004058367925)
                    ·
                      refine ⟨699560395398375380471993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7461977550916004058367925 699560395398375380471993)
                      ·
                        rfl

theorem cell23_1362389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1362389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362389 prefixEnd_1362389 := by exact prefixLift 1362389
  have htrace : WordTrace (prefixWord ++ tailWord_1362389) baseStart_1362389 baseEnd_1362389 := by
    simpa [prefixWord, tailWord_1362389, baseEnd_1362389] using wordTrace_append hprefix tailTrace_1362389
  have hstable : (prefixWord ++ tailWord_1362389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362389).length < 2 ^ (prefixWord ++ tailWord_1362389).sum := by decide
  have hdescent : baseEnd_1362389 < baseStart_1362389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362419 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3]
def baseStart_1362419 : Nat := 118140960795 + 1362419 * 2 ^ 59
def prefixEnd_1362419 : Nat := 4983230072969 + 3 ^ 40 * 1362419 * 2
def baseEnd_1362419 : Nat := 699575799818010263096855

theorem tailTrace_1362419 : CollatzResearch.WordTrace tailWord_1362419 prefixEnd_1362419 699575799818010263096855 := by
  unfold tailWord_1362419
  simp only [CollatzResearch.WordTrace]
  refine ⟨49691503251196120485498311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33127668834130746990332207 49691503251196120485498311)
  ·
    refine ⟨74537254876794180728247467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49691503251196120485498311 74537254876794180728247467)
    ·
      refine ⟨111805882315191271092371201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74537254876794180728247467 111805882315191271092371201)
      ·
        refine ⟨83854411736393453319278401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111805882315191271092371201 83854411736393453319278401)
        ·
          refine ⟨62890808802295089989458801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83854411736393453319278401 62890808802295089989458801)
          ·
            refine ⟨47168106601721317492094101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62890808802295089989458801 47168106601721317492094101)
            ·
              refine ⟨2211004996955686757441911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47168106601721317492094101 2211004996955686757441911)
              ·
                refine ⟨3316507495433530136162867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211004996955686757441911 3316507495433530136162867)
                ·
                  refine ⟨4974761243150295204244301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316507495433530136162867 4974761243150295204244301)
                  ·
                    refine ⟨1865535466181360701591613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4974761243150295204244301 1865535466181360701591613)
                    ·
                      refine ⟨699575799818010263096855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1865535466181360701591613 699575799818010263096855)
                      ·
                        rfl

theorem cell23_1362419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_1362419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362419 prefixEnd_1362419 := by exact prefixLift 1362419
  have htrace : WordTrace (prefixWord ++ tailWord_1362419) baseStart_1362419 baseEnd_1362419 := by
    simpa [prefixWord, tailWord_1362419, baseEnd_1362419] using wordTrace_append hprefix tailTrace_1362419
  have hstable : (prefixWord ++ tailWord_1362419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362419).length < 2 ^ (prefixWord ++ tailWord_1362419).sum := by decide
  have hdescent : baseEnd_1362419 < baseStart_1362419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362436 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1362436 : Nat := 118140960795 + 1362436 * 2 ^ 59
def prefixEnd_1362436 : Nat := 4983230072969 + 3 ^ 40 * 1362436 * 2
def baseEnd_1362436 : Nat := 699584528989136696584277

theorem tailTrace_1362436 : CollatzResearch.WordTrace tailWord_1362436 prefixEnd_1362436 699584528989136696584277 := by
  unfold tailWord_1362436
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846061646067266194433581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33128082194756354925911441 24846061646067266194433581)
  ·
    refine ⟨9317273117275224822912593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24846061646067266194433581 9317273117275224822912593)
    ·
      refine ⟨6987954837956418617184445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9317273117275224822912593 6987954837956418617184445)
      ·
        refine ⟨2620483064233656981444167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6987954837956418617184445 2620483064233656981444167)
        ·
          refine ⟨3930724596350485472166251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620483064233656981444167 3930724596350485472166251)
          ·
            refine ⟨5896086894525728208249377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930724596350485472166251 5896086894525728208249377)
            ·
              refine ⟨4422065170894296156187033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5896086894525728208249377 4422065170894296156187033)
              ·
                refine ⟨3316548878170722117140275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422065170894296156187033 3316548878170722117140275)
                ·
                  refine ⟨4974823317256083175710413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316548878170722117140275 4974823317256083175710413)
                  ·
                    refine ⟨1865558743971031190891405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4974823317256083175710413 1865558743971031190891405)
                    ·
                      refine ⟨699584528989136696584277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1865558743971031190891405 699584528989136696584277)
                      ·
                        rfl

theorem cell23_1362436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1362436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362436 prefixEnd_1362436 := by exact prefixLift 1362436
  have htrace : WordTrace (prefixWord ++ tailWord_1362436) baseStart_1362436 baseEnd_1362436 := by
    simpa [prefixWord, tailWord_1362436, baseEnd_1362436] using wordTrace_append hprefix tailTrace_1362436
  have hstable : (prefixWord ++ tailWord_1362436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362436).length < 2 ^ (prefixWord ++ tailWord_1362436).sum := by decide
  have hdescent : baseEnd_1362436 < baseStart_1362436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362477 : List Nat := [1, 5, 4, 1, 2, 1, 2, 7]
def baseStart_1362477 : Nat := 118140960795 + 1362477 * 2 ^ 59
def prefixEnd_1362477 : Nat := 4983230072969 + 3 ^ 40 * 1362477 * 2
def baseEnd_1362477 : Nat := 25911317840591519858207

theorem tailTrace_1362477 : CollatzResearch.WordTrace tailWord_1362477 prefixEnd_1362477 25911317840591519858207 := by
  unfold tailWord_1362477
  simp only [CollatzResearch.WordTrace]
  refine ⟨49693618684985996391109685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33129079123323997594073123 49693618684985996391109685)
  ·
    refine ⟨4658776751717437161666533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49693618684985996391109685 4658776751717437161666533)
    ·
      refine ⟨873520640947019467812475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4658776751717437161666533 873520640947019467812475)
      ·
        refine ⟨1310280961420529201718713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873520640947019467812475 1310280961420529201718713)
        ·
          refine ⟨982710721065396901289035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310280961420529201718713 982710721065396901289035)
          ·
            refine ⟨1474066081598095351933553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982710721065396901289035 1474066081598095351933553)
            ·
              refine ⟨1105549561198571513950165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474066081598095351933553 1105549561198571513950165)
              ·
                refine ⟨25911317840591519858207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1105549561198571513950165 25911317840591519858207)
                ·
                  rfl

theorem cell23_1362477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 7].length) (baseStart_1362477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362477 prefixEnd_1362477 := by exact prefixLift 1362477
  have htrace : WordTrace (prefixWord ++ tailWord_1362477) baseStart_1362477 baseEnd_1362477 := by
    simpa [prefixWord, tailWord_1362477, baseEnd_1362477] using wordTrace_append hprefix tailTrace_1362477
  have hstable : (prefixWord ++ tailWord_1362477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362477).length < 2 ^ (prefixWord ++ tailWord_1362477).sum := by decide
  have hdescent : baseEnd_1362477 < baseStart_1362477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362493 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_1362493 : Nat := 118140960795 + 1362493 * 2 ^ 59
def prefixEnd_1362493 : Nat := 4983230072969 + 3 ^ 40 * 1362493 * 2
def baseEnd_1362493 : Nat := 699613797386442973571515

theorem tailTrace_1362493 : CollatzResearch.WordTrace tailWord_1362493 prefixEnd_1362493 699613797386442973571515 := by
  unfold tailWord_1362493
  simp only [CollatzResearch.WordTrace]
  refine ⟨49694202252928031123692133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33129468168618687415794755 49694202252928031123692133)
  ·
    refine ⟨9317662922424005835692275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49694202252928031123692133 9317662922424005835692275)
    ·
      refine ⟨13976494383636008753538413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9317662922424005835692275 13976494383636008753538413)
      ·
        refine ⟨5241185393863503282576905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13976494383636008753538413 5241185393863503282576905)
        ·
          refine ⟨3930889045397627461932679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5241185393863503282576905 3930889045397627461932679)
          ·
            refine ⟨5896333568096441192899019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930889045397627461932679 5896333568096441192899019)
            ·
              refine ⟨8844500352144661789348529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896333568096441192899019 8844500352144661789348529)
              ·
                refine ⟨6633375264108496342011397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8844500352144661789348529 6633375264108496342011397)
                ·
                  refine ⟨1243757862020343064127137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6633375264108496342011397 1243757862020343064127137)
                  ·
                    refine ⟨932818396515257298095353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1243757862020343064127137 932818396515257298095353)
                    ·
                      refine ⟨699613797386442973571515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932818396515257298095353 699613797386442973571515)
                      ·
                        rfl

theorem cell23_1362493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_1362493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362493 prefixEnd_1362493 := by exact prefixLift 1362493
  have htrace : WordTrace (prefixWord ++ tailWord_1362493) baseStart_1362493 baseEnd_1362493 := by
    simpa [prefixWord, tailWord_1362493, baseEnd_1362493] using wordTrace_append hprefix tailTrace_1362493
  have hstable : (prefixWord ++ tailWord_1362493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362493).length < 2 ^ (prefixWord ++ tailWord_1362493).sum := by decide
  have hdescent : baseEnd_1362493 < baseStart_1362493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362512 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_1362512 : Nat := 118140960795 + 1362512 * 2 ^ 59
def prefixEnd_1362512 : Nat := 4983230072969 + 3 ^ 40 * 1362512 * 2
def baseEnd_1362512 : Nat := 233207851172959466411309

theorem tailTrace_1362512 : CollatzResearch.WordTrace tailWord_1362512 prefixEnd_1362512 233207851172959466411309 := by
  unfold tailWord_1362512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847447619929598684316895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33129930159906131579089193 24847447619929598684316895)
  ·
    refine ⟨37271171429894398026475343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24847447619929598684316895 37271171429894398026475343)
    ·
      refine ⟨55906757144841597039713015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37271171429894398026475343 55906757144841597039713015)
      ·
        refine ⟨83860135717262395559569523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55906757144841597039713015 83860135717262395559569523)
        ·
          refine ⟨125790203575893593339354285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83860135717262395559569523 125790203575893593339354285)
          ·
            refine ⟨47171326340960097502257857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125790203575893593339354285 47171326340960097502257857)
            ·
              refine ⟨35378494755720073126693393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47171326340960097502257857 35378494755720073126693393)
              ·
                refine ⟨26533871066790054845020045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35378494755720073126693393 26533871066790054845020045)
                ·
                  refine ⟨9950201650046270566882517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26533871066790054845020045 9950201650046270566882517)
                  ·
                    refine ⟨233207851172959466411309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9950201650046270566882517 233207851172959466411309)
                    ·
                      rfl

theorem cell23_1362512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_1362512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362512 prefixEnd_1362512 := by exact prefixLift 1362512
  have htrace : WordTrace (prefixWord ++ tailWord_1362512) baseStart_1362512 baseEnd_1362512 := by
    simpa [prefixWord, tailWord_1362512, baseEnd_1362512] using wordTrace_append hprefix tailTrace_1362512
  have hstable : (prefixWord ++ tailWord_1362512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362512).length < 2 ^ (prefixWord ++ tailWord_1362512).sum := by decide
  have hdescent : baseEnd_1362512 < baseStart_1362512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362516 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 7]
def baseStart_1362516 : Nat := 118140960795 + 1362516 * 2 ^ 59
def prefixEnd_1362516 : Nat := 4983230072969 + 3 ^ 40 * 1362516 * 2
def baseEnd_1362516 : Nat := 77736178604610709287101

theorem tailTrace_1362516 : CollatzResearch.WordTrace tailWord_1362516 prefixEnd_1362516 77736178604610709287101 := by
  unfold tailWord_1362516
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847520565922353025889701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33130027421229804034519601 24847520565922353025889701)
  ·
    refine ⟨4658910106110441192354319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24847520565922353025889701 4658910106110441192354319)
    ·
      refine ⟨6988365159165661788531479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4658910106110441192354319 6988365159165661788531479)
      ·
        refine ⟨10482547738748492682797219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6988365159165661788531479 10482547738748492682797219)
        ·
          refine ⟨15723821608122739024195829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10482547738748492682797219 15723821608122739024195829)
          ·
            refine ⟨1474108275761506783518359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15723821608122739024195829 1474108275761506783518359)
            ·
              refine ⟨2211162413642260175277539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474108275761506783518359 2211162413642260175277539)
              ·
                refine ⟨3316743620463390262916309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211162413642260175277539 3316743620463390262916309)
                ·
                  refine ⟨77736178604610709287101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3316743620463390262916309 77736178604610709287101)
                  ·
                    rfl

theorem cell23_1362516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_1362516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362516 prefixEnd_1362516 := by exact prefixLift 1362516
  have htrace : WordTrace (prefixWord ++ tailWord_1362516) baseStart_1362516 baseEnd_1362516 := by
    simpa [prefixWord, tailWord_1362516, baseEnd_1362516] using wordTrace_append hprefix tailTrace_1362516
  have hstable : (prefixWord ++ tailWord_1362516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362516).length < 2 ^ (prefixWord ++ tailWord_1362516).sum := by decide
  have hdescent : baseEnd_1362516 < baseStart_1362516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362559 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 7, 4]
def baseStart_1362559 : Nat := 118140960795 + 1362559 * 2 ^ 59
def prefixEnd_1362559 : Nat := 4983230072969 + 3 ^ 40 * 1362559 * 2
def baseEnd_1362559 : Nat := 233215895703213238448737

theorem tailTrace_1362559 : CollatzResearch.WordTrace tailWord_1362559 prefixEnd_1362559 233215895703213238448737 := by
  unfold tailWord_1362559
  simp only [CollatzResearch.WordTrace]
  refine ⟨49696609470688924395594731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33131072980459282930396487 49696609470688924395594731)
  ·
    refine ⟨74544914206033386593392097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49696609470688924395594731 74544914206033386593392097)
    ·
      refine ⟨55908685654525039945044073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74544914206033386593392097 55908685654525039945044073)
      ·
        refine ⟨41931514240893779958783055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55908685654525039945044073 41931514240893779958783055)
        ·
          refine ⟨62897271361340669938174583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41931514240893779958783055 62897271361340669938174583)
          ·
            refine ⟨94345907042011004907261875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62897271361340669938174583 94345907042011004907261875)
            ·
              refine ⟨141518860563016507360892813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94345907042011004907261875 141518860563016507360892813)
              ·
                refine ⟨53069572711131190260334805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141518860563016507360892813 53069572711131190260334805)
                ·
                  refine ⟨1243818110417137271726597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53069572711131190260334805 1243818110417137271726597)
                  ·
                    refine ⟨233215895703213238448737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243818110417137271726597 233215895703213238448737)
                    ·
                      rfl

theorem cell23_1362559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_1362559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362559 prefixEnd_1362559 := by exact prefixLift 1362559
  have htrace : WordTrace (prefixWord ++ tailWord_1362559) baseStart_1362559 baseEnd_1362559 := by
    simpa [prefixWord, tailWord_1362559, baseEnd_1362559] using wordTrace_append hprefix tailTrace_1362559
  have hstable : (prefixWord ++ tailWord_1362559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362559).length < 2 ^ (prefixWord ++ tailWord_1362559).sum := by decide
  have hdescent : baseEnd_1362559 < baseStart_1362559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362569 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_1362569 : Nat := 118140960795 + 1362569 * 2 ^ 59
def prefixEnd_1362569 : Nat := 4983230072969 + 3 ^ 40 * 1362569 * 2
def baseEnd_1362569 : Nat := 699652821916184676221165

theorem tailTrace_1362569 : CollatzResearch.WordTrace tailWord_1362569 prefixEnd_1362569 699652821916184676221165 := by
  unfold tailWord_1362569
  simp only [CollatzResearch.WordTrace]
  refine ⟨49696974200652696103458761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33131316133768464068972507 49696974200652696103458761)
  ·
    refine ⟨37272730650489522077594071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49696974200652696103458761 37272730650489522077594071)
    ·
      refine ⟨55909095975734283116391107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37272730650489522077594071 55909095975734283116391107)
      ·
        refine ⟨83863643963601424674586661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55909095975734283116391107 83863643963601424674586661)
        ·
          refine ⟨15724433243175267126484999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83863643963601424674586661 15724433243175267126484999)
          ·
            refine ⟨23586649864762900689727499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15724433243175267126484999 23586649864762900689727499)
            ·
              refine ⟨35379974797144351034591249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23586649864762900689727499 35379974797144351034591249)
              ·
                refine ⟨26534981097858263275943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35379974797144351034591249 26534981097858263275943437)
                ·
                  refine ⟨9950617911696848728478789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26534981097858263275943437 9950617911696848728478789)
                  ·
                    refine ⟨1865740858443159136589773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9950617911696848728478789 1865740858443159136589773)
                    ·
                      refine ⟨699652821916184676221165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1865740858443159136589773 699652821916184676221165)
                      ·
                        rfl

theorem cell23_1362569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_1362569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362569 prefixEnd_1362569 := by exact prefixLift 1362569
  have htrace : WordTrace (prefixWord ++ tailWord_1362569) baseStart_1362569 baseEnd_1362569 := by
    simpa [prefixWord, tailWord_1362569, baseEnd_1362569] using wordTrace_append hprefix tailTrace_1362569
  have hstable : (prefixWord ++ tailWord_1362569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362569).length < 2 ^ (prefixWord ++ tailWord_1362569).sum := by decide
  have hdescent : baseEnd_1362569 < baseStart_1362569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362593 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_1362593 : Nat := 118140960795 + 1362593 * 2 ^ 59
def prefixEnd_1362593 : Nat := 4983230072969 + 3 ^ 40 * 1362593 * 2
def baseEnd_1362593 : Nat := 233221715150630860773685

theorem tailTrace_1362593 : CollatzResearch.WordTrace tailWord_1362593 prefixEnd_1362593 233221715150630860773685 := by
  unfold tailWord_1362593
  simp only [CollatzResearch.WordTrace]
  refine ⟨49697849552565748202332433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33131899701710498801554955 49697849552565748202332433)
  ·
    refine ⟨37273387164424311151749325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49697849552565748202332433 37273387164424311151749325)
    ·
      refine ⟨13977520186659116681905997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37273387164424311151749325 13977520186659116681905997)
      ·
        refine ⟨5241570069997168755714749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13977520186659116681905997 5241570069997168755714749)
        ·
          refine ⟨1965588776248938283393031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5241570069997168755714749 1965588776248938283393031)
          ·
            refine ⟨2948383164373407425089547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965588776248938283393031 2948383164373407425089547)
            ·
              refine ⟨4422574746560111137634321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948383164373407425089547 4422574746560111137634321)
              ·
                refine ⟨3316931059920083353225741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422574746560111137634321 3316931059920083353225741)
                ·
                  refine ⟨1243849147470031257459653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3316931059920083353225741 1243849147470031257459653)
                  ·
                    refine ⟨233221715150630860773685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1243849147470031257459653 233221715150630860773685)
                    ·
                      rfl

theorem cell23_1362593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_1362593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362593 prefixEnd_1362593 := by exact prefixLift 1362593
  have htrace : WordTrace (prefixWord ++ tailWord_1362593) baseStart_1362593 baseEnd_1362593 := by
    simpa [prefixWord, tailWord_1362593, baseEnd_1362593] using wordTrace_append hprefix tailTrace_1362593
  have hstable : (prefixWord ++ tailWord_1362593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362593).length < 2 ^ (prefixWord ++ tailWord_1362593).sum := by decide
  have hdescent : baseEnd_1362593 < baseStart_1362593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362656 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2]
def baseStart_1362656 : Nat := 118140960795 + 1362656 * 2 ^ 59
def prefixEnd_1362656 : Nat := 4983230072969 + 3 ^ 40 * 1362656 * 2
def baseEnd_1362656 : Nat := 699697494733125835833265

theorem tailTrace_1362656 : CollatzResearch.WordTrace tailWord_1362656 prefixEnd_1362656 699697494733125835833265 := by
  unfold tailWord_1362656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850073675668754980937911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33133431567558339974583881 24850073675668754980937911)
  ·
    refine ⟨37275110513503132471406867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24850073675668754980937911 37275110513503132471406867)
    ·
      refine ⟨55912665770254698707110301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37275110513503132471406867 55912665770254698707110301)
      ·
        refine ⟨20967249663845512015166363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55912665770254698707110301 20967249663845512015166363)
        ·
          refine ⟨31450874495768268022749545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20967249663845512015166363 31450874495768268022749545)
          ·
            refine ⟨23588155871826201017062159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31450874495768268022749545 23588155871826201017062159)
            ·
              refine ⟨35382233807739301525593239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23588155871826201017062159 35382233807739301525593239)
              ·
                refine ⟨53073350711608952288389859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35382233807739301525593239 53073350711608952288389859)
                ·
                  refine ⟨79610026067413428432584789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53073350711608952288389859 79610026067413428432584789)
                  ·
                    refine ⟨932929992977501114444353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79610026067413428432584789 932929992977501114444353)
                    ·
                      refine ⟨699697494733125835833265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932929992977501114444353 699697494733125835833265)
                      ·
                        rfl

theorem cell23_1362656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_1362656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362656 prefixEnd_1362656 := by exact prefixLift 1362656
  have htrace : WordTrace (prefixWord ++ tailWord_1362656) baseStart_1362656 baseEnd_1362656 := by
    simpa [prefixWord, tailWord_1362656, baseEnd_1362656] using wordTrace_append hprefix tailTrace_1362656
  have hstable : (prefixWord ++ tailWord_1362656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362656).length < 2 ^ (prefixWord ++ tailWord_1362656).sum := by decide
  have hdescent : baseEnd_1362656 < baseStart_1362656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362696 : List Nat := [2, 1, 3, 2, 2, 3, 2, 8]
def baseStart_1362696 : Nat := 118140960795 + 1362696 * 2 ^ 59
def prefixEnd_1362696 : Nat := 4983230072969 + 3 ^ 40 * 1362696 * 2
def baseEnd_1362696 : Nat := 25915482739233543679003

theorem tailTrace_1362696 : CollatzResearch.WordTrace tailWord_1362696 prefixEnd_1362696 25915482739233543679003 := by
  unfold tailWord_1362696
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850803135596298396665971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33134404180795064528887961 24850803135596298396665971)
  ·
    refine ⟨37276204703394447594998957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24850803135596298396665971 37276204703394447594998957)
    ·
      refine ⟨13978576763772917848124609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37276204703394447594998957 13978576763772917848124609)
      ·
        refine ⟨10483932572829688386093457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13978576763772917848124609 10483932572829688386093457)
        ·
          refine ⟨7862949429622266289570093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10483932572829688386093457 7862949429622266289570093)
          ·
            refine ⟨2948606036108349858588785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7862949429622266289570093 2948606036108349858588785)
            ·
              refine ⟨2211454527081262393941589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2948606036108349858588785 2211454527081262393941589)
              ·
                refine ⟨25915482739233543679003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2211454527081262393941589 25915482739233543679003)
                ·
                  rfl

theorem cell23_1362696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 8].length) (baseStart_1362696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362696 prefixEnd_1362696 := by exact prefixLift 1362696
  have htrace : WordTrace (prefixWord ++ tailWord_1362696) baseStart_1362696 baseEnd_1362696 := by
    simpa [prefixWord, tailWord_1362696, baseEnd_1362696] using wordTrace_append hprefix tailTrace_1362696
  have hstable : (prefixWord ++ tailWord_1362696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362696).length < 2 ^ (prefixWord ++ tailWord_1362696).sum := by decide
  have hdescent : baseEnd_1362696 < baseStart_1362696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362699 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_1362699 : Nat := 118140960795 + 1362699 * 2 ^ 59
def prefixEnd_1362699 : Nat := 4983230072969 + 3 ^ 40 * 1362699 * 2
def baseEnd_1362699 : Nat := 699719574401269167595567

theorem tailTrace_1362699 : CollatzResearch.WordTrace tailWord_1362699 prefixEnd_1362699 699719574401269167595567 := by
  unfold tailWord_1362699
  simp only [CollatzResearch.WordTrace]
  refine ⟨49701715690181728305691151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33134477126787818870460767 49701715690181728305691151)
  ·
    refine ⟨74552573535272592458536727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49701715690181728305691151 74552573535272592458536727)
    ·
      refine ⟨111828860302908888687805091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74552573535272592458536727 111828860302908888687805091)
      ·
        refine ⟨167743290454363333031707637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111828860302908888687805091 167743290454363333031707637)
        ·
          refine ⟨15725933480096562471722591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167743290454363333031707637 15725933480096562471722591)
          ·
            refine ⟨23588900220144843707583887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15725933480096562471722591 23588900220144843707583887)
            ·
              refine ⟨35383350330217265561375831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23588900220144843707583887 35383350330217265561375831)
              ·
                refine ⟨53075025495325898342063747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35383350330217265561375831 53075025495325898342063747)
                ·
                  refine ⟨79612538242988847513095621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53075025495325898342063747 79612538242988847513095621)
                  ·
                    refine ⟨14927350920560408908705429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79612538242988847513095621 14927350920560408908705429)
                    ·
                      refine ⟨699719574401269167595567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14927350920560408908705429 699719574401269167595567)
                      ·
                        rfl

theorem cell23_1362699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_1362699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362699 prefixEnd_1362699 := by exact prefixLift 1362699
  have htrace : WordTrace (prefixWord ++ tailWord_1362699) baseStart_1362699 baseEnd_1362699 := by
    simpa [prefixWord, tailWord_1362699, baseEnd_1362699] using wordTrace_append hprefix tailTrace_1362699
  have hstable : (prefixWord ++ tailWord_1362699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362699).length < 2 ^ (prefixWord ++ tailWord_1362699).sum := by decide
  have hdescent : baseEnd_1362699 < baseStart_1362699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362729 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_1362729 : Nat := 118140960795 + 1362729 * 2 ^ 59
def prefixEnd_1362729 : Nat := 4983230072969 + 3 ^ 40 * 1362729 * 2
def baseEnd_1362729 : Nat := 699734978820904050220429

theorem tailTrace_1362729 : CollatzResearch.WordTrace tailWord_1362729 prefixEnd_1362729 699734978820904050220429 := by
  unfold tailWord_1362729
  simp only [CollatzResearch.WordTrace]
  refine ⟨49702809880073043429283241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33135206586715362286188827 49702809880073043429283241)
  ·
    refine ⟨37277107410054782571962431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49702809880073043429283241 37277107410054782571962431)
    ·
      refine ⟨55915661115082173857943647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37277107410054782571962431 55915661115082173857943647)
      ·
        refine ⟨83873491672623260786915471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55915661115082173857943647 83873491672623260786915471)
        ·
          refine ⟨125810237508934891180373207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83873491672623260786915471 125810237508934891180373207)
          ·
            refine ⟨188715356263402336770559811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125810237508934891180373207 188715356263402336770559811)
            ·
              refine ⟨283073034395103505155839717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188715356263402336770559811 283073034395103505155839717)
              ·
                refine ⟨53076193949081907216719947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283073034395103505155839717 53076193949081907216719947)
                ·
                  refine ⟨79614290923622860825079921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53076193949081907216719947 79614290923622860825079921)
                  ·
                    refine ⟨59710718192717145618809941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79614290923622860825079921 59710718192717145618809941)
                    ·
                      refine ⟨699734978820904050220429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 59710718192717145618809941 699734978820904050220429)
                      ·
                        rfl

theorem cell23_1362729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_1362729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362729 prefixEnd_1362729 := by exact prefixLift 1362729
  have htrace : WordTrace (prefixWord ++ tailWord_1362729) baseStart_1362729 baseEnd_1362729 := by
    simpa [prefixWord, tailWord_1362729, baseEnd_1362729] using wordTrace_append hprefix tailTrace_1362729
  have hstable : (prefixWord ++ tailWord_1362729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362729).length < 2 ^ (prefixWord ++ tailWord_1362729).sum := by decide
  have hdescent : baseEnd_1362729 < baseStart_1362729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362741 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_1362741 : Nat := 118140960795 + 1362741 * 2 ^ 59
def prefixEnd_1362741 : Nat := 4983230072969 + 3 ^ 40 * 1362741 * 2
def baseEnd_1362741 : Nat := 699741140588758003270375

theorem tailTrace_1362741 : CollatzResearch.WordTrace tailWord_1362741 prefixEnd_1362741 699741140588758003270375 := by
  unfold tailWord_1362741
  simp only [CollatzResearch.WordTrace]
  refine ⟨49703247556029569478720077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33135498370686379652480051 49703247556029569478720077)
  ·
    refine ⟨18638717833511088554520029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49703247556029569478720077 18638717833511088554520029)
    ·
      refine ⟨6989519187566658207945011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18638717833511088554520029 6989519187566658207945011)
      ·
        refine ⟨10484278781349987311917517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6989519187566658207945011 10484278781349987311917517)
        ·
          refine ⟨3931604543006245241969069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10484278781349987311917517 3931604543006245241969069)
          ·
            refine ⟨1474351703627341965738401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3931604543006245241969069 1474351703627341965738401)
            ·
              refine ⟨1105763777720506474303801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474351703627341965738401 1105763777720506474303801)
              ·
                refine ⟨829322833290379855727851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105763777720506474303801 829322833290379855727851)
                ·
                  refine ⟨1243984249935569783591777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829322833290379855727851 1243984249935569783591777)
                  ·
                    refine ⟨932988187451677337693833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1243984249935569783591777 932988187451677337693833)
                    ·
                      refine ⟨699741140588758003270375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 932988187451677337693833 699741140588758003270375)
                      ·
                        rfl

theorem cell23_1362741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_1362741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362741 prefixEnd_1362741 := by exact prefixLift 1362741
  have htrace : WordTrace (prefixWord ++ tailWord_1362741) baseStart_1362741 baseEnd_1362741 := by
    simpa [prefixWord, tailWord_1362741, baseEnd_1362741] using wordTrace_append hprefix tailTrace_1362741
  have hstable : (prefixWord ++ tailWord_1362741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362741).length < 2 ^ (prefixWord ++ tailWord_1362741).sum := by decide
  have hdescent : baseEnd_1362741 < baseStart_1362741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362766 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1362766 : Nat := 118140960795 + 1362766 * 2 ^ 59
def prefixEnd_1362766 : Nat := 4983230072969 + 3 ^ 40 * 1362766 * 2
def baseEnd_1362766 : Nat := 699753977605120405457759

theorem tailTrace_1362766 : CollatzResearch.WordTrace tailWord_1362766 prefixEnd_1362766 699753977605120405457759 := by
  unfold tailWord_1362766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213019922617374843547519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33136106253959332498920101 6213019922617374843547519)
  ·
    refine ⟨9319529883926062265321279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213019922617374843547519 9319529883926062265321279)
    ·
      refine ⟨13979294825889093397981919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9319529883926062265321279 13979294825889093397981919)
      ·
        refine ⟨20968942238833640096972879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13979294825889093397981919 20968942238833640096972879)
        ·
          refine ⟨31453413358250460145459319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20968942238833640096972879 31453413358250460145459319)
          ·
            refine ⟨47180120037375690218188979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31453413358250460145459319 47180120037375690218188979)
            ·
              refine ⟨70770180056063535327283469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47180120037375690218188979 70770180056063535327283469)
              ·
                refine ⟨26538817521023825747731301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70770180056063535327283469 26538817521023825747731301)
                ·
                  refine ⟨4976028285191967327699619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26538817521023825747731301 4976028285191967327699619)
                  ·
                    refine ⟨7464042427787950991549429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976028285191967327699619 7464042427787950991549429)
                    ·
                      refine ⟨699753977605120405457759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7464042427787950991549429 699753977605120405457759)
                      ·
                        rfl

theorem cell23_1362766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1362766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362766 prefixEnd_1362766 := by exact prefixLift 1362766
  have htrace : WordTrace (prefixWord ++ tailWord_1362766) baseStart_1362766 baseEnd_1362766 := by
    simpa [prefixWord, tailWord_1362766, baseEnd_1362766] using wordTrace_append hprefix tailTrace_1362766
  have hstable : (prefixWord ++ tailWord_1362766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362766).length < 2 ^ (prefixWord ++ tailWord_1362766).sum := by decide
  have hdescent : baseEnd_1362766 < baseStart_1362766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362803 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 5]
def baseStart_1362803 : Nat := 118140960795 + 1362803 * 2 ^ 59
def prefixEnd_1362803 : Nat := 4983230072969 + 3 ^ 40 * 1362803 * 2
def baseEnd_1362803 : Nat := 77752552932148528966121

theorem tailTrace_1362803 : CollatzResearch.WordTrace tailWord_1362803 prefixEnd_1362803 77752552932148528966121 := by
  unfold tailWord_1362803
  simp only [CollatzResearch.WordTrace]
  refine ⟨49705508881804954067477063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33137005921203302711651375 49705508881804954067477063)
  ·
    refine ⟨74558263322707431101215595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49705508881804954067477063 74558263322707431101215595)
    ·
      refine ⟨111837394984061146651823393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74558263322707431101215595 111837394984061146651823393)
      ·
        refine ⟨83878046238045859988867545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111837394984061146651823393 83878046238045859988867545)
        ·
          refine ⟨62908534678534394991650659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83878046238045859988867545 62908534678534394991650659)
          ·
            refine ⟨94362802017801592487475989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62908534678534394991650659 94362802017801592487475989)
            ·
              refine ⟨4423256344584449647850437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94362802017801592487475989 4423256344584449647850437)
              ·
                refine ⟨829360564609584308971957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4423256344584449647850437 829360564609584308971957)
                ·
                  refine ⟨77752552932148528966121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 829360564609584308971957 77752552932148528966121)
                  ·
                    rfl

theorem cell23_1362803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 5].length) (baseStart_1362803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362803 prefixEnd_1362803 := by exact prefixLift 1362803
  have htrace : WordTrace (prefixWord ++ tailWord_1362803) baseStart_1362803 baseEnd_1362803 := by
    simpa [prefixWord, tailWord_1362803, baseEnd_1362803] using wordTrace_append hprefix tailTrace_1362803
  have hstable : (prefixWord ++ tailWord_1362803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362803).length < 2 ^ (prefixWord ++ tailWord_1362803).sum := by decide
  have hdescent : baseEnd_1362803 < baseStart_1362803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362813 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1362813 : Nat := 118140960795 + 1362813 * 2 ^ 59
def prefixEnd_1362813 : Nat := 4983230072969 + 3 ^ 40 * 1362813 * 2
def baseEnd_1362813 : Nat := 699778111195881721570043

theorem tailTrace_1362813 : CollatzResearch.WordTrace tailWord_1362813 prefixEnd_1362813 699778111195881721570043 := by
  unfold tailWord_1362813
  simp only [CollatzResearch.WordTrace]
  refine ⟨49705873611768725775341093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33137249074512483850227395 49705873611768725775341093)
  ·
    refine ⟨9319851302206636082876455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49705873611768725775341093 9319851302206636082876455)
    ·
      refine ⟨13979776953309954124314683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9319851302206636082876455 13979776953309954124314683)
      ·
        refine ⟨20969665429964931186472025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13979776953309954124314683 20969665429964931186472025)
        ·
          refine ⟨15727249072473698389854019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20969665429964931186472025 15727249072473698389854019)
          ·
            refine ⟨23590873608710547584781029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727249072473698389854019 23590873608710547584781029)
            ·
              refine ⟨4423288801633227672146443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23590873608710547584781029 4423288801633227672146443)
              ·
                refine ⟨6634933202449841508219665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423288801633227672146443 6634933202449841508219665)
                ·
                  refine ⟨4976199901837381131164749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6634933202449841508219665 4976199901837381131164749)
                  ·
                    refine ⟨1866074963189017924186781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4976199901837381131164749 1866074963189017924186781)
                    ·
                      refine ⟨699778111195881721570043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1866074963189017924186781 699778111195881721570043)
                      ·
                        rfl

theorem cell23_1362813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1362813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362813 prefixEnd_1362813 := by exact prefixLift 1362813
  have htrace : WordTrace (prefixWord ++ tailWord_1362813) baseStart_1362813 baseEnd_1362813 := by
    simpa [prefixWord, tailWord_1362813, baseEnd_1362813] using wordTrace_append hprefix tailTrace_1362813
  have hstable : (prefixWord ++ tailWord_1362813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362813).length < 2 ^ (prefixWord ++ tailWord_1362813).sum := by decide
  have hdescent : baseEnd_1362813 < baseStart_1362813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362816 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_1362816 : Nat := 118140960795 + 1362816 * 2 ^ 59
def prefixEnd_1362816 : Nat := 4983230072969 + 3 ^ 40 * 1362816 * 2
def baseEnd_1362816 : Nat := 233259883879281736610843

theorem tailTrace_1362816 : CollatzResearch.WordTrace tailWord_1362816 prefixEnd_1362816 233259883879281736610843 := by
  unfold tailWord_1362816
  simp only [CollatzResearch.WordTrace]
  refine ⟨24852991515378928643850151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33137322020505238191800201 24852991515378928643850151)
  ·
    refine ⟨37279487273068392965775227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24852991515378928643850151 37279487273068392965775227)
    ·
      refine ⟨55919230909602589448662841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37279487273068392965775227 55919230909602589448662841)
      ·
        refine ⟨41939423182201942086497131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55919230909602589448662841 41939423182201942086497131)
        ·
          refine ⟨62909134773302913129745697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41939423182201942086497131 62909134773302913129745697)
          ·
            refine ⟨47181851079977184847309273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62909134773302913129745697 47181851079977184847309273)
            ·
              refine ⟨35386388309982888635481955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47181851079977184847309273 35386388309982888635481955)
              ·
                refine ⟨53079582464974332953222933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35386388309982888635481955 53079582464974332953222933)
                ·
                  refine ⟨2488105428045671857182325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53079582464974332953222933 2488105428045671857182325)
                  ·
                    refine ⟨233259883879281736610843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2488105428045671857182325 233259883879281736610843)
                    ·
                      rfl

theorem cell23_1362816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_1362816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362816 prefixEnd_1362816 := by exact prefixLift 1362816
  have htrace : WordTrace (prefixWord ++ tailWord_1362816) baseStart_1362816 baseEnd_1362816 := by
    simpa [prefixWord, tailWord_1362816, baseEnd_1362816] using wordTrace_append hprefix tailTrace_1362816
  have hstable : (prefixWord ++ tailWord_1362816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362816).length < 2 ^ (prefixWord ++ tailWord_1362816).sum := by decide
  have hdescent : baseEnd_1362816 < baseStart_1362816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362850 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1362850 : Nat := 118140960795 + 1362850 * 2 ^ 59
def prefixEnd_1362850 : Nat := 4983230072969 + 3 ^ 40 * 1362850 * 2
def baseEnd_1362850 : Nat := 233265703326699358935791

theorem tailTrace_1362850 : CollatzResearch.WordTrace tailWord_1362850 prefixEnd_1362850 233265703326699358935791 := by
  unfold tailWord_1362850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12426805778158670273609501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33138148741756454062958669 12426805778158670273609501)
  ·
    refine ⟨4660052166809501352603563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12426805778158670273609501 4660052166809501352603563)
    ·
      refine ⟨6990078250214252028905345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660052166809501352603563 6990078250214252028905345)
      ·
        refine ⟨5242558687660689021679009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6990078250214252028905345 5242558687660689021679009)
        ·
          refine ⟨3931919015745516766259257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5242558687660689021679009 3931919015745516766259257)
          ·
            refine ⟨2948939261809137574694443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3931919015745516766259257 2948939261809137574694443)
            ·
              refine ⟨4423408892713706362041665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948939261809137574694443 4423408892713706362041665)
              ·
                refine ⟨3317556669535279771531249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4423408892713706362041665 3317556669535279771531249)
                ·
                  refine ⟨2488167502151459828648437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3317556669535279771531249 2488167502151459828648437)
                  ·
                    refine ⟨233265703326699358935791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2488167502151459828648437 233265703326699358935791)
                    ·
                      rfl

theorem cell23_1362850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1362850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362850 prefixEnd_1362850 := by exact prefixLift 1362850
  have htrace : WordTrace (prefixWord ++ tailWord_1362850) baseStart_1362850 baseEnd_1362850 := by
    simpa [prefixWord, tailWord_1362850, baseEnd_1362850] using wordTrace_append hprefix tailTrace_1362850
  have hstable : (prefixWord ++ tailWord_1362850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362850).length < 2 ^ (prefixWord ++ tailWord_1362850).sum := by decide
  have hdescent : baseEnd_1362850 < baseStart_1362850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362863 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 3, 4]
def baseStart_1362863 : Nat := 118140960795 + 1362863 * 2 ^ 59
def prefixEnd_1362863 : Nat := 4983230072969 + 3 ^ 40 * 1362863 * 2
def baseEnd_1362863 : Nat := 233267928409535508648271

theorem tailTrace_1362863 : CollatzResearch.WordTrace tailWord_1362863 prefixEnd_1362863 233267928409535508648271 := by
  unfold tailWord_1362863
  simp only [CollatzResearch.WordTrace]
  refine ⟨49707697261587584314661243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33138464841058389543107495 49707697261587584314661243)
  ·
    refine ⟨74561545892381376471991865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49707697261587584314661243 74561545892381376471991865)
    ·
      refine ⟨55921159419286032353993899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74561545892381376471991865 55921159419286032353993899)
      ·
        refine ⟨83881739128929048530990849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55921159419286032353993899 83881739128929048530990849)
        ·
          refine ⟨62911304346696786398243137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83881739128929048530990849 62911304346696786398243137)
          ·
            refine ⟨47183478260022589798682353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62911304346696786398243137 47183478260022589798682353)
            ·
              refine ⟨35387608695016942349011765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47183478260022589798682353 35387608695016942349011765)
              ·
                refine ⟨3317588315157838345219853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35387608695016942349011765 3317588315157838345219853)
                ·
                  refine ⟨1244095618184189379457445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3317588315157838345219853 1244095618184189379457445)
                  ·
                    refine ⟨233267928409535508648271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244095618184189379457445 233267928409535508648271)
                    ·
                      rfl

theorem cell23_1362863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_1362863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362863 prefixEnd_1362863 := by exact prefixLift 1362863
  have htrace : WordTrace (prefixWord ++ tailWord_1362863) baseStart_1362863 baseEnd_1362863 := by
    simpa [prefixWord, tailWord_1362863, baseEnd_1362863] using wordTrace_append hprefix tailTrace_1362863
  have hstable : (prefixWord ++ tailWord_1362863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362863).length < 2 ^ (prefixWord ++ tailWord_1362863).sum := by decide
  have hdescent : baseEnd_1362863 < baseStart_1362863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362896 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1362896 : Nat := 118140960795 + 1362896 * 2 ^ 59
def prefixEnd_1362896 : Nat := 4983230072969 + 3 ^ 40 * 1362896 * 2
def baseEnd_1362896 : Nat := 699820730090204896832161

theorem tailTrace_1362896 : CollatzResearch.WordTrace tailWord_1362896 prefixEnd_1362896 699820730090204896832161 := by
  unfold tailWord_1362896
  simp only [CollatzResearch.WordTrace]
  refine ⟨24854450435234015475306271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33139267246978687300408361 24854450435234015475306271)
  ·
    refine ⟨37281675652851023212959407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24854450435234015475306271 37281675652851023212959407)
    ·
      refine ⟨55922513479276534819439111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37281675652851023212959407 55922513479276534819439111)
      ·
        refine ⟨83883770218914802229158667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55922513479276534819439111 83883770218914802229158667)
        ·
          refine ⟨125825655328372203343738001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83883770218914802229158667 125825655328372203343738001)
          ·
            refine ⟨94369241496279152507803501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125825655328372203343738001 94369241496279152507803501)
            ·
              refine ⟨35388465561104682190426313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94369241496279152507803501 35388465561104682190426313)
              ·
                refine ⟨26541349170828511642819735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35388465561104682190426313 26541349170828511642819735)
                ·
                  refine ⟨39812023756242767464229603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26541349170828511642819735 39812023756242767464229603)
                  ·
                    refine ⟨59718035634364151196344405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39812023756242767464229603 59718035634364151196344405)
                    ·
                      refine ⟨699820730090204896832161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 59718035634364151196344405 699820730090204896832161)
                      ·
                        rfl

theorem cell23_1362896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1362896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362896 prefixEnd_1362896 := by exact prefixLift 1362896
  have htrace : WordTrace (prefixWord ++ tailWord_1362896) baseStart_1362896 baseEnd_1362896 := by
    simpa [prefixWord, tailWord_1362896, baseEnd_1362896] using wordTrace_append hprefix tailTrace_1362896
  have hstable : (prefixWord ++ tailWord_1362896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362896).length < 2 ^ (prefixWord ++ tailWord_1362896).sum := by decide
  have hdescent : baseEnd_1362896 < baseStart_1362896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362954 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_1362954 : Nat := 118140960795 + 1362954 * 2 ^ 59
def prefixEnd_1362954 : Nat := 4983230072969 + 3 ^ 40 * 1362954 * 2
def baseEnd_1362954 : Nat := 699850511968165669906895

theorem tailTrace_1362954 : CollatzResearch.WordTrace tailWord_1362954 prefixEnd_1362954 699850511968165669906895 := by
  unfold tailWord_1362954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427754076064476714055979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33140677536171937904149277 12427754076064476714055979)
  ·
    refine ⟨18641631114096715071083969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12427754076064476714055979 18641631114096715071083969)
    ·
      refine ⟨13981223335572536303312977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18641631114096715071083969 13981223335572536303312977)
      ·
        refine ⟨10485917501679402227484733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13981223335572536303312977 10485917501679402227484733)
        ·
          refine ⟨3932219063129775835306775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10485917501679402227484733 3932219063129775835306775)
          ·
            refine ⟨5898328594694663752960163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932219063129775835306775 5898328594694663752960163)
            ·
              refine ⟨8847492892041995629440245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898328594694663752960163 8847492892041995629440245)
              ·
                refine ⟨829452458628937090260023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8847492892041995629440245 829452458628937090260023)
                ·
                  refine ⟨1244178687943405635390035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829452458628937090260023 1244178687943405635390035)
                  ·
                    refine ⟨1866268031915108453085053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1244178687943405635390035 1866268031915108453085053)
                    ·
                      refine ⟨699850511968165669906895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1866268031915108453085053 699850511968165669906895)
                      ·
                        rfl

theorem cell23_1362954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_1362954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362954 prefixEnd_1362954 := by exact prefixLift 1362954
  have htrace : WordTrace (prefixWord ++ tailWord_1362954) baseStart_1362954 baseEnd_1362954 := by
    simpa [prefixWord, tailWord_1362954, baseEnd_1362954] using wordTrace_append hprefix tailTrace_1362954
  have hstable : (prefixWord ++ tailWord_1362954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362954).length < 2 ^ (prefixWord ++ tailWord_1362954).sum := by decide
  have hdescent : baseEnd_1362954 < baseStart_1362954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362963 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5]
def baseStart_1362963 : Nat := 118140960795 + 1362963 * 2 ^ 59
def prefixEnd_1362963 : Nat := 4983230072969 + 3 ^ 40 * 1362963 * 2
def baseEnd_1362963 : Nat := 699855133294056134694353

theorem tailTrace_1362963 : CollatzResearch.WordTrace tailWord_1362963 prefixEnd_1362963 699855133294056134694353 := by
  unfold tailWord_1362963
  simp only [CollatzResearch.WordTrace]
  refine ⟨49711344561225301393301543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33140896374150200928867695 49711344561225301393301543)
  ·
    refine ⟨74567016841837952089952315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49711344561225301393301543 74567016841837952089952315)
    ·
      refine ⟨111850525262756928134928473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74567016841837952089952315 111850525262756928134928473)
      ·
        refine ⟨83887893947067696101196355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111850525262756928134928473 83887893947067696101196355)
        ·
          refine ⟨125831840920601544151794533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83887893947067696101196355 125831840920601544151794533)
          ·
            refine ⟨23593470172612789528461475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125831840920601544151794533 23593470172612789528461475)
            ·
              refine ⟨35390205258919184292692213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23593470172612789528461475 35390205258919184292692213)
              ·
                refine ⟨3317831743023673527439895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35390205258919184292692213 3317831743023673527439895)
                ·
                  refine ⟨4976747614535510291159843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317831743023673527439895 4976747614535510291159843)
                  ·
                    refine ⟨7465121421803265436739765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976747614535510291159843 7465121421803265436739765)
                    ·
                      refine ⟨699855133294056134694353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7465121421803265436739765 699855133294056134694353)
                      ·
                        rfl

theorem cell23_1362963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_1362963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362963 prefixEnd_1362963 := by exact prefixLift 1362963
  have htrace : WordTrace (prefixWord ++ tailWord_1362963) baseStart_1362963 baseEnd_1362963 := by
    simpa [prefixWord, tailWord_1362963, baseEnd_1362963] using wordTrace_append hprefix tailTrace_1362963
  have hstable : (prefixWord ++ tailWord_1362963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362963).length < 2 ^ (prefixWord ++ tailWord_1362963).sum := by decide
  have hdescent : baseEnd_1362963 < baseStart_1362963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362970 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_1362970 : Nat := 118140960795 + 1362970 * 2 ^ 59
def prefixEnd_1362970 : Nat := 4983230072969 + 3 ^ 40 * 1362970 * 2
def baseEnd_1362970 : Nat := 233286242552879202435607

theorem tailTrace_1362970 : CollatzResearch.WordTrace tailWord_1362970 prefixEnd_1362970 233286242552879202435607 := by
  unfold tailWord_1362970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427899968049985397201591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33141066581466627725870909 12427899968049985397201591)
  ·
    refine ⟨18641849952074978095802387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12427899968049985397201591 18641849952074978095802387)
    ·
      refine ⟨27962774928112467143703581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18641849952074978095802387 27962774928112467143703581)
      ·
        refine ⟨10486040598042175178888843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27962774928112467143703581 10486040598042175178888843)
        ·
          refine ⟨15729060897063262768333265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486040598042175178888843 15729060897063262768333265)
          ·
            refine ⟨11796795672797447076249949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15729060897063262768333265 11796795672797447076249949)
            ·
              refine ⟨4423798377299042653593731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11796795672797447076249949 4423798377299042653593731)
              ·
                refine ⟨6635697565948563980390597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423798377299042653593731 6635697565948563980390597)
                ·
                  refine ⟨1244193293615355746323237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6635697565948563980390597 1244193293615355746323237)
                  ·
                    refine ⟨233286242552879202435607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244193293615355746323237 233286242552879202435607)
                    ·
                      rfl

theorem cell23_1362970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_1362970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362970 prefixEnd_1362970 := by exact prefixLift 1362970
  have htrace : WordTrace (prefixWord ++ tailWord_1362970) baseStart_1362970 baseEnd_1362970 := by
    simpa [prefixWord, tailWord_1362970, baseEnd_1362970] using wordTrace_append hprefix tailTrace_1362970
  have hstable : (prefixWord ++ tailWord_1362970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362970).length < 2 ^ (prefixWord ++ tailWord_1362970).sum := by decide
  have hdescent : baseEnd_1362970 < baseStart_1362970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362980 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1362980 : Nat := 118140960795 + 1362980 * 2 ^ 59
def prefixEnd_1362980 : Nat := 4983230072969 + 3 ^ 40 * 1362980 * 2
def baseEnd_1362980 : Nat := 699863862465182568181775

theorem tailTrace_1362980 : CollatzResearch.WordTrace tailWord_1362980 prefixEnd_1362980 699863862465182568181775 := by
  unfold tailWord_1362980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24855982301081856648335197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33141309734775808864446929 24855982301081856648335197)
  ·
    refine ⟨9320993362905696243125699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24855982301081856648335197 9320993362905696243125699)
    ·
      refine ⟨13981490044358544364688549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9320993362905696243125699 13981490044358544364688549)
      ·
        refine ⟨2621529383317227068379103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13981490044358544364688549 2621529383317227068379103)
        ·
          refine ⟨3932294074975840602568655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621529383317227068379103 3932294074975840602568655)
          ·
            refine ⟨5898441112463760903852983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932294074975840602568655 5898441112463760903852983)
            ·
              refine ⟨8847661668695641355779475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898441112463760903852983 8847661668695641355779475)
              ·
                refine ⟨13271492503043462033669213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8847661668695641355779475 13271492503043462033669213)
                ·
                  refine ⟨4976809688641298262625955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13271492503043462033669213 4976809688641298262625955)
                  ·
                    refine ⟨7465214532961947393938933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976809688641298262625955 7465214532961947393938933)
                    ·
                      refine ⟨699863862465182568181775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7465214532961947393938933 699863862465182568181775)
                      ·
                        rfl

theorem cell23_1362980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1362980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362980 prefixEnd_1362980 := by exact prefixLift 1362980
  have htrace : WordTrace (prefixWord ++ tailWord_1362980) baseStart_1362980 baseEnd_1362980 := by
    simpa [prefixWord, tailWord_1362980, baseEnd_1362980] using wordTrace_append hprefix tailTrace_1362980
  have hstable : (prefixWord ++ tailWord_1362980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362980).length < 2 ^ (prefixWord ++ tailWord_1362980).sum := by decide
  have hdescent : baseEnd_1362980 < baseStart_1362980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362987 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 2, 4]
def baseStart_1362987 : Nat := 118140960795 + 1362987 * 2 ^ 59
def prefixEnd_1362987 : Nat := 4983230072969 + 3 ^ 40 * 1362987 * 2
def baseEnd_1362987 : Nat := 233289152276588013598081

theorem tailTrace_1362987 : CollatzResearch.WordTrace tailWord_1362987 prefixEnd_1362987 233289152276588013598081 := by
  unfold tailWord_1362987
  simp only [CollatzResearch.WordTrace]
  refine ⟨49712219913138353492175215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33141479942092235661450143 49712219913138353492175215)
  ·
    refine ⟨74568329869707530238262823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49712219913138353492175215 74568329869707530238262823)
    ·
      refine ⟨111852494804561295357394235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74568329869707530238262823 111852494804561295357394235)
      ·
        refine ⟨167778742206841943036091353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111852494804561295357394235 167778742206841943036091353)
        ·
          refine ⟨125834056655131457277068515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167778742206841943036091353 125834056655131457277068515)
          ·
            refine ⟨188751084982697185915602773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125834056655131457277068515 188751084982697185915602773)
            ·
              refine ⟨1105963388570491323724235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 188751084982697185915602773 1105963388570491323724235)
              ·
                refine ⟨1658945082855736985586353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105963388570491323724235 1658945082855736985586353)
                ·
                  refine ⟨1244208812141802739189765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1658945082855736985586353 1244208812141802739189765)
                  ·
                    refine ⟨233289152276588013598081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244208812141802739189765 233289152276588013598081)
                    ·
                      rfl

theorem cell23_1362987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 4].length) (baseStart_1362987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362987 prefixEnd_1362987 := by exact prefixLift 1362987
  have htrace : WordTrace (prefixWord ++ tailWord_1362987) baseStart_1362987 baseEnd_1362987 := by
    simpa [prefixWord, tailWord_1362987, baseEnd_1362987] using wordTrace_append hprefix tailTrace_1362987
  have hstable : (prefixWord ++ tailWord_1362987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362987).length < 2 ^ (prefixWord ++ tailWord_1362987).sum := by decide
  have hdescent : baseEnd_1362987 < baseStart_1362987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362990 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1362990 : Nat := 118140960795 + 1362990 * 2 ^ 59
def prefixEnd_1362990 : Nat := 4983230072969 + 3 ^ 40 * 1362990 * 2
def baseEnd_1362990 : Nat := 699868997271727529056729

theorem tailTrace_1362990 : CollatzResearch.WordTrace tailWord_1362990 prefixEnd_1362990 699868997271727529056729 := by
  unfold tailWord_1362990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214041166515935625566803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33141552888084990003022949 6214041166515935625566803)
  ·
    refine ⟨9321061749773903438350205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6214041166515935625566803 9321061749773903438350205)
    ·
      refine ⟨3495398156165213789381327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9321061749773903438350205 3495398156165213789381327)
      ·
        refine ⟨5243097234247820684071991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495398156165213789381327 5243097234247820684071991)
        ·
          refine ⟨7864645851371731026107987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243097234247820684071991 7864645851371731026107987)
          ·
            refine ⟨11796968777057596539161981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864645851371731026107987 11796968777057596539161981)
            ·
              refine ⟨4423863291396598702185743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11796968777057596539161981 4423863291396598702185743)
              ·
                refine ⟨6635794937094898053278615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423863291396598702185743 6635794937094898053278615)
                ·
                  refine ⟨9953692405642347079917923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635794937094898053278615 9953692405642347079917923)
                  ·
                    refine ⟨14930538608463520619876885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9953692405642347079917923 14930538608463520619876885)
                    ·
                      refine ⟨699868997271727529056729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14930538608463520619876885 699868997271727529056729)
                      ·
                        rfl

theorem cell23_1362990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1362990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1362990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1362990 prefixEnd_1362990 := by exact prefixLift 1362990
  have htrace : WordTrace (prefixWord ++ tailWord_1362990) baseStart_1362990 baseEnd_1362990 := by
    simpa [prefixWord, tailWord_1362990, baseEnd_1362990] using wordTrace_append hprefix tailTrace_1362990
  have hstable : (prefixWord ++ tailWord_1362990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362990).length < 2 ^ (prefixWord ++ tailWord_1362990).sum := by decide
  have hdescent : baseEnd_1362990 < baseStart_1362990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363000 : List Nat := [2, 1, 2, 1, 5, 1, 4, 7]
def baseStart_1363000 : Nat := 118140960795 + 1363000 * 2 ^ 59
def prefixEnd_1363000 : Nat := 4983230072969 + 3 ^ 40 * 1363000 * 2
def baseEnd_1363000 : Nat := 25921264151047129256729

theorem tailTrace_1363000 : CollatzResearch.WordTrace tailWord_1363000 prefixEnd_1363000 25921264151047129256729 := by
  unfold tailWord_1363000
  simp only [CollatzResearch.WordTrace]
  refine ⟨24856347031045628356199227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33141796041394171141598969 24856347031045628356199227)
  ·
    refine ⟨37284520546568442534298841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24856347031045628356199227 37284520546568442534298841)
    ·
      refine ⟨27963390409926331900724131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37284520546568442534298841 27963390409926331900724131)
      ·
        refine ⟨41945085614889497851086197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27963390409926331900724131 41945085614889497851086197)
        ·
          refine ⟨3932351776395890423539331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41945085614889497851086197 3932351776395890423539331)
          ·
            refine ⟨5898527664593835635308997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932351776395890423539331 5898527664593835635308997)
            ·
              refine ⟨1105973937111344181620437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5898527664593835635308997 1105973937111344181620437)
              ·
                refine ⟨25921264151047129256729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1105973937111344181620437 25921264151047129256729)
                ·
                  rfl

theorem cell23_1363000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 7].length) (baseStart_1363000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363000 prefixEnd_1363000 := by exact prefixLift 1363000
  have htrace : WordTrace (prefixWord ++ tailWord_1363000) baseStart_1363000 baseEnd_1363000 := by
    simpa [prefixWord, tailWord_1363000, baseEnd_1363000] using wordTrace_append hprefix tailTrace_1363000
  have hstable : (prefixWord ++ tailWord_1363000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363000).length < 2 ^ (prefixWord ++ tailWord_1363000).sum := by decide
  have hdescent : baseEnd_1363000 < baseStart_1363000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363014 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1363014 : Nat := 118140960795 + 1363014 * 2 ^ 59
def prefixEnd_1363014 : Nat := 4983230072969 + 3 ^ 40 * 1363014 * 2
def baseEnd_1363014 : Nat := 699881320807435435156619

theorem tailTrace_1363014 : CollatzResearch.WordTrace tailWord_1363014 prefixEnd_1363014 699881320807435435156619 := by
  unfold tailWord_1363014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553537646376266784481503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33142136456027024735605397 1553537646376266784481503)
  ·
    refine ⟨2330306469564400176722255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1553537646376266784481503 2330306469564400176722255)
    ·
      refine ⟨3495459704346600265083383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2330306469564400176722255 3495459704346600265083383)
      ·
        refine ⟨5243189556519900397625075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495459704346600265083383 5243189556519900397625075)
        ·
          refine ⟨7864784334779850596437613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243189556519900397625075 7864784334779850596437613)
          ·
            refine ⟨2949294125542443973664105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7864784334779850596437613 2949294125542443973664105)
            ·
              refine ⟨2211970594156832980248079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949294125542443973664105 2211970594156832980248079)
              ·
                refine ⟨3317955891235249470372119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211970594156832980248079 3317955891235249470372119)
                ·
                  refine ⟨4976933836852874205558179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317955891235249470372119 4976933836852874205558179)
                  ·
                    refine ⟨7465400755279311308337269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976933836852874205558179 7465400755279311308337269)
                    ·
                      refine ⟨699881320807435435156619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7465400755279311308337269 699881320807435435156619)
                      ·
                        rfl

theorem cell23_1363014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1363014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363014 prefixEnd_1363014 := by exact prefixLift 1363014
  have htrace : WordTrace (prefixWord ++ tailWord_1363014) baseStart_1363014 baseEnd_1363014 := by
    simpa [prefixWord, tailWord_1363014, baseEnd_1363014] using wordTrace_append hprefix tailTrace_1363014
  have hstable : (prefixWord ++ tailWord_1363014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363014).length < 2 ^ (prefixWord ++ tailWord_1363014).sum := by decide
  have hdescent : baseEnd_1363014 < baseStart_1363014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363038 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1363038 : Nat := 118140960795 + 1363038 * 2 ^ 59
def prefixEnd_1363038 : Nat := 4983230072969 + 3 ^ 40 * 1363038 * 2
def baseEnd_1363038 : Nat := 233297881447714447085503

theorem tailTrace_1363038 : CollatzResearch.WordTrace tailWord_1363038 prefixEnd_1363038 233297881447714447085503 := by
  unfold tailWord_1363038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214260004494198650285221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33142720023969059468187845 6214260004494198650285221)
  ·
    refine ⟨1165173750842662246928479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6214260004494198650285221 1165173750842662246928479)
    ·
      refine ⟨1747760626263993370392719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165173750842662246928479 1747760626263993370392719)
      ·
        refine ⟨2621640939395990055589079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747760626263993370392719 2621640939395990055589079)
        ·
          refine ⟨3932461409093985083383619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621640939395990055589079 3932461409093985083383619)
          ·
            refine ⟨5898692113640977625075429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932461409093985083383619 5898692113640977625075429)
            ·
              refine ⟨1106004771307683304701643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5898692113640977625075429 1106004771307683304701643)
              ·
                refine ⟨1659007156961524957052465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106004771307683304701643 1659007156961524957052465)
                ·
                  refine ⟨1244255367721143717789349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1659007156961524957052465 1244255367721143717789349)
                  ·
                    refine ⟨233297881447714447085503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244255367721143717789349 233297881447714447085503)
                    ·
                      rfl

theorem cell23_1363038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1363038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363038 prefixEnd_1363038 := by exact prefixLift 1363038
  have htrace : WordTrace (prefixWord ++ tailWord_1363038) baseStart_1363038 baseEnd_1363038 := by
    simpa [prefixWord, tailWord_1363038, baseEnd_1363038] using wordTrace_append hprefix tailTrace_1363038
  have hstable : (prefixWord ++ tailWord_1363038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363038).length < 2 ^ (prefixWord ++ tailWord_1363038).sum := by decide
  have hdescent : baseEnd_1363038 < baseStart_1363038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363043 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 8]
def baseStart_1363043 : Nat := 118140960795 + 1363043 * 2 ^ 59
def prefixEnd_1363043 : Nat := 4983230072969 + 3 ^ 40 * 1363043 * 2
def baseEnd_1363043 : Nat := 233298737248805273897995

theorem tailTrace_1363043 : CollatzResearch.WordTrace tailWord_1363043 prefixEnd_1363043 233298737248805273897995 := by
  unfold tailWord_1363043
  simp only [CollatzResearch.WordTrace]
  refine ⟨49714262400935475056213783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33142841600623650037475855 49714262400935475056213783)
  ·
    refine ⟨74571393601403212584320675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49714262400935475056213783 74571393601403212584320675)
    ·
      refine ⟨111857090402104818876481013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74571393601403212584320675 111857090402104818876481013)
      ·
        refine ⟨10486602225197326769670095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111857090402104818876481013 10486602225197326769670095)
        ·
          refine ⟨15729903337795990154505143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486602225197326769670095 15729903337795990154505143)
          ·
            refine ⟨23594855006693985231757715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729903337795990154505143 23594855006693985231757715)
            ·
              refine ⟨35392282510040977847636573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23594855006693985231757715 35392282510040977847636573)
              ·
                refine ⟨13272105941265366692863715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35392282510040977847636573 13272105941265366692863715)
                ·
                  refine ⟨19908158911898050039295573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13272105941265366692863715 19908158911898050039295573)
                  ·
                    refine ⟨233298737248805273897995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19908158911898050039295573 233298737248805273897995)
                    ·
                      rfl

theorem cell23_1363043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_1363043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363043 prefixEnd_1363043 := by exact prefixLift 1363043
  have htrace : WordTrace (prefixWord ++ tailWord_1363043) baseStart_1363043 baseEnd_1363043 := by
    simpa [prefixWord, tailWord_1363043, baseEnd_1363043] using wordTrace_append hprefix tailTrace_1363043
  have hstable : (prefixWord ++ tailWord_1363043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363043).length < 2 ^ (prefixWord ++ tailWord_1363043).sum := by decide
  have hdescent : baseEnd_1363043 < baseStart_1363043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363048 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1363048 : Nat := 118140960795 + 1363048 * 2 ^ 59
def prefixEnd_1363048 : Nat := 4983230072969 + 3 ^ 40 * 1363048 * 2
def baseEnd_1363048 : Nat := 699898779149688302131463

theorem tailTrace_1363048 : CollatzResearch.WordTrace tailWord_1363048 prefixEnd_1363048 699898779149688302131463 := by
  unfold tailWord_1363048
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857222382958680455072899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33142963177278240606763865 24857222382958680455072899)
  ·
    refine ⟨37285833574438020682609349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24857222382958680455072899 37285833574438020682609349)
    ·
      refine ⟨6991093795207128877989253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37285833574438020682609349 6991093795207128877989253)
      ·
        refine ⟨1310830086601336664622985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6991093795207128877989253 1310830086601336664622985)
        ·
          refine ⟨983122564951002498467239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310830086601336664622985 983122564951002498467239)
          ·
            refine ⟨1474683847426503747700859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983122564951002498467239 1474683847426503747700859)
            ·
              refine ⟨2212025771139755621551289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474683847426503747700859 2212025771139755621551289)
              ·
                refine ⟨1659019328354816716163467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212025771139755621551289 1659019328354816716163467)
                ·
                  refine ⟨2488528992532225074245201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659019328354816716163467 2488528992532225074245201)
                  ·
                    refine ⟨1866396744399168805683901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2488528992532225074245201 1866396744399168805683901)
                    ·
                      refine ⟨699898779149688302131463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1866396744399168805683901 699898779149688302131463)
                      ·
                        rfl

theorem cell23_1363048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1363048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363048 prefixEnd_1363048 := by exact prefixLift 1363048
  have htrace : WordTrace (prefixWord ++ tailWord_1363048) baseStart_1363048 baseEnd_1363048 := by
    simpa [prefixWord, tailWord_1363048, baseEnd_1363048] using wordTrace_append hprefix tailTrace_1363048
  have hstable : (prefixWord ++ tailWord_1363048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363048).length < 2 ^ (prefixWord ++ tailWord_1363048).sum := by decide
  have hdescent : baseEnd_1363048 < baseStart_1363048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363054 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1363054 : Nat := 118140960795 + 1363054 * 2 ^ 59
def prefixEnd_1363054 : Nat := 4983230072969 + 3 ^ 40 * 1363054 * 2
def baseEnd_1363054 : Nat := 699901860033615278656435

theorem tailTrace_1363054 : CollatzResearch.WordTrace tailWord_1363054 prefixEnd_1363054 699901860033615278656435 := by
  unfold tailWord_1363054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214332950486952991858027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33143109069263749289909477 6214332950486952991858027)
  ·
    refine ⟨9321499425730429487787041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6214332950486952991858027 9321499425730429487787041)
    ·
      refine ⟨6991124569297822115840281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9321499425730429487787041 6991124569297822115840281)
      ·
        refine ⟨5243343426973366586880211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6991124569297822115840281 5243343426973366586880211)
        ·
          refine ⟨7865015140460049880320317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243343426973366586880211 7865015140460049880320317)
          ·
            refine ⟨2949380677672518705120119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7865015140460049880320317 2949380677672518705120119)
            ·
              refine ⟨4424071016508778057680179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949380677672518705120119 4424071016508778057680179)
              ·
                refine ⟨6636106524763167086520269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424071016508778057680179 6636106524763167086520269)
                ·
                  refine ⟨2488539946786187657445101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6636106524763167086520269 2488539946786187657445101)
                  ·
                    refine ⟨933202480044820371541913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2488539946786187657445101 933202480044820371541913)
                    ·
                      refine ⟨699901860033615278656435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933202480044820371541913 699901860033615278656435)
                      ·
                        rfl

theorem cell23_1363054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1363054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363054 prefixEnd_1363054 := by exact prefixLift 1363054
  have htrace : WordTrace (prefixWord ++ tailWord_1363054) baseStart_1363054 baseEnd_1363054 := by
    simpa [prefixWord, tailWord_1363054, baseEnd_1363054] using wordTrace_append hprefix tailTrace_1363054
  have hstable : (prefixWord ++ tailWord_1363054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363054).length < 2 ^ (prefixWord ++ tailWord_1363054).sum := by decide
  have hdescent : baseEnd_1363054 < baseStart_1363054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363067 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 6, 2, 2]
def baseStart_1363067 : Nat := 118140960795 + 1363067 * 2 ^ 59
def prefixEnd_1363067 : Nat := 4983230072969 + 3 ^ 40 * 1363067 * 2
def baseEnd_1363067 : Nat := 699908535282123727793875

theorem tailTrace_1363067 : CollatzResearch.WordTrace tailWord_1363067 prefixEnd_1363067 699908535282123727793875 := by
  unfold tailWord_1363067
  simp only [CollatzResearch.WordTrace]
  refine ⟨49715137752848527155087455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33143425168565684770058303 49715137752848527155087455)
  ·
    refine ⟨74572706629272790732631183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49715137752848527155087455 74572706629272790732631183)
    ·
      refine ⟨111859059943909186098946775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74572706629272790732631183 111859059943909186098946775)
      ·
        refine ⟨167788589915863779148420163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111859059943909186098946775 167788589915863779148420163)
        ·
          refine ⟨251682884873795668722630245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167788589915863779148420163 251682884873795668722630245)
          ·
            refine ⟨47190540913836687885493171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251682884873795668722630245 47190540913836687885493171)
            ·
              refine ⟨70785811370755031828239757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47190540913836687885493171 70785811370755031828239757)
              ·
                refine ⟨26544679264033136935589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70785811370755031828239757 26544679264033136935589909)
                ·
                  refine ⟨1244281840501553293855777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26544679264033136935589909 1244281840501553293855777)
                  ·
                    refine ⟨933211380376164970391833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1244281840501553293855777 933211380376164970391833)
                    ·
                      refine ⟨699908535282123727793875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933211380376164970391833 699908535282123727793875)
                      ·
                        rfl

theorem cell23_1363067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2, 2].length) (baseStart_1363067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363067 prefixEnd_1363067 := by exact prefixLift 1363067
  have htrace : WordTrace (prefixWord ++ tailWord_1363067) baseStart_1363067 baseEnd_1363067 := by
    simpa [prefixWord, tailWord_1363067, baseEnd_1363067] using wordTrace_append hprefix tailTrace_1363067
  have hstable : (prefixWord ++ tailWord_1363067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363067).length < 2 ^ (prefixWord ++ tailWord_1363067).sum := by decide
  have hdescent : baseEnd_1363067 < baseStart_1363067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363083 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_1363083 : Nat := 118140960795 + 1363083 * 2 ^ 59
def prefixEnd_1363083 : Nat := 4983230072969 + 3 ^ 40 * 1363083 * 2
def baseEnd_1363083 : Nat := 699916750972595665193801

theorem tailTrace_1363083 : CollatzResearch.WordTrace tailWord_1363083 prefixEnd_1363083 699916750972595665193801 := by
  unfold tailWord_1363083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49715721320790561887669903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33143814213860374591779935 49715721320790561887669903)
  ·
    refine ⟨74573581981185842831504855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49715721320790561887669903 74573581981185842831504855)
    ·
      refine ⟨111860372971778764247257283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74573581981185842831504855 111860372971778764247257283)
      ·
        refine ⟨167790559457668146370885925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111860372971778764247257283 167790559457668146370885925)
        ·
          refine ⟨31460729898312777444541111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167790559457668146370885925 31460729898312777444541111)
          ·
            refine ⟨47191094847469166166811667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31460729898312777444541111 47191094847469166166811667)
            ·
              refine ⟨70786642271203749250217501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47191094847469166166811667 70786642271203749250217501)
              ·
                refine ⟨26544990851701405968831563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70786642271203749250217501 26544990851701405968831563)
                ·
                  refine ⟨39817486277552108953247345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26544990851701405968831563 39817486277552108953247345)
                  ·
                    refine ⟨29863114708164081714935509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39817486277552108953247345 29863114708164081714935509)
                    ·
                      refine ⟨699916750972595665193801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29863114708164081714935509 699916750972595665193801)
                      ·
                        rfl

theorem cell23_1363083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_1363083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363083 prefixEnd_1363083 := by exact prefixLift 1363083
  have htrace : WordTrace (prefixWord ++ tailWord_1363083) baseStart_1363083 baseEnd_1363083 := by
    simpa [prefixWord, tailWord_1363083, baseEnd_1363083] using wordTrace_append hprefix tailTrace_1363083
  have hstable : (prefixWord ++ tailWord_1363083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363083).length < 2 ^ (prefixWord ++ tailWord_1363083).sum := by decide
  have hdescent : baseEnd_1363083 < baseStart_1363083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363157 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1363157 : Nat := 118140960795 + 1363157 * 2 ^ 59
def prefixEnd_1363157 : Nat := 4983230072969 + 3 ^ 40 * 1363157 * 2
def baseEnd_1363157 : Nat := 699954748541028375668461

theorem tailTrace_1363157 : CollatzResearch.WordTrace tailWord_1363157 prefixEnd_1363157 699954748541028375668461 := by
  unfold tailWord_1363157
  simp only [CollatzResearch.WordTrace]
  refine ⟨49718420322522472525863725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33145613548348315017242483 49718420322522472525863725)
  ·
    refine ⟨18644407620945927197198897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49718420322522472525863725 18644407620945927197198897)
    ·
      refine ⟨13983305715709445397899173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18644407620945927197198897 13983305715709445397899173)
      ·
        refine ⟨2621869821695521012106095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13983305715709445397899173 2621869821695521012106095)
        ·
          refine ⟨3932804732543281518159143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621869821695521012106095 3932804732543281518159143)
          ·
            refine ⟨5899207098814922277238715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932804732543281518159143 5899207098814922277238715)
            ·
              refine ⟨8848810648222383415858073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899207098814922277238715 8848810648222383415858073)
              ·
                refine ⟨6636607986166787561893555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8848810648222383415858073 6636607986166787561893555)
                ·
                  refine ⟨9954911979250181342840333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636607986166787561893555 9954911979250181342840333)
                  ·
                    refine ⟨3733091992218818003565125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9954911979250181342840333 3733091992218818003565125)
                    ·
                      refine ⟨699954748541028375668461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3733091992218818003565125 699954748541028375668461)
                      ·
                        rfl

theorem cell23_1363157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1363157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363157 prefixEnd_1363157 := by exact prefixLift 1363157
  have htrace : WordTrace (prefixWord ++ tailWord_1363157) baseStart_1363157 baseEnd_1363157 := by
    simpa [prefixWord, tailWord_1363157, baseEnd_1363157] using wordTrace_append hprefix tailTrace_1363157
  have hstable : (prefixWord ++ tailWord_1363157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363157).length < 2 ^ (prefixWord ++ tailWord_1363157).sum := by decide
  have hdescent : baseEnd_1363157 < baseStart_1363157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363167 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 3, 4]
def baseStart_1363167 : Nat := 118140960795 + 1363167 * 2 ^ 59
def prefixEnd_1363167 : Nat := 4983230072969 + 3 ^ 40 * 1363167 * 2
def baseEnd_1363167 : Nat := 233319961115857778847805

theorem tailTrace_1363167 : CollatzResearch.WordTrace tailWord_1363167 prefixEnd_1363167 233319961115857778847805 := by
  unfold tailWord_1363167
  simp only [CollatzResearch.WordTrace]
  refine ⟨49718785052486244233727755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33145856701657496155818503 49718785052486244233727755)
  ·
    refine ⟨74578177578729366350591633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49718785052486244233727755 74578177578729366350591633)
    ·
      refine ⟨55933633184047024762943725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74578177578729366350591633 55933633184047024762943725)
      ·
        refine ⟨20975112444017634286103897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55933633184047024762943725 20975112444017634286103897)
        ·
          refine ⟨15731334333013225714577923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20975112444017634286103897 15731334333013225714577923)
          ·
            refine ⟨23597001499519838571866885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15731334333013225714577923 23597001499519838571866885)
            ·
              refine ⟨4424437781159969732225041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23597001499519838571866885 4424437781159969732225041)
              ·
                refine ⟨3318328335869977299168781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424437781159969732225041 3318328335869977299168781)
                ·
                  refine ⟨1244373125951241487188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3318328335869977299168781 1244373125951241487188293)
                  ·
                    refine ⟨233319961115857778847805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244373125951241487188293 233319961115857778847805)
                    ·
                      rfl

theorem cell23_1363167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_1363167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363167 prefixEnd_1363167 := by exact prefixLift 1363167
  have htrace : WordTrace (prefixWord ++ tailWord_1363167) baseStart_1363167 baseEnd_1363167 := by
    simpa [prefixWord, tailWord_1363167, baseEnd_1363167] using wordTrace_append hprefix tailTrace_1363167
  have hstable : (prefixWord ++ tailWord_1363167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363167).length < 2 ^ (prefixWord ++ tailWord_1363167).sum := by decide
  have hdescent : baseEnd_1363167 < baseStart_1363167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363180 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 8]
def baseStart_1363180 : Nat := 118140960795 + 1363180 * 2 ^ 59
def prefixEnd_1363180 : Nat := 4983230072969 + 3 ^ 40 * 1363180 * 2
def baseEnd_1363180 : Nat := 77774062066231309520095

theorem tailTrace_1363180 : CollatzResearch.WordTrace tailWord_1363180 prefixEnd_1363180 77774062066231309520095 := by
  unfold tailWord_1363180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859629600719573726975497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33146172800959431635967329 24859629600719573726975497)
  ·
    refine ⟨18644722200539680295231623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24859629600719573726975497 18644722200539680295231623)
    ·
      refine ⟨27967083300809520442847435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18644722200539680295231623 27967083300809520442847435)
      ·
        refine ⟨41950624951214280664271153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27967083300809520442847435 41950624951214280664271153)
        ·
          refine ⟨31462968713410710498203365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41950624951214280664271153 31462968713410710498203365)
          ·
            refine ⟨5899306633764508218413131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31462968713410710498203365 5899306633764508218413131)
            ·
              refine ⟨8848959950646762327619697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899306633764508218413131 8848959950646762327619697)
              ·
                refine ⟨6636719962985071745714773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8848959950646762327619697 6636719962985071745714773)
                ·
                  refine ⟨77774062066231309520095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6636719962985071745714773 77774062066231309520095)
                  ·
                    rfl

theorem cell23_1363180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_1363180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363180 prefixEnd_1363180 := by exact prefixLift 1363180
  have htrace : WordTrace (prefixWord ++ tailWord_1363180) baseStart_1363180 baseEnd_1363180 := by
    simpa [prefixWord, tailWord_1363180, baseEnd_1363180] using wordTrace_append hprefix tailTrace_1363180
  have hstable : (prefixWord ++ tailWord_1363180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363180).length < 2 ^ (prefixWord ++ tailWord_1363180).sum := by decide
  have hdescent : baseEnd_1363180 < baseStart_1363180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363188 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1363188 : Nat := 118140960795 + 1363188 * 2 ^ 59
def prefixEnd_1363188 : Nat := 4983230072969 + 3 ^ 40 * 1363188 * 2
def baseEnd_1363188 : Nat := 233323555480439251460273

theorem tailTrace_1363188 : CollatzResearch.WordTrace tailWord_1363188 prefixEnd_1363188 233323555480439251460273 := by
  unfold tailWord_1363188
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859775492705082410121109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33146367323606776546828145 24859775492705082410121109)
  ·
    refine ⟨1165301976220550737974427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24859775492705082410121109 1165301976220550737974427)
    ·
      refine ⟨1747952964330826106961641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165301976220550737974427 1747952964330826106961641)
      ·
        refine ⟨1310964723248119580221231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1747952964330826106961641 1310964723248119580221231)
        ·
          refine ⟨1966447084872179370331847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310964723248119580221231 1966447084872179370331847)
          ·
            refine ⟨2949670627308269055497771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966447084872179370331847 2949670627308269055497771)
            ·
              refine ⟨4424505940962403583246657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949670627308269055497771 4424505940962403583246657)
              ·
                refine ⟨3318379455721802687434993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424505940962403583246657 3318379455721802687434993)
                ·
                  refine ⟨2488784591791352015576245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318379455721802687434993 2488784591791352015576245)
                  ·
                    refine ⟨233323555480439251460273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2488784591791352015576245 233323555480439251460273)
                    ·
                      rfl

theorem cell23_1363188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1363188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363188 prefixEnd_1363188 := by exact prefixLift 1363188
  have htrace : WordTrace (prefixWord ++ tailWord_1363188) baseStart_1363188 baseEnd_1363188 := by
    simpa [prefixWord, tailWord_1363188, baseEnd_1363188] using wordTrace_append hprefix tailTrace_1363188
  have hstable : (prefixWord ++ tailWord_1363188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363188).length < 2 ^ (prefixWord ++ tailWord_1363188).sum := by decide
  have hdescent : baseEnd_1363188 < baseStart_1363188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363210 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_1363210 : Nat := 118140960795 + 1363210 * 2 ^ 59
def prefixEnd_1363210 : Nat := 4983230072969 + 3 ^ 40 * 1363210 * 2
def baseEnd_1363210 : Nat := 233327321005238889435239

theorem tailTrace_1363210 : CollatzResearch.WordTrace tailWord_1363210 prefixEnd_1363210 233327321005238889435239 := by
  unfold tailWord_1363210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12430088347832615644385771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33146902260886975051695389 12430088347832615644385771)
  ·
    refine ⟨18645132521748923466578657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12430088347832615644385771 18645132521748923466578657)
    ·
      refine ⟨13983849391311692599933993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18645132521748923466578657 13983849391311692599933993)
      ·
        refine ⟨10487887043483769449950495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13983849391311692599933993 10487887043483769449950495)
        ·
          refine ⟨15731830565225654174925743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10487887043483769449950495 15731830565225654174925743)
          ·
            refine ⟨23597745847838481262388615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15731830565225654174925743 23597745847838481262388615)
            ·
              refine ⟨35396618771757721893582923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23597745847838481262388615 35396618771757721893582923)
              ·
                refine ⟨53094928157636582840374385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35396618771757721893582923 53094928157636582840374385)
                ·
                  refine ⟨39821196118227437130280789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53094928157636582840374385 39821196118227437130280789)
                  ·
                    refine ⟨233327321005238889435239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39821196118227437130280789 233327321005238889435239)
                    ·
                      rfl

theorem cell23_1363210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_1363210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363210 prefixEnd_1363210 := by exact prefixLift 1363210
  have htrace : WordTrace (prefixWord ++ tailWord_1363210) baseStart_1363210 baseEnd_1363210 := by
    simpa [prefixWord, tailWord_1363210, baseEnd_1363210] using wordTrace_append hprefix tailTrace_1363210
  have hstable : (prefixWord ++ tailWord_1363210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363210).length < 2 ^ (prefixWord ++ tailWord_1363210).sum := by decide
  have hdescent : baseEnd_1363210 < baseStart_1363210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363214 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_1363214 : Nat := 118140960795 + 1363214 * 2 ^ 59
def prefixEnd_1363214 : Nat := 4983230072969 + 3 ^ 40 * 1363214 * 2
def baseEnd_1363214 : Nat := 77776001882037183628411

theorem tailTrace_1363214 : CollatzResearch.WordTrace tailWord_1363214 prefixEnd_1363214 77776001882037183628411 := by
  unfold tailWord_1363214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215062410414496407586087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33146999522210647507125797 6215062410414496407586087)
  ·
    refine ⟨9322593615621744611379131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215062410414496407586087 9322593615621744611379131)
    ·
      refine ⟨13983890423432616917068697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9322593615621744611379131 13983890423432616917068697)
      ·
        refine ⟨10487917817574462687801523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13983890423432616917068697 10487917817574462687801523)
        ·
          refine ⟨15731876726361694031702285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10487917817574462687801523 15731876726361694031702285)
          ·
            refine ⟨5899453772385635261888357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15731876726361694031702285 5899453772385635261888357)
            ·
              refine ⟨1106147582322306611604067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5899453772385635261888357 1106147582322306611604067)
              ·
                refine ⟨1659221373483459917406101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106147582322306611604067 1659221373483459917406101)
                ·
                  refine ⟨77776001882037183628411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1659221373483459917406101 77776001882037183628411)
                  ·
                    rfl

theorem cell23_1363214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_1363214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363214 prefixEnd_1363214 := by exact prefixLift 1363214
  have htrace : WordTrace (prefixWord ++ tailWord_1363214) baseStart_1363214 baseEnd_1363214 := by
    simpa [prefixWord, tailWord_1363214, baseEnd_1363214] using wordTrace_append hprefix tailTrace_1363214
  have hstable : (prefixWord ++ tailWord_1363214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363214).length < 2 ^ (prefixWord ++ tailWord_1363214).sum := by decide
  have hdescent : baseEnd_1363214 < baseStart_1363214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363281 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_1363281 : Nat := 118140960795 + 1363281 * 2 ^ 59
def prefixEnd_1363281 : Nat := 4983230072969 + 3 ^ 40 * 1363281 * 2
def baseEnd_1363281 : Nat := 700018420142185890517891

theorem tailTrace_1363281 : CollatzResearch.WordTrace tailWord_1363281 prefixEnd_1363281 700018420142185890517891 := by
  unfold tailWord_1363281
  simp only [CollatzResearch.WordTrace]
  refine ⟨49722942974073241703377697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33148628649382161135585131 49722942974073241703377697)
  ·
    refine ⟨37292207230554931277533273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49722942974073241703377697 37292207230554931277533273)
    ·
      refine ⟨27969155422916198458149955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37292207230554931277533273 27969155422916198458149955)
      ·
        refine ⟨41953733134374297687224933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27969155422916198458149955 41953733134374297687224933)
        ·
          refine ⟨7866324962695180816354675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41953733134374297687224933 7866324962695180816354675)
          ·
            refine ⟨11799487444042771224532013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866324962695180816354675 11799487444042771224532013)
            ·
              refine ⟨4424807791516039209199505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11799487444042771224532013 4424807791516039209199505)
              ·
                refine ⟨3318605843637029406899629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424807791516039209199505 3318605843637029406899629)
                ·
                  refine ⟨1244477191363886027587361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3318605843637029406899629 1244477191363886027587361)
                  ·
                    refine ⟨933357893522914520690521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1244477191363886027587361 933357893522914520690521)
                    ·
                      refine ⟨700018420142185890517891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933357893522914520690521 700018420142185890517891)
                      ·
                        rfl

theorem cell23_1363281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_1363281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363281 prefixEnd_1363281 := by exact prefixLift 1363281
  have htrace : WordTrace (prefixWord ++ tailWord_1363281) baseStart_1363281 baseEnd_1363281 := by
    simpa [prefixWord, tailWord_1363281, baseEnd_1363281] using wordTrace_append hprefix tailTrace_1363281
  have hstable : (prefixWord ++ tailWord_1363281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363281).length < 2 ^ (prefixWord ++ tailWord_1363281).sum := by decide
  have hdescent : baseEnd_1363281 < baseStart_1363281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363284 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1363284 : Nat := 118140960795 + 1363284 * 2 ^ 59
def prefixEnd_1363284 : Nat := 4983230072969 + 3 ^ 40 * 1363284 * 2
def baseEnd_1363284 : Nat := 700019960584149378780377

theorem tailTrace_1363284 : CollatzResearch.WordTrace tailWord_1363284 prefixEnd_1363284 700019960584149378780377 := by
  unfold tailWord_1363284
  simp only [CollatzResearch.WordTrace]
  refine ⟨24861526196531186607868453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33148701595374915477157937 24861526196531186607868453)
  ·
    refine ⟨4661536161849597488975335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24861526196531186607868453 4661536161849597488975335)
    ·
      refine ⟨6992304242774396233463003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661536161849597488975335 6992304242774396233463003)
      ·
        refine ⟨10488456364161594350194505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992304242774396233463003 10488456364161594350194505)
        ·
          refine ⟨7866342273121195762645879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10488456364161594350194505 7866342273121195762645879)
          ·
            refine ⟨11799513409681793643968819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866342273121195762645879 11799513409681793643968819)
            ·
              refine ⟨17699270114522690465953229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11799513409681793643968819 17699270114522690465953229)
              ·
                refine ⟨6637226292946008924732461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17699270114522690465953229 6637226292946008924732461)
                ·
                  refine ⟨2488959859854753346774673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6637226292946008924732461 2488959859854753346774673)
                  ·
                    refine ⟨1866719894891065010081005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2488959859854753346774673 1866719894891065010081005)
                    ·
                      refine ⟨700019960584149378780377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1866719894891065010081005 700019960584149378780377)
                      ·
                        rfl

theorem cell23_1363284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1363284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363284 prefixEnd_1363284 := by exact prefixLift 1363284
  have htrace : WordTrace (prefixWord ++ tailWord_1363284) baseStart_1363284 baseEnd_1363284 := by
    simpa [prefixWord, tailWord_1363284, baseEnd_1363284] using wordTrace_append hprefix tailTrace_1363284
  have hstable : (prefixWord ++ tailWord_1363284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363284).length < 2 ^ (prefixWord ++ tailWord_1363284).sum := by decide
  have hdescent : baseEnd_1363284 < baseStart_1363284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363331 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 3]
def baseStart_1363331 : Nat := 118140960795 + 1363331 * 2 ^ 59
def prefixEnd_1363331 : Nat := 4983230072969 + 3 ^ 40 * 1363331 * 2
def baseEnd_1363331 : Nat := 700044094174910694892661

theorem tailTrace_1363331 : CollatzResearch.WordTrace tailWord_1363331 prefixEnd_1363331 700044094174910694892661 := by
  unfold tailWord_1363331
  simp only [CollatzResearch.WordTrace]
  refine ⟨49724766623892100242697847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33149844415928066828465231 49724766623892100242697847)
  ·
    refine ⟨74587149935838150364046771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49724766623892100242697847 74587149935838150364046771)
    ·
      refine ⟨111880724903757225546070157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74587149935838150364046771 111880724903757225546070157)
      ·
        refine ⟨41955271838908959579776309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111880724903757225546070157 41955271838908959579776309)
        ·
          refine ⟨3933306734897714960604029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41955271838908959579776309 3933306734897714960604029)
          ·
            refine ⟨1474990025586643110226511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3933306734897714960604029 1474990025586643110226511)
            ·
              refine ⟨2212485038379964665339767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474990025586643110226511 2212485038379964665339767)
              ·
                refine ⟨3318727557569946998009651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212485038379964665339767 3318727557569946998009651)
                ·
                  refine ⟨4978091336354920497014477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318727557569946998009651 4978091336354920497014477)
                  ·
                    refine ⟨1866784251133095186380429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4978091336354920497014477 1866784251133095186380429)
                    ·
                      refine ⟨700044094174910694892661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1866784251133095186380429 700044094174910694892661)
                      ·
                        rfl

theorem cell23_1363331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_1363331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363331 prefixEnd_1363331 := by exact prefixLift 1363331
  have htrace : WordTrace (prefixWord ++ tailWord_1363331) baseStart_1363331 baseEnd_1363331 := by
    simpa [prefixWord, tailWord_1363331, baseEnd_1363331] using wordTrace_append hprefix tailTrace_1363331
  have hstable : (prefixWord ++ tailWord_1363331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363331).length < 2 ^ (prefixWord ++ tailWord_1363331).sum := by decide
  have hdescent : baseEnd_1363331 < baseStart_1363331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363407 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 7]
def baseStart_1363407 : Nat := 118140960795 + 1363407 * 2 ^ 59
def prefixEnd_1363407 : Nat := 4983230072969 + 3 ^ 40 * 1363407 * 2
def baseEnd_1363407 : Nat := 233361039568217465847437

theorem tailTrace_1363407 : CollatzResearch.WordTrace tailWord_1363407 prefixEnd_1363407 233361039568217465847437 := by
  unfold tailWord_1363407
  simp only [CollatzResearch.WordTrace]
  refine ⟨49727538571616765222464475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33151692381077843481642983 49727538571616765222464475)
  ·
    refine ⟨74591307857425147833696713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49727538571616765222464475 74591307857425147833696713)
    ·
      refine ⟨55943480893068860875272535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74591307857425147833696713 55943480893068860875272535)
      ·
        refine ⟨83915221339603291312908803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55943480893068860875272535 83915221339603291312908803)
        ·
          refine ⟨125872832009404936969363205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83915221339603291312908803 125872832009404936969363205)
          ·
            refine ⟨23601156001763425681755601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125872832009404936969363205 23601156001763425681755601)
            ·
              refine ⟨17700867001322569261316701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23601156001763425681755601 17700867001322569261316701)
              ·
                refine ⟨6637825125495963472993763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17700867001322569261316701 6637825125495963472993763)
                ·
                  refine ⟨9956737688243945209490645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6637825125495963472993763 9956737688243945209490645)
                  ·
                    refine ⟨233361039568217465847437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9956737688243945209490645 233361039568217465847437)
                    ·
                      rfl

theorem cell23_1363407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_1363407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363407 prefixEnd_1363407 := by exact prefixLift 1363407
  have htrace : WordTrace (prefixWord ++ tailWord_1363407) baseStart_1363407 baseEnd_1363407 := by
    simpa [prefixWord, tailWord_1363407, baseEnd_1363407] using wordTrace_append hprefix tailTrace_1363407
  have hstable : (prefixWord ++ tailWord_1363407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363407).length < 2 ^ (prefixWord ++ tailWord_1363407).sum := by decide
  have hdescent : baseEnd_1363407 < baseStart_1363407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363431 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1363431 : Nat := 118140960795 + 1363431 * 2 ^ 59
def prefixEnd_1363431 : Nat := 4983230072969 + 3 ^ 40 * 1363431 * 2
def baseEnd_1363431 : Nat := 700095442240360303642201

theorem tailTrace_1363431 : CollatzResearch.WordTrace tailWord_1363431 prefixEnd_1363431 700095442240360303642201 := by
  unfold tailWord_1363431
  simp only [CollatzResearch.WordTrace]
  refine ⟨49728413923529817321338147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33152275949019878214225431 49728413923529817321338147)
  ·
    refine ⟨74592620885294725982007221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49728413923529817321338147 74592620885294725982007221)
    ·
      refine ⟨6993058207996380560813177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74592620885294725982007221 6993058207996380560813177)
      ·
        refine ⟨5244793655997285420609883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6993058207996380560813177 5244793655997285420609883)
        ·
          refine ⟨7867190483995928130914825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244793655997285420609883 7867190483995928130914825)
          ·
            refine ⟨5900392862996946098186119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867190483995928130914825 5900392862996946098186119)
            ·
              refine ⟨8850589294495419147279179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900392862996946098186119 8850589294495419147279179)
              ·
                refine ⟨13275883941743128720918769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850589294495419147279179 13275883941743128720918769)
                ·
                  refine ⟨9956912956307346540689077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13275883941743128720918769 9956912956307346540689077)
                  ·
                    refine ⟨933460589653813738189601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9956912956307346540689077 933460589653813738189601)
                    ·
                      refine ⟨700095442240360303642201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933460589653813738189601 700095442240360303642201)
                      ·
                        rfl

theorem cell23_1363431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1363431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363431 prefixEnd_1363431 := by exact prefixLift 1363431
  have htrace : WordTrace (prefixWord ++ tailWord_1363431) baseStart_1363431 baseEnd_1363431 := by
    simpa [prefixWord, tailWord_1363431, baseEnd_1363431] using wordTrace_append hprefix tailTrace_1363431
  have hstable : (prefixWord ++ tailWord_1363431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363431).length < 2 ^ (prefixWord ++ tailWord_1363431).sum := by decide
  have hdescent : baseEnd_1363431 < baseStart_1363431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363458 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1363458 : Nat := 118140960795 + 1363458 * 2 ^ 59
def prefixEnd_1363458 : Nat := 4983230072969 + 3 ^ 40 * 1363458 * 2
def baseEnd_1363458 : Nat := 233369768739343899334859

theorem tailTrace_1363458 : CollatzResearch.WordTrace tailWord_1363458 prefixEnd_1363458 233369768739343899334859 := by
  unfold tailWord_1363458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432349673608000233142757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33152932462954667288380685 12432349673608000233142757)
  ·
    refine ⟨2331065563801500043714267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12432349673608000233142757 2331065563801500043714267)
    ·
      refine ⟨3496598345702250065571401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331065563801500043714267 3496598345702250065571401)
      ·
        refine ⟨2622448759276687549178551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496598345702250065571401 2622448759276687549178551)
        ·
          refine ⟨3933673138915031323767827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622448759276687549178551 3933673138915031323767827)
          ·
            refine ⟨5900509708372546985651741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933673138915031323767827 5900509708372546985651741)
            ·
              refine ⟨2212691140639705119619403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5900509708372546985651741 2212691140639705119619403)
              ·
                refine ⟨3319036710959557679429105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212691140639705119619403 3319036710959557679429105)
                ·
                  refine ⟨2489277533219668259571829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319036710959557679429105 2489277533219668259571829)
                  ·
                    refine ⟨233369768739343899334859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2489277533219668259571829 233369768739343899334859)
                    ·
                      rfl

theorem cell23_1363458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1363458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363458 prefixEnd_1363458 := by exact prefixLift 1363458
  have htrace : WordTrace (prefixWord ++ tailWord_1363458) baseStart_1363458 baseEnd_1363458 := by
    simpa [prefixWord, tailWord_1363458, baseEnd_1363458] using wordTrace_append hprefix tailTrace_1363458
  have hstable : (prefixWord ++ tailWord_1363458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363458).length < 2 ^ (prefixWord ++ tailWord_1363458).sum := by decide
  have hdescent : baseEnd_1363458 < baseStart_1363458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363484 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 8]
def baseStart_1363484 : Nat := 118140960795 + 1363484 * 2 ^ 59
def prefixEnd_1363484 : Nat := 4983230072969 + 3 ^ 40 * 1363484 * 2
def baseEnd_1363484 : Nat := 77791406301672066253273

theorem tailTrace_1363484 : CollatzResearch.WordTrace tailWord_1363484 prefixEnd_1363484 77791406301672066253273 := by
  unfold tailWord_1363484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865173496168903686508753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33153564661558538248678337 24865173496168903686508753)
  ·
    refine ⟨18648880122126677764881565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24865173496168903686508753 18648880122126677764881565)
    ·
      refine ⟨6993330045797504161830587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18648880122126677764881565 6993330045797504161830587)
      ·
        refine ⟨10489995068696256242745881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993330045797504161830587 10489995068696256242745881)
        ·
          refine ⟨7867496301522192182059411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10489995068696256242745881 7867496301522192182059411)
          ·
            refine ⟨11801244452283288273089117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867496301522192182059411 11801244452283288273089117)
            ·
              refine ⟨4425466669606233102408419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11801244452283288273089117 4425466669606233102408419)
              ·
                refine ⟨6638200004409349653612629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425466669606233102408419 6638200004409349653612629)
                ·
                  refine ⟨77791406301672066253273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6638200004409349653612629 77791406301672066253273)
                  ·
                    rfl

theorem cell23_1363484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_1363484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363484 prefixEnd_1363484 := by exact prefixLift 1363484
  have htrace : WordTrace (prefixWord ++ tailWord_1363484) baseStart_1363484 baseEnd_1363484 := by
    simpa [prefixWord, tailWord_1363484, baseEnd_1363484] using wordTrace_append hprefix tailTrace_1363484
  have hstable : (prefixWord ++ tailWord_1363484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363484).length < 2 ^ (prefixWord ++ tailWord_1363484).sum := by decide
  have hdescent : baseEnd_1363484 < baseStart_1363484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363488 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_1363488 : Nat := 118140960795 + 1363488 * 2 ^ 59
def prefixEnd_1363488 : Nat := 4983230072969 + 3 ^ 40 * 1363488 * 2
def baseEnd_1363488 : Nat := 233374903545888860209813

theorem tailTrace_1363488 : CollatzResearch.WordTrace tailWord_1363488 prefixEnd_1363488 233374903545888860209813 := by
  unfold tailWord_1363488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865246442161658028081559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33153661922882210704108745 24865246442161658028081559)
  ·
    refine ⟨37297869663242487042122339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24865246442161658028081559 37297869663242487042122339)
    ·
      refine ⟨55946804494863730563183509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37297869663242487042122339 55946804494863730563183509)
      ·
        refine ⟨2622506460696737370149227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55946804494863730563183509 2622506460696737370149227)
        ·
          refine ⟨3933759691045106055223841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622506460696737370149227 3933759691045106055223841)
          ·
            refine ⟨2950319768283829541417881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3933759691045106055223841 2950319768283829541417881)
            ·
              refine ⟨2212739826212872156063411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950319768283829541417881 2212739826212872156063411)
              ·
                refine ⟨3319109739319308234095117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212739826212872156063411 3319109739319308234095117)
                ·
                  refine ⟨1244666152244740587785669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3319109739319308234095117 1244666152244740587785669)
                  ·
                    refine ⟨233374903545888860209813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1244666152244740587785669 233374903545888860209813)
                    ·
                      rfl

theorem cell23_1363488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_1363488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363488 prefixEnd_1363488 := by exact prefixLift 1363488
  have htrace : WordTrace (prefixWord ++ tailWord_1363488) baseStart_1363488 baseEnd_1363488 := by
    simpa [prefixWord, tailWord_1363488, baseEnd_1363488] using wordTrace_append hprefix tailTrace_1363488
  have hstable : (prefixWord ++ tailWord_1363488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363488).length < 2 ^ (prefixWord ++ tailWord_1363488).sum := by decide
  have hdescent : baseEnd_1363488 < baseStart_1363488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363538 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_1363538 : Nat := 118140960795 + 1363538 * 2 ^ 59
def prefixEnd_1363538 : Nat := 4983230072969 + 3 ^ 40 * 1363538 * 2
def baseEnd_1363538 : Nat := 700150384670391385004209

theorem tailTrace_1363538 : CollatzResearch.WordTrace tailWord_1363538 prefixEnd_1363538 700150384670391385004209 := by
  unfold tailWord_1363538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12433079133535543648870817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33154877689428116396988845 12433079133535543648870817)
  ·
    refine ⟨9324809350151657736653113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12433079133535543648870817 9324809350151657736653113)
    ·
      refine ⟨6993607012613743302489835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9324809350151657736653113 6993607012613743302489835)
      ·
        refine ⟨10490410518920614953734753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993607012613743302489835 10490410518920614953734753)
        ·
          refine ⟨7867807889190461215301065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10490410518920614953734753 7867807889190461215301065)
          ·
            refine ⟨5900855916892845911475799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867807889190461215301065 5900855916892845911475799)
            ·
              refine ⟨8851283875339268867213699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900855916892845911475799 8851283875339268867213699)
              ·
                refine ⟨13276925813008903300820549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8851283875339268867213699 13276925813008903300820549)
                ·
                  refine ⟨2489423589939169368903853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13276925813008903300820549 2489423589939169368903853)
                  ·
                    refine ⟨933533846227188513338945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489423589939169368903853 933533846227188513338945)
                    ·
                      refine ⟨700150384670391385004209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933533846227188513338945 700150384670391385004209)
                      ·
                        rfl

theorem cell23_1363538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_1363538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363538 prefixEnd_1363538 := by exact prefixLift 1363538
  have htrace : WordTrace (prefixWord ++ tailWord_1363538) baseStart_1363538 baseEnd_1363538 := by
    simpa [prefixWord, tailWord_1363538, baseEnd_1363538] using wordTrace_append hprefix tailTrace_1363538
  have hstable : (prefixWord ++ tailWord_1363538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363538).length < 2 ^ (prefixWord ++ tailWord_1363538).sum := by decide
  have hdescent : baseEnd_1363538 < baseStart_1363538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363565 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1363565 : Nat := 118140960795 + 1363565 * 2 ^ 59
def prefixEnd_1363565 : Nat := 4983230072969 + 3 ^ 40 * 1363565 * 2
def baseEnd_1363565 : Nat := 233388082882687593122195

theorem tailTrace_1363565 : CollatzResearch.WordTrace tailWord_1363565 prefixEnd_1363565 233388082882687593122195 := by
  unfold tailWord_1363565
  simp only [CollatzResearch.WordTrace]
  refine ⟨49733301305044358206716149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33155534203362905471144099 49733301305044358206716149)
  ·
    refine ⟨4662496997347908581879639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49733301305044358206716149 4662496997347908581879639)
    ·
      refine ⟨6993745496021862872819459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662496997347908581879639 6993745496021862872819459)
      ·
        refine ⟨10490618244032794309229189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993745496021862872819459 10490618244032794309229189)
        ·
          refine ⟨1966990920756148932980473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10490618244032794309229189 1966990920756148932980473)
          ·
            refine ⟨1475243190567111699735355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966990920756148932980473 1475243190567111699735355)
            ·
              refine ⟨2212864785850667549603033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475243190567111699735355 2212864785850667549603033)
              ·
                refine ⟨1659648589388000662202275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212864785850667549603033 1659648589388000662202275)
                ·
                  refine ⟨2489472884082000993303413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659648589388000662202275 2489472884082000993303413)
                  ·
                    refine ⟨233388082882687593122195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2489472884082000993303413 233388082882687593122195)
                    ·
                      rfl

theorem cell23_1363565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1363565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363565 prefixEnd_1363565 := by exact prefixLift 1363565
  have htrace : WordTrace (prefixWord ++ tailWord_1363565) baseStart_1363565 baseEnd_1363565 := by
    simpa [prefixWord, tailWord_1363565, baseEnd_1363565] using wordTrace_append hprefix tailTrace_1363565
  have hstable : (prefixWord ++ tailWord_1363565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363565).length < 2 ^ (prefixWord ++ tailWord_1363565).sum := by decide
  have hdescent : baseEnd_1363565 < baseStart_1363565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363568 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_1363568 : Nat := 118140960795 + 1363568 * 2 ^ 59
def prefixEnd_1363568 : Nat := 4983230072969 + 3 ^ 40 * 1363568 * 2
def baseEnd_1363568 : Nat := 700165789090026267629071

theorem tailTrace_1363568 : CollatzResearch.WordTrace tailWord_1363568 prefixEnd_1363568 700165789090026267629071 := by
  unfold tailWord_1363568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24866705362016744859537679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33155607149355659812716905 24866705362016744859537679)
  ·
    refine ⟨37300058043025117289306519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24866705362016744859537679 37300058043025117289306519)
    ·
      refine ⟨55950087064537675933959779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37300058043025117289306519 55950087064537675933959779)
      ·
        refine ⟨83925130596806513900939669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55950087064537675933959779 83925130596806513900939669)
        ·
          refine ⟨3933990496725305339106547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83925130596806513900939669 3933990496725305339106547)
          ·
            refine ⟨5900985745087958008659821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933990496725305339106547 5900985745087958008659821)
            ·
              refine ⟨2212869654407984253247433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5900985745087958008659821 2212869654407984253247433)
              ·
                refine ⟨1659652240805988189935575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212869654407984253247433 1659652240805988189935575)
                ·
                  refine ⟨2489478361208982284903363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659652240805988189935575 2489478361208982284903363)
                  ·
                    refine ⟨3734217541813473427355045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489478361208982284903363 3734217541813473427355045)
                    ·
                      refine ⟨700165789090026267629071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3734217541813473427355045 700165789090026267629071)
                      ·
                        rfl

theorem cell23_1363568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_1363568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363568 prefixEnd_1363568 := by exact prefixLift 1363568
  have htrace : WordTrace (prefixWord ++ tailWord_1363568) baseStart_1363568 baseEnd_1363568 := by
    simpa [prefixWord, tailWord_1363568, baseEnd_1363568] using wordTrace_append hprefix tailTrace_1363568
  have hstable : (prefixWord ++ tailWord_1363568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363568).length < 2 ^ (prefixWord ++ tailWord_1363568).sum := by decide
  have hdescent : baseEnd_1363568 < baseStart_1363568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363581 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1363581 : Nat := 118140960795 + 1363581 * 2 ^ 59
def prefixEnd_1363581 : Nat := 4983230072969 + 3 ^ 40 * 1363581 * 2
def baseEnd_1363581 : Nat := 700172464338534716766511

theorem tailTrace_1363581 : CollatzResearch.WordTrace tailWord_1363581 prefixEnd_1363581 700172464338534716766511 := by
  unfold tailWord_1363581
  simp only [CollatzResearch.WordTrace]
  refine ⟨49733884872986392939298597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33155923248657595292865731 49733884872986392939298597)
  ·
    refine ⟨9325103413684948676118487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49733884872986392939298597 9325103413684948676118487)
    ·
      refine ⟨13987655120527423014177731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9325103413684948676118487 13987655120527423014177731)
      ·
        refine ⟨20981482680791134521266597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13987655120527423014177731 20981482680791134521266597)
        ·
          refine ⟨3934028002648337722737487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20981482680791134521266597 3934028002648337722737487)
          ·
            refine ⟨5901042003972506584106231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934028002648337722737487 5901042003972506584106231)
            ·
              refine ⟨8851563005958759876159347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901042003972506584106231 8851563005958759876159347)
              ·
                refine ⟨13277344508938139814239021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8851563005958759876159347 13277344508938139814239021)
                ·
                  refine ⟨4979004190851802430339633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13277344508938139814239021 4979004190851802430339633)
                  ·
                    refine ⟨3734253143138851822754725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979004190851802430339633 3734253143138851822754725)
                    ·
                      refine ⟨700172464338534716766511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3734253143138851822754725 700172464338534716766511)
                      ·
                        rfl

theorem cell23_1363581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1363581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363581 prefixEnd_1363581 := by exact prefixLift 1363581
  have htrace : WordTrace (prefixWord ++ tailWord_1363581) baseStart_1363581 baseEnd_1363581 := by
    simpa [prefixWord, tailWord_1363581, baseEnd_1363581] using wordTrace_append hprefix tailTrace_1363581
  have hstable : (prefixWord ++ tailWord_1363581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363581).length < 2 ^ (prefixWord ++ tailWord_1363581).sum := by decide
  have hdescent : baseEnd_1363581 < baseStart_1363581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363585 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_1363585 : Nat := 118140960795 + 1363585 * 2 ^ 59
def prefixEnd_1363585 : Nat := 4983230072969 + 3 ^ 40 * 1363585 * 2
def baseEnd_1363585 : Nat := 700174518261152701116493

theorem tailTrace_1363585 : CollatzResearch.WordTrace tailWord_1363585 prefixEnd_1363585 700174518261152701116493 := by
  unfold tailWord_1363585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49734030764971901622444209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33156020509981267748296139 49734030764971901622444209)
  ·
    refine ⟨37300523073728926216833157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49734030764971901622444209 37300523073728926216833157)
    ·
      refine ⟨6993848076324173665656217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37300523073728926216833157 6993848076324173665656217)
      ·
        refine ⟨5245386057243130249242163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6993848076324173665656217 5245386057243130249242163)
        ·
          refine ⟨7868079085864695373863245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245386057243130249242163 7868079085864695373863245)
          ·
            refine ⟨2950529657199260765198717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7868079085864695373863245 2950529657199260765198717)
            ·
              refine ⟨1106448621449722786949519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2950529657199260765198717 1106448621449722786949519)
              ·
                refine ⟨1659672932174584180424279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106448621449722786949519 1659672932174584180424279)
                ·
                  refine ⟨2489509398261876270636419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659672932174584180424279 2489509398261876270636419)
                  ·
                    refine ⟨3734264097392814405954629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489509398261876270636419 3734264097392814405954629)
                    ·
                      refine ⟨700174518261152701116493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3734264097392814405954629 700174518261152701116493)
                      ·
                        rfl

theorem cell23_1363585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_1363585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363585 prefixEnd_1363585 := by exact prefixLift 1363585
  have htrace : WordTrace (prefixWord ++ tailWord_1363585) baseStart_1363585 baseEnd_1363585 := by
    simpa [prefixWord, tailWord_1363585, baseEnd_1363585] using wordTrace_append hprefix tailTrace_1363585
  have hstable : (prefixWord ++ tailWord_1363585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363585).length < 2 ^ (prefixWord ++ tailWord_1363585).sum := by decide
  have hdescent : baseEnd_1363585 < baseStart_1363585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363615 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1363615 : Nat := 118140960795 + 1363615 * 2 ^ 59
def prefixEnd_1363615 : Nat := 4983230072969 + 3 ^ 40 * 1363615 * 2
def baseEnd_1363615 : Nat := 700189922680787583741355

theorem tailTrace_1363615 : CollatzResearch.WordTrace tailWord_1363615 prefixEnd_1363615 700189922680787583741355 := by
  unfold tailWord_1363615
  simp only [CollatzResearch.WordTrace]
  refine ⟨49735124954863216746036299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33156749969908811164024199 49735124954863216746036299)
  ·
    refine ⟨74602687432294825119054449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49735124954863216746036299 74602687432294825119054449)
    ·
      refine ⟨55952015574221118839290837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74602687432294825119054449 55952015574221118839290837)
      ·
        refine ⟨1311375365020807472795879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 55952015574221118839290837 1311375365020807472795879)
        ·
          refine ⟨1967063047531211209193819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311375365020807472795879 1967063047531211209193819)
          ·
            refine ⟨2950594571296816813790729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967063047531211209193819 2950594571296816813790729)
            ·
              refine ⟨2212945928472612610343047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950594571296816813790729 2212945928472612610343047)
              ·
                refine ⟨3319418892708918915514571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212945928472612610343047 3319418892708918915514571)
                ·
                  refine ⟨4979128339063378373271857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319418892708918915514571 4979128339063378373271857)
                  ·
                    refine ⟨3734346254297533779953893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979128339063378373271857 3734346254297533779953893)
                    ·
                      refine ⟨700189922680787583741355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3734346254297533779953893 700189922680787583741355)
                      ·
                        rfl

theorem cell23_1363615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1363615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363615 prefixEnd_1363615 := by exact prefixLift 1363615
  have htrace : WordTrace (prefixWord ++ tailWord_1363615) baseStart_1363615 baseEnd_1363615 := by
    simpa [prefixWord, tailWord_1363615, baseEnd_1363615] using wordTrace_append hprefix tailTrace_1363615
  have hstable : (prefixWord ++ tailWord_1363615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363615).length < 2 ^ (prefixWord ++ tailWord_1363615).sum := by decide
  have hdescent : baseEnd_1363615 < baseStart_1363615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363645 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_1363645 : Nat := 118140960795 + 1363645 * 2 ^ 59
def prefixEnd_1363645 : Nat := 4983230072969 + 3 ^ 40 * 1363645 * 2
def baseEnd_1363645 : Nat := 700205327100422466366217

theorem tailTrace_1363645 : CollatzResearch.WordTrace tailWord_1363645 prefixEnd_1363645 700205327100422466366217 := by
  unfold tailWord_1363645
  simp only [CollatzResearch.WordTrace]
  refine ⟨49736219144754531869628389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33157479429836354579752259 49736219144754531869628389)
  ·
    refine ⟨9325541089641474725555323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49736219144754531869628389 9325541089641474725555323)
    ·
      refine ⟨13988311634462212088332985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9325541089641474725555323 13988311634462212088332985)
      ·
        refine ⟨10491233725846659066249739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13988311634462212088332985 10491233725846659066249739)
        ·
          refine ⟨15736850588769988599374609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10491233725846659066249739 15736850588769988599374609)
          ·
            refine ⟨11802637941577491449530957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15736850588769988599374609 11802637941577491449530957)
            ·
              refine ⟨4425989228091559293574109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11802637941577491449530957 4425989228091559293574109)
              ·
                refine ⟨1659745960534334735090291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4425989228091559293574109 1659745960534334735090291)
                ·
                  refine ⟨2489618940801502102635437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659745960534334735090291 2489618940801502102635437)
                  ·
                    refine ⟨933607102800563288488289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489618940801502102635437 933607102800563288488289)
                    ·
                      refine ⟨700205327100422466366217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933607102800563288488289 700205327100422466366217)
                      ·
                        rfl

theorem cell23_1363645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_1363645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363645 prefixEnd_1363645 := by exact prefixLift 1363645
  have htrace : WordTrace (prefixWord ++ tailWord_1363645) baseStart_1363645 baseEnd_1363645 := by
    simpa [prefixWord, tailWord_1363645, baseEnd_1363645] using wordTrace_append hprefix tailTrace_1363645
  have hstable : (prefixWord ++ tailWord_1363645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363645).length < 2 ^ (prefixWord ++ tailWord_1363645).sum := by decide
  have hdescent : baseEnd_1363645 < baseStart_1363645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363668 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1363668 : Nat := 118140960795 + 1363668 * 2 ^ 59
def prefixEnd_1363668 : Nat := 4983230072969 + 3 ^ 40 * 1363668 * 2
def baseEnd_1363668 : Nat := 233405712385158625459537

theorem tailTrace_1363668 : CollatzResearch.WordTrace tailWord_1363668 prefixEnd_1363668 233405712385158625459537 := by
  unfold tailWord_1363668
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868529011835603398857829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33158038682447471198477105 24868529011835603398857829)
  ·
    refine ⟨4662849189719175637285843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24868529011835603398857829 4662849189719175637285843)
    ·
      refine ⟨6994273784578763455928765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662849189719175637285843 6994273784578763455928765)
      ·
        refine ⟨2622852669217036295973287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6994273784578763455928765 2622852669217036295973287)
        ·
          refine ⟨3934279003825554443959931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622852669217036295973287 3934279003825554443959931)
          ·
            refine ⟨5901418505738331665939897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934279003825554443959931 5901418505738331665939897)
            ·
              refine ⟨4426063879303748749454923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5901418505738331665939897 4426063879303748749454923)
              ·
                refine ⟨6639095818955623124182385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426063879303748749454923 6639095818955623124182385)
                ·
                  refine ⟨4979321864216717343136789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6639095818955623124182385 4979321864216717343136789)
                  ·
                    refine ⟨233405712385158625459537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4979321864216717343136789 233405712385158625459537)
                    ·
                      rfl

theorem cell23_1363668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1363668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363668 prefixEnd_1363668 := by exact prefixLift 1363668
  have htrace : WordTrace (prefixWord ++ tailWord_1363668) baseStart_1363668 baseEnd_1363668 := by
    simpa [prefixWord, tailWord_1363668, baseEnd_1363668] using wordTrace_append hprefix tailTrace_1363668
  have hstable : (prefixWord ++ tailWord_1363668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363668).length < 2 ^ (prefixWord ++ tailWord_1363668).sum := by decide
  have hdescent : baseEnd_1363668 < baseStart_1363668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363671 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1363671 : Nat := 118140960795 + 1363671 * 2 ^ 59
def prefixEnd_1363671 : Nat := 4983230072969 + 3 ^ 40 * 1363671 * 2
def baseEnd_1363671 : Nat := 700218677597439364641097

theorem tailTrace_1363671 : CollatzResearch.WordTrace tailWord_1363671 prefixEnd_1363671 700218677597439364641097 := by
  unfold tailWord_1363671
  simp only [CollatzResearch.WordTrace]
  refine ⟨49737167442660338310074867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33158111628440225540049911 49737167442660338310074867)
  ·
    refine ⟨74605751163990507465112301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49737167442660338310074867 74605751163990507465112301)
    ·
      refine ⟨27977156686496440299417113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74605751163990507465112301 27977156686496440299417113)
      ·
        refine ⟨20982867514872330224562835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27977156686496440299417113 20982867514872330224562835)
        ·
          refine ⟨31474301272308495336844253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20982867514872330224562835 31474301272308495336844253)
          ·
            refine ⟨11802862977115685751316595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31474301272308495336844253 11802862977115685751316595)
            ·
              refine ⟨17704294465673528626974893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11802862977115685751316595 17704294465673528626974893)
              ·
                refine ⟨6639110424627573235115585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17704294465673528626974893 6639110424627573235115585)
                ·
                  refine ⟨4979332818470679926336689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6639110424627573235115585 4979332818470679926336689)
                  ·
                    refine ⟨3734499613853009944752517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4979332818470679926336689 3734499613853009944752517)
                    ·
                      refine ⟨700218677597439364641097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3734499613853009944752517 700218677597439364641097)
                      ·
                        rfl

theorem cell23_1363671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1363671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363671 prefixEnd_1363671 := by exact prefixLift 1363671
  have htrace : WordTrace (prefixWord ++ tailWord_1363671) baseStart_1363671 baseEnd_1363671 := by
    simpa [prefixWord, tailWord_1363671, baseEnd_1363671] using wordTrace_append hprefix tailTrace_1363671
  have hstable : (prefixWord ++ tailWord_1363671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363671).length < 2 ^ (prefixWord ++ tailWord_1363671).sum := by decide
  have hdescent : baseEnd_1363671 < baseStart_1363671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363691 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3]
def baseStart_1363691 : Nat := 118140960795 + 1363691 * 2 ^ 59
def prefixEnd_1363691 : Nat := 4983230072969 + 3 ^ 40 * 1363691 * 2
def baseEnd_1363691 : Nat := 700228947210529286391005

theorem tailTrace_1363691 : CollatzResearch.WordTrace tailWord_1363691 prefixEnd_1363691 700228947210529286391005 := by
  unfold tailWord_1363691
  simp only [CollatzResearch.WordTrace]
  refine ⟨49737896902587881725802927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33158597935058587817201951 49737896902587881725802927)
  ·
    refine ⟨74606845353881822588704391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49737896902587881725802927 74606845353881822588704391)
    ·
      refine ⟨111910268030822733883056587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74606845353881822588704391 111910268030822733883056587)
      ·
        refine ⟨167865402046234100824584881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111910268030822733883056587 167865402046234100824584881)
        ·
          refine ⟨125899051534675575618438661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167865402046234100824584881 125899051534675575618438661)
          ·
            refine ⟨23606072162751670428457249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125899051534675575618438661 23606072162751670428457249)
            ·
              refine ⟨17704554122063752821342937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23606072162751670428457249 17704554122063752821342937)
              ·
                refine ⟨13278415591547814616007203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17704554122063752821342937 13278415591547814616007203)
                ·
                  refine ⟨19917623387321721924010805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13278415591547814616007203 19917623387321721924010805)
                  ·
                    refine ⟨1867277192561411430376013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19917623387321721924010805 1867277192561411430376013)
                    ·
                      refine ⟨700228947210529286391005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1867277192561411430376013 700228947210529286391005)
                      ·
                        rfl

theorem cell23_1363691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 3].length) (baseStart_1363691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363691 prefixEnd_1363691 := by exact prefixLift 1363691
  have htrace : WordTrace (prefixWord ++ tailWord_1363691) baseStart_1363691 baseEnd_1363691 := by
    simpa [prefixWord, tailWord_1363691, baseEnd_1363691] using wordTrace_append hprefix tailTrace_1363691
  have hstable : (prefixWord ++ tailWord_1363691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363691).length < 2 ^ (prefixWord ++ tailWord_1363691).sum := by decide
  have hdescent : baseEnd_1363691 < baseStart_1363691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363711 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 4, 5]
def baseStart_1363711 : Nat := 118140960795 + 1363711 * 2 ^ 59
def prefixEnd_1363711 : Nat := 4983230072969 + 3 ^ 40 * 1363711 * 2
def baseEnd_1363711 : Nat := 233413072274539736046971

theorem tailTrace_1363711 : CollatzResearch.WordTrace tailWord_1363711 prefixEnd_1363711 233413072274539736046971 := by
  unfold tailWord_1363711
  simp only [CollatzResearch.WordTrace]
  refine ⟨49738626362515425141530987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33159084241676950094353991 49738626362515425141530987)
  ·
    refine ⟨74607939543773137712296481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49738626362515425141530987 74607939543773137712296481)
    ·
      refine ⟨55955954657829853284222361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74607939543773137712296481 55955954657829853284222361)
      ·
        refine ⟨41966965993372389963166771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55955954657829853284222361 41966965993372389963166771)
        ·
          refine ⟨62950448990058584944750157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41966965993372389963166771 62950448990058584944750157)
          ·
            refine ⟨23606418371271969354281309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62950448990058584944750157 23606418371271969354281309)
            ·
              refine ⟨8852406889226988507855491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23606418371271969354281309 8852406889226988507855491)
              ·
                refine ⟨13278610333840482761783237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852406889226988507855491 13278610333840482761783237)
                ·
                  refine ⟨2489739437595090517834357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13278610333840482761783237 2489739437595090517834357)
                  ·
                    refine ⟨233413072274539736046971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2489739437595090517834357 233413072274539736046971)
                    ·
                      rfl

theorem cell23_1363711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_1363711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363711 prefixEnd_1363711 := by exact prefixLift 1363711
  have htrace : WordTrace (prefixWord ++ tailWord_1363711) baseStart_1363711 baseEnd_1363711 := by
    simpa [prefixWord, tailWord_1363711, baseEnd_1363711] using wordTrace_append hprefix tailTrace_1363711
  have hstable : (prefixWord ++ tailWord_1363711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363711).length < 2 ^ (prefixWord ++ tailWord_1363711).sum := by decide
  have hdescent : baseEnd_1363711 < baseStart_1363711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363731 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_1363731 : Nat := 118140960795 + 1363731 * 2 ^ 59
def prefixEnd_1363731 : Nat := 4983230072969 + 3 ^ 40 * 1363731 * 2
def baseEnd_1363731 : Nat := 700249486436709129890821

theorem tailTrace_1363731 : CollatzResearch.WordTrace tailWord_1363731 prefixEnd_1363731 700249486436709129890821 := by
  unfold tailWord_1363731
  simp only [CollatzResearch.WordTrace]
  refine ⟨49739355822442968557259047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33159570548295312371506031 49739355822442968557259047)
  ·
    refine ⟨74609033733664452835888571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49739355822442968557259047 74609033733664452835888571)
    ·
      refine ⟨111913550600496679253832857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74609033733664452835888571 111913550600496679253832857)
      ·
        refine ⟨83935162950372509440374643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111913550600496679253832857 83935162950372509440374643)
        ·
          refine ⟨125902744425558764160561965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83935162950372509440374643 125902744425558764160561965)
          ·
            refine ⟨47213529159584536560210737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125902744425558764160561965 47213529159584536560210737)
            ·
              refine ⟨35410146869688402420158053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47213529159584536560210737 35410146869688402420158053)
              ·
                refine ⟨6639402538066575453779635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35410146869688402420158053 6639402538066575453779635)
                ·
                  refine ⟨9959103807099863180669453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639402538066575453779635 9959103807099863180669453)
                  ·
                    refine ⟨3734663927662448692751045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9959103807099863180669453 3734663927662448692751045)
                    ·
                      refine ⟨700249486436709129890821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3734663927662448692751045 700249486436709129890821)
                      ·
                        rfl

theorem cell23_1363731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_1363731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363731 prefixEnd_1363731 := by exact prefixLift 1363731
  have htrace : WordTrace (prefixWord ++ tailWord_1363731) baseStart_1363731 baseEnd_1363731 := by
    simpa [prefixWord, tailWord_1363731, baseEnd_1363731] using wordTrace_append hprefix tailTrace_1363731
  have hstable : (prefixWord ++ tailWord_1363731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363731).length < 2 ^ (prefixWord ++ tailWord_1363731).sum := by decide
  have hdescent : baseEnd_1363731 < baseStart_1363731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363815 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1363815 : Nat := 118140960795 + 1363815 * 2 ^ 59
def prefixEnd_1363815 : Nat := 4983230072969 + 3 ^ 40 * 1363815 * 2
def baseEnd_1363815 : Nat := 700292618811686801240435

theorem tailTrace_1363815 : CollatzResearch.WordTrace tailWord_1363815 prefixEnd_1363815 700292618811686801240435 := by
  unfold tailWord_1363815
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742419554138650903316899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33161613036092433935544599 49742419554138650903316899)
  ·
    refine ⟨74613629331207976354975349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49742419554138650903316899 74613629331207976354975349)
    ·
      refine ⟨6995027749800747783278939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74613629331207976354975349 6995027749800747783278939)
      ·
        refine ⟨10492541624701121674918409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995027749800747783278939 10492541624701121674918409)
        ·
          refine ⟨7869406218525841256188807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10492541624701121674918409 7869406218525841256188807)
          ·
            refine ⟨11804109327788761884283211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869406218525841256188807 11804109327788761884283211)
            ·
              refine ⟨17706163991683142826424817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11804109327788761884283211 17706163991683142826424817)
              ·
                refine ⟨13279622993762357119818613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17706163991683142826424817 13279622993762357119818613)
                ·
                  refine ⟨1244964655665220979982995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13279622993762357119818613 1244964655665220979982995)
                  ·
                    refine ⟨1867446983497831469974493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1244964655665220979982995 1867446983497831469974493)
                    ·
                      refine ⟨700292618811686801240435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1867446983497831469974493 700292618811686801240435)
                      ·
                        rfl

theorem cell23_1363815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1363815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363815 prefixEnd_1363815 := by exact prefixLift 1363815
  have htrace : WordTrace (prefixWord ++ tailWord_1363815) baseStart_1363815 baseEnd_1363815 := by
    simpa [prefixWord, tailWord_1363815, baseEnd_1363815] using wordTrace_append hprefix tailTrace_1363815
  have hstable : (prefixWord ++ tailWord_1363815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363815).length < 2 ^ (prefixWord ++ tailWord_1363815).sum := by decide
  have hdescent : baseEnd_1363815 < baseStart_1363815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363822 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_1363822 : Nat := 118140960795 + 1363822 * 2 ^ 59
def prefixEnd_1363822 : Nat := 4983230072969 + 3 ^ 40 * 1363822 * 2
def baseEnd_1363822 : Nat := 77810690352918697094767

theorem tailTrace_1363822 : CollatzResearch.WordTrace tailWord_1363822 prefixEnd_1363822 77810690352918697094767 := by
  unfold tailWord_1363822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217834358139161387352715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33161783243408860732547813 6217834358139161387352715)
  ·
    refine ⟨9326751537208742081029073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6217834358139161387352715 9326751537208742081029073)
    ·
      refine ⟨6995063652906556560771805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9326751537208742081029073 6995063652906556560771805)
      ·
        refine ⟨2623148869839958710289427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6995063652906556560771805 2623148869839958710289427)
        ·
          refine ⟨3934723304759938065434141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623148869839958710289427 3934723304759938065434141)
          ·
            refine ⟨1475521239284976774537803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3934723304759938065434141 1475521239284976774537803)
            ·
              refine ⟨2213281858927465161806705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475521239284976774537803 2213281858927465161806705)
              ·
                refine ⟨1659961394195598871355029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213281858927465161806705 1659961394195598871355029)
                ·
                  refine ⟨77810690352918697094767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1659961394195598871355029 77810690352918697094767)
                  ·
                    rfl

theorem cell23_1363822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_1363822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363822 prefixEnd_1363822 := by exact prefixLift 1363822
  have htrace : WordTrace (prefixWord ++ tailWord_1363822) baseStart_1363822 baseEnd_1363822 := by
    simpa [prefixWord, tailWord_1363822, baseEnd_1363822] using wordTrace_append hprefix tailTrace_1363822
  have hstable : (prefixWord ++ tailWord_1363822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363822).length < 2 ^ (prefixWord ++ tailWord_1363822).sum := by decide
  have hdescent : baseEnd_1363822 < baseStart_1363822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363825 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_1363825 : Nat := 118140960795 + 1363825 * 2 ^ 59
def prefixEnd_1363825 : Nat := 4983230072969 + 3 ^ 40 * 1363825 * 2
def baseEnd_1363825 : Nat := 700297753618231762115389

theorem tailTrace_1363825 : CollatzResearch.WordTrace tailWord_1363825 prefixEnd_1363825 700297753618231762115389 := by
  unfold tailWord_1363825
  simp only [CollatzResearch.WordTrace]
  refine ⟨49742784284102422611180929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33161856189401615074120619 49742784284102422611180929)
  ·
    refine ⟨37307088213076816958385697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49742784284102422611180929 37307088213076816958385697)
    ·
      refine ⟨27980316159807612718789273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37307088213076816958385697 27980316159807612718789273)
      ·
        refine ⟨20985237119855709539091955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27980316159807612718789273 20985237119855709539091955)
        ·
          refine ⟨31477855679783564308637933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20985237119855709539091955 31477855679783564308637933)
          ·
            refine ⟨11804195879918836615739225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31477855679783564308637933 11804195879918836615739225)
            ·
              refine ⟨8853146909939127461804419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11804195879918836615739225 8853146909939127461804419)
              ·
                refine ⟨13279720364908691192706629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8853146909939127461804419 13279720364908691192706629)
                ·
                  refine ⟨2489947568420379598632493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13279720364908691192706629 2489947568420379598632493)
                  ·
                    refine ⟨933730338157642349487185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2489947568420379598632493 933730338157642349487185)
                    ·
                      refine ⟨700297753618231762115389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933730338157642349487185 700297753618231762115389)
                      ·
                        rfl

theorem cell23_1363825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_1363825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363825 prefixEnd_1363825 := by exact prefixLift 1363825
  have htrace : WordTrace (prefixWord ++ tailWord_1363825) baseStart_1363825 baseEnd_1363825 := by
    simpa [prefixWord, tailWord_1363825, baseEnd_1363825] using wordTrace_append hprefix tailTrace_1363825
  have hstable : (prefixWord ++ tailWord_1363825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363825).length < 2 ^ (prefixWord ++ tailWord_1363825).sum := by decide
  have hdescent : baseEnd_1363825 < baseStart_1363825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363831 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 10]
def baseStart_1363831 : Nat := 118140960795 + 1363831 * 2 ^ 59
def prefixEnd_1363831 : Nat := 4983230072969 + 3 ^ 40 * 1363831 * 2
def baseEnd_1363831 : Nat := 233433611500719579546787

theorem tailTrace_1363831 : CollatzResearch.WordTrace tailWord_1363831 prefixEnd_1363831 233433611500719579546787 := by
  unfold tailWord_1363831
  simp only [CollatzResearch.WordTrace]
  refine ⟨49743003122080685635899347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33162002081387123757266231 49743003122080685635899347)
  ·
    refine ⟨74614504683121028453849021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49743003122080685635899347 74614504683121028453849021)
    ·
      refine ⟨27980439256170385670193383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74614504683121028453849021 27980439256170385670193383)
      ·
        refine ⟨41970658884255578505290075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27980439256170385670193383 41970658884255578505290075)
        ·
          refine ⟨62955988326383367757935113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41970658884255578505290075 62955988326383367757935113)
          ·
            refine ⟨47216991244787525818451335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62955988326383367757935113 47216991244787525818451335)
            ·
              refine ⟨70825486867181288727677003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47216991244787525818451335 70825486867181288727677003)
              ·
                refine ⟨106238230300771933091515505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70825486867181288727677003 106238230300771933091515505)
                ·
                  refine ⟨79678672725578949818636629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106238230300771933091515505 79678672725578949818636629)
                  ·
                    refine ⟨233433611500719579546787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 79678672725578949818636629 233433611500719579546787)
                    ·
                      rfl

theorem cell23_1363831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_1363831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363831 prefixEnd_1363831 := by exact prefixLift 1363831
  have htrace : WordTrace (prefixWord ++ tailWord_1363831) baseStart_1363831 baseEnd_1363831 := by
    simpa [prefixWord, tailWord_1363831, baseEnd_1363831] using wordTrace_append hprefix tailTrace_1363831
  have hstable : (prefixWord ++ tailWord_1363831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363831).length < 2 ^ (prefixWord ++ tailWord_1363831).sum := by decide
  have hdescent : baseEnd_1363831 < baseStart_1363831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363866 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1363866 : Nat := 118140960795 + 1363866 * 2 ^ 59
def prefixEnd_1363866 : Nat := 4983230072969 + 3 ^ 40 * 1363866 * 2
def baseEnd_1363866 : Nat := 700318806325066101702701

theorem tailTrace_1363866 : CollatzResearch.WordTrace tailWord_1363866 prefixEnd_1363866 700318806325066101702701 := by
  unfold tailWord_1363866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436069919238471653355863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33162853117969257742282301 12436069919238471653355863)
  ·
    refine ⟨18654104878857707480033795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12436069919238471653355863 18654104878857707480033795)
    ·
      refine ⟨27981157318286561220050693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18654104878857707480033795 27981157318286561220050693)
      ·
        refine ⟨5246466997178730228759505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27981157318286561220050693 5246466997178730228759505)
        ·
          refine ⟨3934850247884047671569629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5246466997178730228759505 3934850247884047671569629)
          ·
            refine ⟨1475568842956517876838611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3934850247884047671569629 1475568842956517876838611)
            ·
              refine ⟨2213353264434776815257917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475568842956517876838611 2213353264434776815257917)
              ·
                refine ⟨830007474163041305721719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2213353264434776815257917 830007474163041305721719)
                ·
                  refine ⟨1245011211244561958582579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830007474163041305721719 1245011211244561958582579)
                  ·
                    refine ⟨1867516816866842937873869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1245011211244561958582579 1867516816866842937873869)
                    ·
                      refine ⟨700318806325066101702701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1867516816866842937873869 700318806325066101702701)
                      ·
                        rfl

theorem cell23_1363866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1363866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363866 prefixEnd_1363866 := by exact prefixLift 1363866
  have htrace : WordTrace (prefixWord ++ tailWord_1363866) baseStart_1363866 baseEnd_1363866 := by
    simpa [prefixWord, tailWord_1363866, baseEnd_1363866] using wordTrace_append hprefix tailTrace_1363866
  have hstable : (prefixWord ++ tailWord_1363866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363866).length < 2 ^ (prefixWord ++ tailWord_1363866).sum := by decide
  have hdescent : baseEnd_1363866 < baseStart_1363866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363889 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1363889 : Nat := 118140960795 + 1363889 * 2 ^ 59
def prefixEnd_1363889 : Nat := 4983230072969 + 3 ^ 40 * 1363889 * 2
def baseEnd_1363889 : Nat := 700330616380119511715095

theorem tailTrace_1363889 : CollatzResearch.WordTrace tailWord_1363889 prefixEnd_1363889 700330616380119511715095 := by
  unfold tailWord_1363889
  simp only [CollatzResearch.WordTrace]
  refine ⟨49745118555870561541510721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33163412370580374361007147 49745118555870561541510721)
  ·
    refine ⟨37308838916902921156133041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49745118555870561541510721 37308838916902921156133041)
    ·
      refine ⟨27981629187677190867099781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37308838916902921156133041 27981629187677190867099781)
      ·
        refine ⟨5246555472689473287581209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27981629187677190867099781 5246555472689473287581209)
        ·
          refine ⟨3934916604517104965685907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5246555472689473287581209 3934916604517104965685907)
          ·
            refine ⟨5902374906775657448528861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934916604517104965685907 5902374906775657448528861)
            ·
              refine ⟨2213390590040871543198323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5902374906775657448528861 2213390590040871543198323)
              ·
                refine ⟨3320085885061307314797485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213390590040871543198323 3320085885061307314797485)
                ·
                  refine ⟨1245032206897990243049057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3320085885061307314797485 1245032206897990243049057)
                  ·
                    refine ⟨933774155173492682286793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245032206897990243049057 933774155173492682286793)
                    ·
                      refine ⟨700330616380119511715095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933774155173492682286793 700330616380119511715095)
                      ·
                        rfl

theorem cell23_1363889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1363889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363889 prefixEnd_1363889 := by exact prefixLift 1363889
  have htrace : WordTrace (prefixWord ++ tailWord_1363889) baseStart_1363889 baseEnd_1363889 := by
    simpa [prefixWord, tailWord_1363889, baseEnd_1363889] using wordTrace_append hprefix tailTrace_1363889
  have hstable : (prefixWord ++ tailWord_1363889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363889).length < 2 ^ (prefixWord ++ tailWord_1363889).sum := by decide
  have hdescent : baseEnd_1363889 < baseStart_1363889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363926 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1363926 : Nat := 118140960795 + 1363926 * 2 ^ 59
def prefixEnd_1363926 : Nat := 4983230072969 + 3 ^ 40 * 1363926 * 2
def baseEnd_1363926 : Nat := 700349615164335866952425

theorem tailTrace_1363926 : CollatzResearch.WordTrace tailWord_1363926 prefixEnd_1363926 700349615164335866952425 := by
  unfold tailWord_1363926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109154253546032303787977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33164312037824344573738421 3109154253546032303787977)
  ·
    refine ⟨2331865690159524227840983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3109154253546032303787977 2331865690159524227840983)
    ·
      refine ⟨3497798535239286341761475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331865690159524227840983 3497798535239286341761475)
      ·
        refine ⟨5246697802858929512642213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497798535239286341761475 5246697802858929512642213)
        ·
          refine ⟨983755838036049283620415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5246697802858929512642213 983755838036049283620415)
          ·
            refine ⟨1475633757054073925430623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983755838036049283620415 1475633757054073925430623)
            ·
              refine ⟨2213450635581110888145935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475633757054073925430623 2213450635581110888145935)
              ·
                refine ⟨3320175953371666332218903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213450635581110888145935 3320175953371666332218903)
                ·
                  refine ⟨4980263930057499498328355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320175953371666332218903 4980263930057499498328355)
                  ·
                    refine ⟨7470395895086249247492533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4980263930057499498328355 7470395895086249247492533)
                    ·
                      refine ⟨700349615164335866952425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7470395895086249247492533 700349615164335866952425)
                      ·
                        rfl

theorem cell23_1363926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1363926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363926 prefixEnd_1363926 := by exact prefixLift 1363926
  have htrace : WordTrace (prefixWord ++ tailWord_1363926) baseStart_1363926 baseEnd_1363926 := by
    simpa [prefixWord, tailWord_1363926, baseEnd_1363926] using wordTrace_append hprefix tailTrace_1363926
  have hstable : (prefixWord ++ tailWord_1363926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363926).length < 2 ^ (prefixWord ++ tailWord_1363926).sum := by decide
  have hdescent : baseEnd_1363926 < baseStart_1363926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363939 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1363939 : Nat := 118140960795 + 1363939 * 2 ^ 59
def prefixEnd_1363939 : Nat := 4983230072969 + 3 ^ 40 * 1363939 * 2
def baseEnd_1363939 : Nat := 700356290412844316089865

theorem tailTrace_1363939 : CollatzResearch.WordTrace tailWord_1363939 prefixEnd_1363939 700356290412844316089865 := by
  unfold tailWord_1363939
  simp only [CollatzResearch.WordTrace]
  refine ⟨49746942205689420080830871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33164628137126280053887247 49746942205689420080830871)
  ·
    refine ⟨74620413308534130121246307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49746942205689420080830871 74620413308534130121246307)
    ·
      refine ⟨111930619962801195181869461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74620413308534130121246307 111930619962801195181869461)
      ·
        refine ⟨5246747810756306024150131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111930619962801195181869461 5246747810756306024150131)
        ·
          refine ⟨7870121716134459036225197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246747810756306024150131 7870121716134459036225197)
          ·
            refine ⟨2951295643550422138584449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7870121716134459036225197 2951295643550422138584449)
            ·
              refine ⟨2213471732662816603938337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951295643550422138584449 2213471732662816603938337)
              ·
                refine ⟨1660103799497112452953753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213471732662816603938337 1660103799497112452953753)
                ·
                  refine ⟨1245077849622834339715315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1660103799497112452953753 1245077849622834339715315)
                  ·
                    refine ⟨1867616774434251509572973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1245077849622834339715315 1867616774434251509572973)
                    ·
                      refine ⟨700356290412844316089865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1867616774434251509572973 700356290412844316089865)
                      ·
                        rfl

theorem cell23_1363939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1363939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363939 prefixEnd_1363939 := by exact prefixLift 1363939
  have htrace : WordTrace (prefixWord ++ tailWord_1363939) baseStart_1363939 baseEnd_1363939 := by
    simpa [prefixWord, tailWord_1363939, baseEnd_1363939] using wordTrace_append hprefix tailTrace_1363939
  have hstable : (prefixWord ++ tailWord_1363939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363939).length < 2 ^ (prefixWord ++ tailWord_1363939).sum := by decide
  have hdescent : baseEnd_1363939 < baseStart_1363939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363948 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1363948 : Nat := 118140960795 + 1363948 * 2 ^ 59
def prefixEnd_1363948 : Nat := 4983230072969 + 3 ^ 40 * 1363948 * 2
def baseEnd_1363948 : Nat := 700360911738734780877323

theorem tailTrace_1363948 : CollatzResearch.WordTrace tailWord_1363948 prefixEnd_1363948 700360911738734780877323 := by
  unfold tailWord_1363948
  simp only [CollatzResearch.WordTrace]
  refine ⟨24873635231328407308954249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33164846975104543078605665 24873635231328407308954249)
  ·
    refine ⟨18655226423496305481715687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24873635231328407308954249 18655226423496305481715687)
    ·
      refine ⟨27982839635244458222573531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18655226423496305481715687 27982839635244458222573531)
      ·
        refine ⟨41974259452866687333860297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27982839635244458222573531 41974259452866687333860297)
        ·
          refine ⟨31480694589650015500395223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41974259452866687333860297 31480694589650015500395223)
          ·
            refine ⟨47221041884475023250592835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31480694589650015500395223 47221041884475023250592835)
            ·
              refine ⟨70831562826712534875889253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47221041884475023250592835 70831562826712534875889253)
              ·
                refine ⟨13280918030008600289229235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70831562826712534875889253 13280918030008600289229235)
                ·
                  refine ⟨19921377045012900433843853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13280918030008600289229235 19921377045012900433843853)
                  ·
                    refine ⟨7470516391879837662691445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19921377045012900433843853 7470516391879837662691445)
                    ·
                      refine ⟨700360911738734780877323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7470516391879837662691445 700360911738734780877323)
                      ·
                        rfl

theorem cell23_1363948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1363948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363948 prefixEnd_1363948 := by exact prefixLift 1363948
  have htrace : WordTrace (prefixWord ++ tailWord_1363948) baseStart_1363948 baseEnd_1363948 := by
    simpa [prefixWord, tailWord_1363948, baseEnd_1363948] using wordTrace_append hprefix tailTrace_1363948
  have hstable : (prefixWord ++ tailWord_1363948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363948).length < 2 ^ (prefixWord ++ tailWord_1363948).sum := by decide
  have hdescent : baseEnd_1363948 < baseStart_1363948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363962 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_1363962 : Nat := 118140960795 + 1363962 * 2 ^ 59
def prefixEnd_1363962 : Nat := 4983230072969 + 3 ^ 40 * 1363962 * 2
def baseEnd_1363962 : Nat := 700368100467897726102259

theorem tailTrace_1363962 : CollatzResearch.WordTrace tailWord_1363962 prefixEnd_1363962 700368100467897726102259 := by
  unfold tailWord_1363962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436945271151523752229535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33165187389737396672612093 12436945271151523752229535)
  ·
    refine ⟨18655417906727285628344303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12436945271151523752229535 18655417906727285628344303)
    ·
      refine ⟨27983126860090928442516455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18655417906727285628344303 27983126860090928442516455)
      ·
        refine ⟨41974690290136392663774683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27983126860090928442516455 41974690290136392663774683)
        ·
          refine ⟨62962035435204588995662025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41974690290136392663774683 62962035435204588995662025)
          ·
            refine ⟨47221526576403441746746519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62962035435204588995662025 47221526576403441746746519)
            ·
              refine ⟨70832289864605162620119779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47221526576403441746746519 70832289864605162620119779)
              ·
                refine ⟨106248434796907743930179669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70832289864605162620119779 106248434796907743930179669)
                ·
                  refine ⟨1245098845276262624181793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 106248434796907743930179669 1245098845276262624181793)
                  ·
                    refine ⟨933824133957196968136345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245098845276262624181793 933824133957196968136345)
                    ·
                      refine ⟨700368100467897726102259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933824133957196968136345 700368100467897726102259)
                      ·
                        rfl

theorem cell23_1363962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_1363962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363962 prefixEnd_1363962 := by exact prefixLift 1363962
  have htrace : WordTrace (prefixWord ++ tailWord_1363962) baseStart_1363962 baseEnd_1363962 := by
    simpa [prefixWord, tailWord_1363962, baseEnd_1363962] using wordTrace_append hprefix tailTrace_1363962
  have hstable : (prefixWord ++ tailWord_1363962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363962).length < 2 ^ (prefixWord ++ tailWord_1363962).sum := by decide
  have hdescent : baseEnd_1363962 < baseStart_1363962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363974 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1363974 : Nat := 118140960795 + 1363974 * 2 ^ 59
def prefixEnd_1363974 : Nat := 4983230072969 + 3 ^ 40 * 1363974 * 2
def baseEnd_1363974 : Nat := 700374262235751679152205

theorem tailTrace_1363974 : CollatzResearch.WordTrace tailWord_1363974 prefixEnd_1363974 700374262235751679152205 := by
  unfold tailWord_1363974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554631836267581908073593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33165479173708414038903317 1554631836267581908073593)
  ·
    refine ⟨1165973877200686431055195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1554631836267581908073593 1165973877200686431055195)
    ·
      refine ⟨1748960815801029646582793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165973877200686431055195 1748960815801029646582793)
      ·
        refine ⟨1311720611850772234937095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1748960815801029646582793 1311720611850772234937095)
        ·
          refine ⟨1967580917776158352405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311720611850772234937095 1967580917776158352405643)
          ·
            refine ⟨2951371376664237528608465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967580917776158352405643 2951371376664237528608465)
            ·
              refine ⟨2213528532498178146456349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951371376664237528608465 2213528532498178146456349)
              ·
                refine ⟨830073199686816804921131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2213528532498178146456349 830073199686816804921131)
                ·
                  refine ⟨1245109799530225207381697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830073199686816804921131 1245109799530225207381697)
                  ·
                    refine ⟨933832349647668905536273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245109799530225207381697 933832349647668905536273)
                    ·
                      refine ⟨700374262235751679152205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933832349647668905536273 700374262235751679152205)
                      ·
                        rfl

theorem cell23_1363974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1363974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363974 prefixEnd_1363974 := by exact prefixLift 1363974
  have htrace : WordTrace (prefixWord ++ tailWord_1363974) baseStart_1363974 baseEnd_1363974 := by
    simpa [prefixWord, tailWord_1363974, baseEnd_1363974] using wordTrace_append hprefix tailTrace_1363974
  have hstable : (prefixWord ++ tailWord_1363974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363974).length < 2 ^ (prefixWord ++ tailWord_1363974).sum := by decide
  have hdescent : baseEnd_1363974 < baseStart_1363974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363996 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1363996 : Nat := 118140960795 + 1363996 * 2 ^ 59
def prefixEnd_1363996 : Nat := 4983230072969 + 3 ^ 40 * 1363996 * 2
def baseEnd_1363996 : Nat := 700385558810150593077103

theorem tailTrace_1363996 : CollatzResearch.WordTrace tailWord_1363996 prefixEnd_1363996 700385558810150593077103 := by
  unfold tailWord_1363996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24874510583241459407827921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33166014110988612543770561 24874510583241459407827921)
  ·
    refine ⟨18655882937431094555870941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24874510583241459407827921 18655882937431094555870941)
    ·
      refine ⟨6995956101536660458451603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18655882937431094555870941 6995956101536660458451603)
      ·
        refine ⟨10493934152304990687677405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995956101536660458451603 10493934152304990687677405)
        ·
          refine ⟨3935225307114371507879027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10493934152304990687677405 3935225307114371507879027)
          ·
            refine ⟨5902837960671557261818541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935225307114371507879027 5902837960671557261818541)
            ·
              refine ⟨2213564235251833973181953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5902837960671557261818541 2213564235251833973181953)
              ·
                refine ⟨1660173176438875479886465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213564235251833973181953 1660173176438875479886465)
                ·
                  refine ⟨1245129882329156609914849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1660173176438875479886465 1245129882329156609914849)
                  ·
                    refine ⟨933847411746867457436137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245129882329156609914849 933847411746867457436137)
                    ·
                      refine ⟨700385558810150593077103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933847411746867457436137 700385558810150593077103)
                      ·
                        rfl

theorem cell23_1363996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1363996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1363996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1363996 prefixEnd_1363996 := by exact prefixLift 1363996
  have htrace : WordTrace (prefixWord ++ tailWord_1363996) baseStart_1363996 baseEnd_1363996 := by
    simpa [prefixWord, tailWord_1363996, baseEnd_1363996] using wordTrace_append hprefix tailTrace_1363996
  have hstable : (prefixWord ++ tailWord_1363996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363996).length < 2 ^ (prefixWord ++ tailWord_1363996).sum := by decide
  have hdescent : baseEnd_1363996 < baseStart_1363996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364002 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1364002 : Nat := 118140960795 + 1364002 * 2 ^ 59
def prefixEnd_1364002 : Nat := 4983230072969 + 3 ^ 40 * 1364002 * 2
def baseEnd_1364002 : Nat := 77820959966008618844675

theorem tailTrace_1364002 : CollatzResearch.WordTrace tailWord_1364002 prefixEnd_1364002 77820959966008618844675 := by
  unfold tailWord_1364002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12437310001115295460093565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33166160002974121226916173 12437310001115295460093565)
  ·
    refine ⟨4663991250418235797535087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12437310001115295460093565 4663991250418235797535087)
    ·
      refine ⟨6995986875627353696302631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663991250418235797535087 6995986875627353696302631)
      ·
        refine ⟨10493980313441030544453947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995986875627353696302631 10493980313441030544453947)
        ·
          refine ⟨15740970470161545816680921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10493980313441030544453947 15740970470161545816680921)
          ·
            refine ⟨11805727852621159362510691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15740970470161545816680921 11805727852621159362510691)
            ·
              refine ⟨17708591778931739043766037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11805727852621159362510691 17708591778931739043766037)
              ·
                refine ⟨830090239637425267676533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17708591778931739043766037 830090239637425267676533)
                ·
                  refine ⟨77820959966008618844675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830090239637425267676533 77820959966008618844675)
                  ·
                    rfl

theorem cell23_1364002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1364002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364002 prefixEnd_1364002 := by exact prefixLift 1364002
  have htrace : WordTrace (prefixWord ++ tailWord_1364002) baseStart_1364002 baseEnd_1364002 := by
    simpa [prefixWord, tailWord_1364002, baseEnd_1364002] using wordTrace_append hprefix tailTrace_1364002
  have hstable : (prefixWord ++ tailWord_1364002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364002).length < 2 ^ (prefixWord ++ tailWord_1364002).sum := by decide
  have hdescent : baseEnd_1364002 < baseStart_1364002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364089 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1364089 : Nat := 118140960795 + 1364089 * 2 ^ 59
def prefixEnd_1364089 : Nat := 4983230072969 + 3 ^ 40 * 1364089 * 2
def baseEnd_1364089 : Nat := 700433312511018729214175

theorem tailTrace_1364089 : CollatzResearch.WordTrace tailWord_1364089 prefixEnd_1364089 700433312511018729214175 := by
  unfold tailWord_1364089
  simp only [CollatzResearch.WordTrace]
  refine ⟨49752413155145995698791321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33168275436763997132527547 49752413155145995698791321)
  ·
    refine ⟨37314309866359496774093491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49752413155145995698791321 37314309866359496774093491)
    ·
      refine ⟨55971464799539245161140237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37314309866359496774093491 55971464799539245161140237)
      ·
        refine ⟨20989299299827216935427589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55971464799539245161140237 20989299299827216935427589)
        ·
          refine ⟨3935493618717603175392673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20989299299827216935427589 3935493618717603175392673)
          ·
            refine ⟨2951620214038202381544505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3935493618717603175392673 2951620214038202381544505)
            ·
              refine ⟨2213715160528651786158379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951620214038202381544505 2213715160528651786158379)
              ·
                refine ⟨3320572740792977679237569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213715160528651786158379 3320572740792977679237569)
                ·
                  refine ⟨2490429555594733259428177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320572740792977679237569 2490429555594733259428177)
                  ·
                    refine ⟨1867822166696049944571133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490429555594733259428177 1867822166696049944571133)
                    ·
                      refine ⟨700433312511018729214175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1867822166696049944571133 700433312511018729214175)
                      ·
                        rfl

theorem cell23_1364089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1364089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364089 prefixEnd_1364089 := by exact prefixLift 1364089
  have htrace : WordTrace (prefixWord ++ tailWord_1364089) baseStart_1364089 baseEnd_1364089 := by
    simpa [prefixWord, tailWord_1364089, baseEnd_1364089] using wordTrace_append hprefix tailTrace_1364089
  have hstable : (prefixWord ++ tailWord_1364089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364089).length < 2 ^ (prefixWord ++ tailWord_1364089).sum := by decide
  have hdescent : baseEnd_1364089 < baseStart_1364089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364152 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_1364152 : Nat := 118140960795 + 1364152 * 2 ^ 59
def prefixEnd_1364152 : Nat := 4983230072969 + 3 ^ 40 * 1364152 * 2
def baseEnd_1364152 : Nat := 233488553930750660908795

theorem tailTrace_1364152 : CollatzResearch.WordTrace tailWord_1364152 prefixEnd_1364152 233488553930750660908795 := by
  unfold tailWord_1364152
  simp only [CollatzResearch.WordTrace]
  refine ⟨24877355476958878729167355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33169807302611838305556473 24877355476958878729167355)
  ·
    refine ⟨37316033215438318093751033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24877355476958878729167355 37316033215438318093751033)
    ·
      refine ⟨27987024911578738570313275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37316033215438318093751033 27987024911578738570313275)
      ·
        refine ⟨41980537367368107855469913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27987024911578738570313275 41980537367368107855469913)
        ·
          refine ⟨31485403025526080891602435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41980537367368107855469913 31485403025526080891602435)
          ·
            refine ⟨47228104538289121337403653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31485403025526080891602435 47228104538289121337403653)
            ·
              refine ⟨8855269600929210250763185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47228104538289121337403653 8855269600929210250763185)
              ·
                refine ⟨6641452200696907688072389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8855269600929210250763185 6641452200696907688072389)
                ·
                  refine ⟨1245272287630670191513573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6641452200696907688072389 1245272287630670191513573)
                  ·
                    refine ⟨233488553930750660908795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1245272287630670191513573 233488553930750660908795)
                    ·
                      rfl

theorem cell23_1364152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_1364152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364152 prefixEnd_1364152 := by exact prefixLift 1364152
  have htrace : WordTrace (prefixWord ++ tailWord_1364152) baseStart_1364152 baseEnd_1364152 := by
    simpa [prefixWord, tailWord_1364152, baseEnd_1364152] using wordTrace_append hprefix tailTrace_1364152
  have hstable : (prefixWord ++ tailWord_1364152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364152).length < 2 ^ (prefixWord ++ tailWord_1364152).sum := by decide
  have hdescent : baseEnd_1364152 < baseStart_1364152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364159 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 7, 2, 2]
def baseStart_1364159 : Nat := 118140960795 + 1364159 * 2 ^ 59
def prefixEnd_1364159 : Nat := 4983230072969 + 3 ^ 40 * 1364159 * 2
def baseEnd_1364159 : Nat := 700469256156833455338853

theorem tailTrace_1364159 : CollatzResearch.WordTrace tailWord_1364159 prefixEnd_1364159 700469256156833455338853 := by
  unfold tailWord_1364159
  simp only [CollatzResearch.WordTrace]
  refine ⟨49754966264892397653839531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33169977509928265102559687 49754966264892397653839531)
  ·
    refine ⟨74632449397338596480759297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49754966264892397653839531 74632449397338596480759297)
    ·
      refine ⟨55974337048003947360569473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74632449397338596480759297 55974337048003947360569473)
      ·
        refine ⟨41980752786002960520427105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55974337048003947360569473 41980752786002960520427105)
        ·
          refine ⟨31485564589502220390320329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41980752786002960520427105 31485564589502220390320329)
          ·
            refine ⟨23614173442126665292740247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31485564589502220390320329 23614173442126665292740247)
            ·
              refine ⟨35421260163189997939110371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23614173442126665292740247 35421260163189997939110371)
              ·
                refine ⟨53131890244784996908665557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35421260163189997939110371 53131890244784996908665557)
                ·
                  refine ⟨1245278677612148365046849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53131890244784996908665557 1245278677612148365046849)
                  ·
                    refine ⟨933959008209111273785137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245278677612148365046849 933959008209111273785137)
                    ·
                      refine ⟨700469256156833455338853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933959008209111273785137 700469256156833455338853)
                      ·
                        rfl

theorem cell23_1364159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_1364159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364159 prefixEnd_1364159 := by exact prefixLift 1364159
  have htrace : WordTrace (prefixWord ++ tailWord_1364159) baseStart_1364159 baseEnd_1364159 := by
    simpa [prefixWord, tailWord_1364159, baseEnd_1364159] using wordTrace_append hprefix tailTrace_1364159
  have hstable : (prefixWord ++ tailWord_1364159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364159).length < 2 ^ (prefixWord ++ tailWord_1364159).sum := by decide
  have hdescent : baseEnd_1364159 < baseStart_1364159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364189 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1364189 : Nat := 118140960795 + 1364189 * 2 ^ 59
def prefixEnd_1364189 : Nat := 4983230072969 + 3 ^ 40 * 1364189 * 2
def baseEnd_1364189 : Nat := 700484660576468337963715

theorem tailTrace_1364189 : CollatzResearch.WordTrace tailWord_1364189 prefixEnd_1364189 700484660576468337963715 := by
  unfold tailWord_1364189
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756060454783712777431621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33170706969855808518287747 49756060454783712777431621)
  ·
    refine ⟨9329261335271946145768429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49756060454783712777431621 9329261335271946145768429)
    ·
      refine ⟨3498473000726979804663161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9329261335271946145768429 3498473000726979804663161)
      ·
        refine ⟨2623854750545234853497371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3498473000726979804663161 2623854750545234853497371)
        ·
          refine ⟨3935782125817852280246057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623854750545234853497371 3935782125817852280246057)
          ·
            refine ⟨2951836594363389210184543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3935782125817852280246057 2951836594363389210184543)
            ·
              refine ⟨4427754891545083815276815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951836594363389210184543 4427754891545083815276815)
              ·
                refine ⟨6641632337317625722915223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427754891545083815276815 6641632337317625722915223)
                ·
                  refine ⟨9962448505976438584372835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641632337317625722915223 9962448505976438584372835)
                  ·
                    refine ⟨14943672758964657876559253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9962448505976438584372835 14943672758964657876559253)
                    ·
                      refine ⟨700484660576468337963715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14943672758964657876559253 700484660576468337963715)
                      ·
                        rfl

theorem cell23_1364189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1364189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364189 prefixEnd_1364189 := by exact prefixLift 1364189
  have htrace : WordTrace (prefixWord ++ tailWord_1364189) baseStart_1364189 baseEnd_1364189 := by
    simpa [prefixWord, tailWord_1364189, baseEnd_1364189] using wordTrace_append hprefix tailTrace_1364189
  have hstable : (prefixWord ++ tailWord_1364189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364189).length < 2 ^ (prefixWord ++ tailWord_1364189).sum := by decide
  have hdescent : baseEnd_1364189 < baseStart_1364189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364199 : List Nat := [1, 1, 5, 3, 1, 1, 4, 7]
def baseStart_1364199 : Nat := 118140960795 + 1364199 * 2 ^ 59
def prefixEnd_1364199 : Nat := 4983230072969 + 3 ^ 40 * 1364199 * 2
def baseEnd_1364199 : Nat := 25944066495667159216247

theorem tailTrace_1364199 : CollatzResearch.WordTrace tailWord_1364199 prefixEnd_1364199 25944066495667159216247 := by
  unfold tailWord_1364199
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756425184747484485295651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33170950123164989656863767 49756425184747484485295651)
  ·
    refine ⟨74634637777121226727943477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49756425184747484485295651 74634637777121226727943477)
    ·
      refine ⟨6996997291605115005744701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74634637777121226727943477 6996997291605115005744701)
      ·
        refine ⟨2623873984351918127154263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6996997291605115005744701 2623873984351918127154263)
        ·
          refine ⟨3935810976527877190731395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623873984351918127154263 3935810976527877190731395)
          ·
            refine ⟨5903716464791815786097093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935810976527877190731395 5903716464791815786097093)
            ·
              refine ⟨1106946837148465459893205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5903716464791815786097093 1106946837148465459893205)
              ·
                refine ⟨25944066495667159216247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1106946837148465459893205 25944066495667159216247)
                ·
                  rfl

theorem cell23_1364199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 7].length) (baseStart_1364199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364199 prefixEnd_1364199 := by exact prefixLift 1364199
  have htrace : WordTrace (prefixWord ++ tailWord_1364199) baseStart_1364199 baseEnd_1364199 := by
    simpa [prefixWord, tailWord_1364199, baseEnd_1364199] using wordTrace_append hprefix tailTrace_1364199
  have hstable : (prefixWord ++ tailWord_1364199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364199).length < 2 ^ (prefixWord ++ tailWord_1364199).sum := by decide
  have hdescent : baseEnd_1364199 < baseStart_1364199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364209 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_1364209 : Nat := 118140960795 + 1364209 * 2 ^ 59
def prefixEnd_1364209 : Nat := 4983230072969 + 3 ^ 40 * 1364209 * 2
def baseEnd_1364209 : Nat := 700494930189558259713623

theorem tailTrace_1364209 : CollatzResearch.WordTrace tailWord_1364209 prefixEnd_1364209 700494930189558259713623 := by
  unfold tailWord_1364209
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756789914711256193159681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33171193276474170795439787 49756789914711256193159681)
  ·
    refine ⟨37317592436033442144869761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49756789914711256193159681 37317592436033442144869761)
    ·
      refine ⟨27988194327025081608652321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37317592436033442144869761 27988194327025081608652321)
      ·
        refine ⟨20991145745268811206489241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27988194327025081608652321 20991145745268811206489241)
        ·
          refine ⟨15743359308951608404866931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20991145745268811206489241 15743359308951608404866931)
          ·
            refine ⟨23615038963427412607300397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15743359308951608404866931 23615038963427412607300397)
            ·
              refine ⟨8855639611285279727737649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23615038963427412607300397 8855639611285279727737649)
              ·
                refine ⟨6641729708463959795803237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8855639611285279727737649 6641729708463959795803237)
                ·
                  refine ⟨1245324320336992461713107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6641729708463959795803237 1245324320336992461713107)
                  ·
                    refine ⟨1867986480505488692569661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1245324320336992461713107 1867986480505488692569661)
                    ·
                      refine ⟨700494930189558259713623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1867986480505488692569661 700494930189558259713623)
                      ·
                        rfl

theorem cell23_1364209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_1364209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364209 prefixEnd_1364209 := by exact prefixLift 1364209
  have htrace : WordTrace (prefixWord ++ tailWord_1364209) baseStart_1364209 baseEnd_1364209 := by
    simpa [prefixWord, tailWord_1364209, baseEnd_1364209] using wordTrace_append hprefix tailTrace_1364209
  have hstable : (prefixWord ++ tailWord_1364209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364209).length < 2 ^ (prefixWord ++ tailWord_1364209).sum := by decide
  have hdescent : baseEnd_1364209 < baseStart_1364209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364210 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1364210 : Nat := 118140960795 + 1364210 * 2 ^ 59
def prefixEnd_1364210 : Nat := 4983230072969 + 3 ^ 40 * 1364210 * 2
def baseEnd_1364210 : Nat := 700495443670212755801119

theorem tailTrace_1364210 : CollatzResearch.WordTrace tailWord_1364210 prefixEnd_1364210 700495443670212755801119 := by
  unfold tailWord_1364210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439206596926908340986521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33171217591805088909297389 12439206596926908340986521)
  ·
    refine ⟨9329404947695181255739891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12439206596926908340986521 9329404947695181255739891)
    ·
      refine ⟨13994107421542771883609837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9329404947695181255739891 13994107421542771883609837)
      ·
        refine ⟨5247790283078539456353689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13994107421542771883609837 5247790283078539456353689)
        ·
          refine ⟨3935842712308904592265267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5247790283078539456353689 3935842712308904592265267)
          ·
            refine ⟨5903764068463356888397901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935842712308904592265267 5903764068463356888397901)
            ·
              refine ⟨2213911525673758833149213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5903764068463356888397901 2213911525673758833149213)
              ·
                refine ⟨830216822127659562430955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2213911525673758833149213 830216822127659562430955)
                ·
                  refine ⟨1245325233191489343646433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830216822127659562430955 1245325233191489343646433)
                  ·
                    refine ⟨933993924893617007734825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245325233191489343646433 933993924893617007734825)
                    ·
                      refine ⟨700495443670212755801119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 933993924893617007734825 700495443670212755801119)
                      ·
                        rfl

theorem cell23_1364210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1364210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364210 prefixEnd_1364210 := by exact prefixLift 1364210
  have htrace : WordTrace (prefixWord ++ tailWord_1364210) baseStart_1364210 baseEnd_1364210 := by
    simpa [prefixWord, tailWord_1364210, baseEnd_1364210] using wordTrace_append hprefix tailTrace_1364210
  have hstable : (prefixWord ++ tailWord_1364210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364210).length < 2 ^ (prefixWord ++ tailWord_1364210).sum := by decide
  have hdescent : baseEnd_1364210 < baseStart_1364210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364253 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1364253 : Nat := 118140960795 + 1364253 * 2 ^ 59
def prefixEnd_1364253 : Nat := 4983230072969 + 3 ^ 40 * 1364253 * 2
def baseEnd_1364253 : Nat := 700517523338356087563421

theorem tailTrace_1364253 : CollatzResearch.WordTrace tailWord_1364253 prefixEnd_1364253 700517523338356087563421 := by
  unfold tailWord_1364253
  simp only [CollatzResearch.WordTrace]
  refine ⟨49758394726551851707761413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33172263151034567805174275 49758394726551851707761413)
  ·
    refine ⟨9329699011228472195205265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49758394726551851707761413 9329699011228472195205265)
    ·
      refine ⟨6997274258421354146403949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9329699011228472195205265 6997274258421354146403949)
      ·
        refine ⟨2623977846908007804901481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6997274258421354146403949 2623977846908007804901481)
        ·
          refine ⟨1967983385181005853676111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2623977846908007804901481 1967983385181005853676111)
          ·
            refine ⟨2951975077771508780514167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967983385181005853676111 2951975077771508780514167)
            ·
              refine ⟨4427962616657263170771251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951975077771508780514167 4427962616657263170771251)
              ·
                refine ⟨6641943924985894756156877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427962616657263170771251 6641943924985894756156877)
                ·
                  refine ⟨2490728971869710533558829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6641943924985894756156877 2490728971869710533558829)
                  ·
                    refine ⟨934023364451141450084561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490728971869710533558829 934023364451141450084561)
                    ·
                      refine ⟨700517523338356087563421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934023364451141450084561 700517523338356087563421)
                      ·
                        rfl

theorem cell23_1364253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1364253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364253 prefixEnd_1364253 := by exact prefixLift 1364253
  have htrace : WordTrace (prefixWord ++ tailWord_1364253) baseStart_1364253 baseEnd_1364253 := by
    simpa [prefixWord, tailWord_1364253, baseEnd_1364253] using wordTrace_append hprefix tailTrace_1364253
  have hstable : (prefixWord ++ tailWord_1364253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364253).length < 2 ^ (prefixWord ++ tailWord_1364253).sum := by decide
  have hdescent : baseEnd_1364253 < baseStart_1364253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364312 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1364312 : Nat := 118140960795 + 1364312 * 2 ^ 59
def prefixEnd_1364312 : Nat := 4983230072969 + 3 ^ 40 * 1364312 * 2
def baseEnd_1364312 : Nat := 700547818696971356725649

theorem tailTrace_1364312 : CollatzResearch.WordTrace tailWord_1364312 prefixEnd_1364312 700547818696971356725649 := by
  unfold tailWord_1364312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24880273316669052392079595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33173697755558736522772793 24880273316669052392079595)
  ·
    refine ⟨37320409975003578588119393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24880273316669052392079595 37320409975003578588119393)
    ·
      refine ⟨27990307481252683941089545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37320409975003578588119393 27990307481252683941089545)
      ·
        refine ⟨20992730610939512955817159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27990307481252683941089545 20992730610939512955817159)
        ·
          refine ⟨31489095916409269433725739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20992730610939512955817159 31489095916409269433725739)
          ·
            refine ⟨47233643874613904150588609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31489095916409269433725739 47233643874613904150588609)
            ·
              refine ⟨35425232905960428112941457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47233643874613904150588609 35425232905960428112941457)
              ·
                refine ⟨26568924679470321084706093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35425232905960428112941457 26568924679470321084706093)
                ·
                  refine ⟨9963346754801370406764785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26568924679470321084706093 9963346754801370406764785)
                  ·
                    refine ⟨7472510066101027805073589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9963346754801370406764785 7472510066101027805073589)
                    ·
                      refine ⟨700547818696971356725649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7472510066101027805073589 700547818696971356725649)
                      ·
                        rfl

theorem cell23_1364312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1364312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364312 prefixEnd_1364312 := by exact prefixLift 1364312
  have htrace : WordTrace (prefixWord ++ tailWord_1364312) baseStart_1364312 baseEnd_1364312 := by
    simpa [prefixWord, tailWord_1364312, baseEnd_1364312] using wordTrace_append hprefix tailTrace_1364312
  have hstable : (prefixWord ++ tailWord_1364312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364312).length < 2 ^ (prefixWord ++ tailWord_1364312).sum := by decide
  have hdescent : baseEnd_1364312 < baseStart_1364312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364319 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 2, 5]
def baseStart_1364319 : Nat := 118140960795 + 1364319 * 2 ^ 59
def prefixEnd_1364319 : Nat := 4983230072969 + 3 ^ 40 * 1364319 * 2
def baseEnd_1364319 : Nat := 233517137687184276446039

theorem tailTrace_1364319 : CollatzResearch.WordTrace tailWord_1364319 prefixEnd_1364319 233517137687184276446039 := by
  unfold tailWord_1364319
  simp only [CollatzResearch.WordTrace]
  refine ⟨49760801944312744979664011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33173867962875163319776007 49760801944312744979664011)
  ·
    refine ⟨74641202916469117469496017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49760801944312744979664011 74641202916469117469496017)
    ·
      refine ⟨55980902187351838102122013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74641202916469117469496017 55980902187351838102122013)
      ·
        refine ⟨20992838320256939288295755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55980902187351838102122013 20992838320256939288295755)
        ·
          refine ⟨31489257480385408932443633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20992838320256939288295755 31489257480385408932443633)
          ·
            refine ⟨23616943110289056699332725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31489257480385408932443633 23616943110289056699332725)
            ·
              refine ⟨2214088416589599065562443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23616943110289056699332725 2214088416589599065562443)
              ·
                refine ⟨3321132624884398598343665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214088416589599065562443 3321132624884398598343665)
                ·
                  refine ⟨2490849468663298948757749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3321132624884398598343665 2490849468663298948757749)
                  ·
                    refine ⟨233517137687184276446039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2490849468663298948757749 233517137687184276446039)
                    ·
                      rfl

theorem cell23_1364319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_1364319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364319 prefixEnd_1364319 := by exact prefixLift 1364319
  have htrace : WordTrace (prefixWord ++ tailWord_1364319) baseStart_1364319 baseEnd_1364319 := by
    simpa [prefixWord, tailWord_1364319, baseEnd_1364319] using wordTrace_append hprefix tailTrace_1364319
  have hstable : (prefixWord ++ tailWord_1364319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364319).length < 2 ^ (prefixWord ++ tailWord_1364319).sum := by decide
  have hdescent : baseEnd_1364319 < baseStart_1364319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364339 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 6, 2]
def baseStart_1364339 : Nat := 118140960795 + 1364339 * 2 ^ 59
def prefixEnd_1364339 : Nat := 4983230072969 + 3 ^ 40 * 1364339 * 2
def baseEnd_1364339 : Nat := 700561682674642751088025

theorem tailTrace_1364339 : CollatzResearch.WordTrace tailWord_1364339 prefixEnd_1364339 700561682674642751088025 := by
  unfold tailWord_1364339
  simp only [CollatzResearch.WordTrace]
  refine ⟨49761531404240288395392071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33174354269493525596928047 49761531404240288395392071)
  ·
    refine ⟨74642297106360432593088107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49761531404240288395392071 74642297106360432593088107)
    ·
      refine ⟨111963445659540648889632161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74642297106360432593088107 111963445659540648889632161)
      ·
        refine ⟨83972584244655486667224121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111963445659540648889632161 83972584244655486667224121)
        ·
          refine ⟨62979438183491615000418091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83972584244655486667224121 62979438183491615000418091)
          ·
            refine ⟨94469157275237422500627137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62979438183491615000418091 94469157275237422500627137)
            ·
              refine ⟨70851867956428066875470353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94469157275237422500627137 70851867956428066875470353)
              ·
                refine ⟨53138900967321050156602765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70851867956428066875470353 53138900967321050156602765)
                ·
                  refine ⟨19927087862745393808726037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53138900967321050156602765 19927087862745393808726037)
                  ·
                    refine ⟨934082243566190334784033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19927087862745393808726037 934082243566190334784033)
                    ·
                      refine ⟨700561682674642751088025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934082243566190334784033 700561682674642751088025)
                      ·
                        rfl

theorem cell23_1364339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6, 2].length) (baseStart_1364339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364339 prefixEnd_1364339 := by exact prefixLift 1364339
  have htrace : WordTrace (prefixWord ++ tailWord_1364339) baseStart_1364339 baseEnd_1364339 := by
    simpa [prefixWord, tailWord_1364339, baseEnd_1364339] using wordTrace_append hprefix tailTrace_1364339
  have hstable : (prefixWord ++ tailWord_1364339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364339).length < 2 ^ (prefixWord ++ tailWord_1364339).sum := by decide
  have hdescent : baseEnd_1364339 < baseStart_1364339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364356 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_1364356 : Nat := 118140960795 + 1364356 * 2 ^ 59
def prefixEnd_1364356 : Nat := 4983230072969 + 3 ^ 40 * 1364356 * 2
def baseEnd_1364356 : Nat := 700570411845769184575447

theorem tailTrace_1364356 : CollatzResearch.WordTrace tailWord_1364356 prefixEnd_1364356 700570411845769184575447 := by
  unfold tailWord_1364356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24881075722589350149380461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33174767630119133532507281 24881075722589350149380461)
  ·
    refine ⟨9330403395971006306017673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24881075722589350149380461 9330403395971006306017673)
    ·
      refine ⟨6997802546978254729513255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9330403395971006306017673 6997802546978254729513255)
      ·
        refine ⟨10496703820467382094269883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6997802546978254729513255 10496703820467382094269883)
        ·
          refine ⟨15745055730701073141404825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10496703820467382094269883 15745055730701073141404825)
          ·
            refine ⟨11808791798025804856053619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15745055730701073141404825 11808791798025804856053619)
            ·
              refine ⟨17713187697038707284080429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808791798025804856053619 17713187697038707284080429)
              ·
                refine ⟨6642445386389515231530161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17713187697038707284080429 6642445386389515231530161)
                ·
                  refine ⟨4981834039792136423647621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6642445386389515231530161 4981834039792136423647621)
                  ·
                    refine ⟨934093882461025579433929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4981834039792136423647621 934093882461025579433929)
                    ·
                      refine ⟨700570411845769184575447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934093882461025579433929 700570411845769184575447)
                      ·
                        rfl

theorem cell23_1364356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_1364356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364356 prefixEnd_1364356 := by exact prefixLift 1364356
  have htrace : WordTrace (prefixWord ++ tailWord_1364356) baseStart_1364356 baseEnd_1364356 := by
    simpa [prefixWord, tailWord_1364356, baseEnd_1364356] using wordTrace_append hprefix tailTrace_1364356
  have hstable : (prefixWord ++ tailWord_1364356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364356).length < 2 ^ (prefixWord ++ tailWord_1364356).sum := by decide
  have hdescent : baseEnd_1364356 < baseStart_1364356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364359 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1364359 : Nat := 118140960795 + 1364359 * 2 ^ 59
def prefixEnd_1364359 : Nat := 4983230072969 + 3 ^ 40 * 1364359 * 2
def baseEnd_1364359 : Nat := 700571952287732672837933

theorem tailTrace_1364359 : CollatzResearch.WordTrace tailWord_1364359 prefixEnd_1364359 700571952287732672837933 := by
  unfold tailWord_1364359
  simp only [CollatzResearch.WordTrace]
  refine ⟨49762260864167831811120131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33174840576111887874080087 49762260864167831811120131)
  ·
    refine ⟨74643391296251747716680197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49762260864167831811120131 74643391296251747716680197)
    ·
      refine ⟨13995635868047202696877537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74643391296251747716680197 13995635868047202696877537)
      ·
        refine ⟨10496726901035402022658153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13995635868047202696877537 10496726901035402022658153)
        ·
          refine ⟨7872545175776551516993615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10496726901035402022658153 7872545175776551516993615)
          ·
            refine ⟨11808817763664827275490423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872545175776551516993615 11808817763664827275490423)
            ·
              refine ⟨17713226645497240913235635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808817763664827275490423 17713226645497240913235635)
              ·
                refine ⟨26569839968245861369853453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17713226645497240913235635 26569839968245861369853453)
                ·
                  refine ⟨9963689988092198013695045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26569839968245861369853453 9963689988092198013695045)
                  ·
                    refine ⟨1868191872767287127567821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9963689988092198013695045 1868191872767287127567821)
                    ·
                      refine ⟨700571952287732672837933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1868191872767287127567821 700571952287732672837933)
                      ·
                        rfl

theorem cell23_1364359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1364359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364359 prefixEnd_1364359 := by exact prefixLift 1364359
  have htrace : WordTrace (prefixWord ++ tailWord_1364359) baseStart_1364359 baseEnd_1364359 := by
    simpa [prefixWord, tailWord_1364359, baseEnd_1364359] using wordTrace_append hprefix tailTrace_1364359
  have hstable : (prefixWord ++ tailWord_1364359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364359).length < 2 ^ (prefixWord ++ tailWord_1364359).sum := by decide
  have hdescent : baseEnd_1364359 < baseStart_1364359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364374 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1364374 : Nat := 118140960795 + 1364374 * 2 ^ 59
def prefixEnd_1364374 : Nat := 4983230072969 + 3 ^ 40 * 1364374 * 2
def baseEnd_1364374 : Nat := 77842183833061123794485

theorem tailTrace_1364374 : CollatzResearch.WordTrace tailWord_1364374 prefixEnd_1364374 77842183833061123794485 := by
  unfold tailWord_1364374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110175497444593085807261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33175205306075659581944117 3110175497444593085807261)
  ·
    refine ⟨1166315811541722407177723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3110175497444593085807261 1166315811541722407177723)
    ·
      refine ⟨1749473717312583610766585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166315811541722407177723 1749473717312583610766585)
      ·
        refine ⟨1312105287984437708074939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749473717312583610766585 1312105287984437708074939)
        ·
          refine ⟨1968157931976656562112409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312105287984437708074939 1968157931976656562112409)
          ·
            refine ⟨1476118448982492421584307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968157931976656562112409 1476118448982492421584307)
            ·
              refine ⟨2214177673473738632376461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476118448982492421584307 2214177673473738632376461)
              ·
                refine ⟨830316627552651987141173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2214177673473738632376461 830316627552651987141173)
                ·
                  refine ⟨77842183833061123794485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830316627552651987141173 77842183833061123794485)
                  ·
                    rfl

theorem cell23_1364374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1364374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364374 prefixEnd_1364374 := by exact prefixLift 1364374
  have htrace : WordTrace (prefixWord ++ tailWord_1364374) baseStart_1364374 baseEnd_1364374 := by
    simpa [prefixWord, tailWord_1364374, baseEnd_1364374] using wordTrace_append hprefix tailTrace_1364374
  have hstable : (prefixWord ++ tailWord_1364374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364374).length < 2 ^ (prefixWord ++ tailWord_1364374).sum := by decide
  have hdescent : baseEnd_1364374 < baseStart_1364374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364376 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1364376 : Nat := 118140960795 + 1364376 * 2 ^ 59
def prefixEnd_1364376 : Nat := 4983230072969 + 3 ^ 40 * 1364376 * 2
def baseEnd_1364376 : Nat := 700580681458859106325355

theorem tailTrace_1364376 : CollatzResearch.WordTrace tailWord_1364376 prefixEnd_1364376 700580681458859106325355 := by
  unfold tailWord_1364376
  simp only [CollatzResearch.WordTrace]
  refine ⟨24881440452553121857244491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33175253936737495809659321 24881440452553121857244491)
  ·
    refine ⟨37322160678829682785866737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24881440452553121857244491 37322160678829682785866737)
    ·
      refine ⟨27991620509122262089400053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37322160678829682785866737 27991620509122262089400053)
      ·
        refine ⟨2624214422730212070881255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27991620509122262089400053 2624214422730212070881255)
        ·
          refine ⟨3936321634095318106321883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624214422730212070881255 3936321634095318106321883)
          ·
            refine ⟨5904482451142977159482825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936321634095318106321883 5904482451142977159482825)
            ·
              refine ⟨4428361838357232869612119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5904482451142977159482825 4428361838357232869612119)
              ·
                refine ⟨6642542757535849304418179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428361838357232869612119 6642542757535849304418179)
                ·
                  refine ⟨9963814136303773956627269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642542757535849304418179 9963814136303773956627269)
                  ·
                    refine ⟨1868215150556957616867613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9963814136303773956627269 1868215150556957616867613)
                    ·
                      refine ⟨700580681458859106325355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1868215150556957616867613 700580681458859106325355)
                      ·
                        rfl

theorem cell23_1364376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1364376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364376 prefixEnd_1364376 := by exact prefixLift 1364376
  have htrace : WordTrace (prefixWord ++ tailWord_1364376) baseStart_1364376 baseEnd_1364376 := by
    simpa [prefixWord, tailWord_1364376, baseEnd_1364376] using wordTrace_append hprefix tailTrace_1364376
  have hstable : (prefixWord ++ tailWord_1364376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364376).length < 2 ^ (prefixWord ++ tailWord_1364376).sum := by decide
  have hdescent : baseEnd_1364376 < baseStart_1364376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364413 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 6]
def baseStart_1364413 : Nat := 118140960795 + 1364413 * 2 ^ 59
def prefixEnd_1364413 : Nat := 4983230072969 + 3 ^ 40 * 1364413 * 2
def baseEnd_1364413 : Nat := 77844408915897273506965

theorem tailTrace_1364413 : CollatzResearch.WordTrace tailWord_1364413 prefixEnd_1364413 77844408915897273506965 := by
  unfold tailWord_1364413
  simp only [CollatzResearch.WordTrace]
  refine ⟨49764230405972199033585893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33176153603981466022390595 49764230405972199033585893)
  ·
    refine ⟨9330793201119787318797355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49764230405972199033585893 9330793201119787318797355)
    ·
      refine ⟨13996189801679680978196033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330793201119787318797355 13996189801679680978196033)
      ·
        refine ⟨10497142351259760733647025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13996189801679680978196033 10497142351259760733647025)
        ·
          refine ⟨7872856763444820550235269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10497142351259760733647025 7872856763444820550235269)
          ·
            refine ⟨1476160643145903853169113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7872856763444820550235269 1476160643145903853169113)
            ·
              refine ⟨1107120482359427889876835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476160643145903853169113 1107120482359427889876835)
              ·
                refine ⟨1660680723539141834815253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107120482359427889876835 1660680723539141834815253)
                ·
                  refine ⟨77844408915897273506965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1660680723539141834815253 77844408915897273506965)
                  ·
                    rfl

theorem cell23_1364413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_1364413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364413 prefixEnd_1364413 := by exact prefixLift 1364413
  have htrace : WordTrace (prefixWord ++ tailWord_1364413) baseStart_1364413 baseEnd_1364413 := by
    simpa [prefixWord, tailWord_1364413, baseEnd_1364413] using wordTrace_append hprefix tailTrace_1364413
  have hstable : (prefixWord ++ tailWord_1364413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364413).length < 2 ^ (prefixWord ++ tailWord_1364413).sum := by decide
  have hdescent : baseEnd_1364413 < baseStart_1364413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364416 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2]
def baseStart_1364416 : Nat := 118140960795 + 1364416 * 2 ^ 59
def prefixEnd_1364416 : Nat := 4983230072969 + 3 ^ 40 * 1364416 * 2
def baseEnd_1364416 : Nat := 700601220685038949825171

theorem tailTrace_1364416 : CollatzResearch.WordTrace tailWord_1364416 prefixEnd_1364416 700601220685038949825171 := by
  unfold tailWord_1364416
  simp only [CollatzResearch.WordTrace]
  refine ⟨24882169912480665272972551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33176226549974220363963401 24882169912480665272972551)
  ·
    refine ⟨37323254868720997909458827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24882169912480665272972551 37323254868720997909458827)
    ·
      refine ⟨55984882303081496864188241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37323254868720997909458827 55984882303081496864188241)
      ·
        refine ⟨41988661727311122648141181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55984882303081496864188241 41988661727311122648141181)
        ·
          refine ⟨15745748147741670993052943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41988661727311122648141181 15745748147741670993052943)
          ·
            refine ⟨23618622221612506489579415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15745748147741670993052943 23618622221612506489579415)
            ·
              refine ⟨35427933332418759734369123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23618622221612506489579415 35427933332418759734369123)
              ·
                refine ⟨53141899998628139601553685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35427933332418759734369123 53141899998628139601553685)
                ·
                  refine ⟨2491026562435694043822829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53141899998628139601553685 2491026562435694043822829)
                  ·
                    refine ⟨934134960913385266433561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491026562435694043822829 934134960913385266433561)
                    ·
                      refine ⟨700601220685038949825171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934134960913385266433561 700601220685038949825171)
                      ·
                        rfl

theorem cell23_1364416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_1364416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364416 prefixEnd_1364416 := by exact prefixLift 1364416
  have htrace : WordTrace (prefixWord ++ tailWord_1364416) baseStart_1364416 baseEnd_1364416 := by
    simpa [prefixWord, tailWord_1364416, baseEnd_1364416] using wordTrace_append hprefix tailTrace_1364416
  have hstable : (prefixWord ++ tailWord_1364416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364416).length < 2 ^ (prefixWord ++ tailWord_1364416).sum := by decide
  have hdescent : baseEnd_1364416 < baseStart_1364416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364459 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_1364459 : Nat := 118140960795 + 1364459 * 2 ^ 59
def prefixEnd_1364459 : Nat := 4983230072969 + 3 ^ 40 * 1364459 * 2
def baseEnd_1364459 : Nat := 700623300353182281587473

theorem tailTrace_1364459 : CollatzResearch.WordTrace tailWord_1364459 prefixEnd_1364459 700623300353182281587473 := by
  unfold tailWord_1364459
  simp only [CollatzResearch.WordTrace]
  refine ⟨49765908163805548889760431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33177272109203699259840287 49765908163805548889760431)
  ·
    refine ⟨74648862245708323334640647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49765908163805548889760431 74648862245708323334640647)
    ·
      refine ⟨111973293368562485001960971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74648862245708323334640647 111973293368562485001960971)
      ·
        refine ⟨167959940052843727502941457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111973293368562485001960971 167959940052843727502941457)
        ·
          refine ⟨125969955039632795627206093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167959940052843727502941457 125969955039632795627206093)
          ·
            refine ⟨47238733139862298360202285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125969955039632795627206093 47238733139862298360202285)
            ·
              refine ⟨17714524927448361885075857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47238733139862298360202285 17714524927448361885075857)
              ·
                refine ⟨13285893695586271413806893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17714524927448361885075857 13285893695586271413806893)
                ·
                  refine ⟨4982210135844851780177585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13285893695586271413806893 4982210135844851780177585)
                  ·
                    refine ⟨3736657601883638835133189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4982210135844851780177585 3736657601883638835133189)
                    ·
                      refine ⟨700623300353182281587473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3736657601883638835133189 700623300353182281587473)
                      ·
                        rfl

theorem cell23_1364459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_1364459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364459 prefixEnd_1364459 := by exact prefixLift 1364459
  have htrace : WordTrace (prefixWord ++ tailWord_1364459) baseStart_1364459 baseEnd_1364459 := by
    simpa [prefixWord, tailWord_1364459, baseEnd_1364459] using wordTrace_append hprefix tailTrace_1364459
  have hstable : (prefixWord ++ tailWord_1364459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364459).length < 2 ^ (prefixWord ++ tailWord_1364459).sum := by decide
  have hdescent : baseEnd_1364459 < baseStart_1364459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364463 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 3, 2, 2]
def baseStart_1364463 : Nat := 118140960795 + 1364463 * 2 ^ 59
def prefixEnd_1364463 : Nat := 4983230072969 + 3 ^ 40 * 1364463 * 2
def baseEnd_1364463 : Nat := 700625354275800265937455

theorem tailTrace_1364463 : CollatzResearch.WordTrace tailWord_1364463 prefixEnd_1364463 700625354275800265937455 := by
  unfold tailWord_1364463
  simp only [CollatzResearch.WordTrace]
  refine ⟨49766054055791057572906043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33177369370527371715270695 49766054055791057572906043)
  ·
    refine ⟨74649081083686586359359065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49766054055791057572906043 74649081083686586359359065)
    ·
      refine ⟨55986810812764939769519299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74649081083686586359359065 55986810812764939769519299)
      ·
        refine ⟨83980216219147409654278949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55986810812764939769519299 83980216219147409654278949)
        ·
          refine ⟨15746290541090139310177303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83980216219147409654278949 15746290541090139310177303)
          ·
            refine ⟨23619435811635208965265955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15746290541090139310177303 23619435811635208965265955)
            ·
              refine ⟨35429153717452813447898933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23619435811635208965265955 35429153717452813447898933)
              ·
                refine ⟨3321483161011201260740525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35429153717452813447898933 3321483161011201260740525)
                ·
                  refine ⟨1245556185379200472777697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3321483161011201260740525 1245556185379200472777697)
                  ·
                    refine ⟨934167139034400354583273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245556185379200472777697 934167139034400354583273)
                    ·
                      refine ⟨700625354275800265937455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934167139034400354583273 700625354275800265937455)
                      ·
                        rfl

theorem cell23_1364463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2, 2].length) (baseStart_1364463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364463 prefixEnd_1364463 := by exact prefixLift 1364463
  have htrace : WordTrace (prefixWord ++ tailWord_1364463) baseStart_1364463 baseEnd_1364463 := by
    simpa [prefixWord, tailWord_1364463, baseEnd_1364463] using wordTrace_append hprefix tailTrace_1364463
  have hstable : (prefixWord ++ tailWord_1364463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364463).length < 2 ^ (prefixWord ++ tailWord_1364463).sum := by decide
  have hdescent : baseEnd_1364463 < baseStart_1364463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364513 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1364513 : Nat := 118140960795 + 1364513 * 2 ^ 59
def prefixEnd_1364513 : Nat := 4983230072969 + 3 ^ 40 * 1364513 * 2
def baseEnd_1364513 : Nat := 700651028308525070312225

theorem tailTrace_1364513 : CollatzResearch.WordTrace tailWord_1364513 prefixEnd_1364513 700651028308525070312225 := by
  unfold tailWord_1364513
  simp only [CollatzResearch.WordTrace]
  refine ⟨49767877705609916112226193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33178585137073277408150795 49767877705609916112226193)
  ·
    refine ⟨37325908279207437084169645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49767877705609916112226193 37325908279207437084169645)
    ·
      refine ⟨13997215604702788906563617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37325908279207437084169645 13997215604702788906563617)
      ·
        refine ⟨10497911703527091679922713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13997215604702788906563617 10497911703527091679922713)
        ·
          refine ⟨7873433777645318759942035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10497911703527091679922713 7873433777645318759942035)
          ·
            refine ⟨11810150666467978139913053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873433777645318759942035 11810150666467978139913053)
            ·
              refine ⟨4428806499925491802467395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11810150666467978139913053 4428806499925491802467395)
              ·
                refine ⟨6643209749888237703701093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428806499925491802467395 6643209749888237703701093)
                ·
                  refine ⟨1245601828104044569443955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6643209749888237703701093 1245601828104044569443955)
                  ·
                    refine ⟨1868402742156066854165933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1245601828104044569443955 1868402742156066854165933)
                    ·
                      refine ⟨700651028308525070312225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1868402742156066854165933 700651028308525070312225)
                      ·
                        rfl

theorem cell23_1364513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1364513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364513 prefixEnd_1364513 := by exact prefixLift 1364513
  have htrace : WordTrace (prefixWord ++ tailWord_1364513) baseStart_1364513 baseEnd_1364513 := by
    simpa [prefixWord, tailWord_1364513, baseEnd_1364513] using wordTrace_append hprefix tailTrace_1364513
  have hstable : (prefixWord ++ tailWord_1364513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364513).length < 2 ^ (prefixWord ++ tailWord_1364513).sum := by decide
  have hdescent : baseEnd_1364513 < baseStart_1364513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364540 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_1364540 : Nat := 118140960795 + 1364540 * 2 ^ 59
def prefixEnd_1364540 : Nat := 4983230072969 + 3 ^ 40 * 1364540 * 2
def baseEnd_1364540 : Nat := 700664892286196464674601

theorem tailTrace_1364540 : CollatzResearch.WordTrace tailWord_1364540 prefixEnd_1364540 700664892286196464674601 := by
  unfold tailWord_1364540
  simp only [CollatzResearch.WordTrace]
  refine ⟨24884431238256049861729537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33179241651008066482306049 24884431238256049861729537)
  ·
    refine ⟨18663323428692037396297153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24884431238256049861729537 18663323428692037396297153)
    ·
      refine ⟨13997492571519028047222865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18663323428692037396297153 13997492571519028047222865)
      ·
        refine ⟨10498119428639271035417149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13997492571519028047222865 10498119428639271035417149)
        ·
          refine ⟨3936794785739726638281431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10498119428639271035417149 3936794785739726638281431)
          ·
            refine ⟨5905192178609589957422147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936794785739726638281431 5905192178609589957422147)
            ·
              refine ⟨8857788267914384936133221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905192178609589957422147 8857788267914384936133221)
              ·
                refine ⟨1660835300233947175524979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8857788267914384936133221 1660835300233947175524979)
                ·
                  refine ⟨2491252950350920763287469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660835300233947175524979 2491252950350920763287469)
                  ·
                    refine ⟨934219856381595286232801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491252950350920763287469 934219856381595286232801)
                    ·
                      refine ⟨700664892286196464674601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934219856381595286232801 700664892286196464674601)
                      ·
                        rfl

theorem cell23_1364540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_1364540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364540 prefixEnd_1364540 := by exact prefixLift 1364540
  have htrace : WordTrace (prefixWord ++ tailWord_1364540) baseStart_1364540 baseEnd_1364540 := by
    simpa [prefixWord, tailWord_1364540, baseEnd_1364540] using wordTrace_append hprefix tailTrace_1364540
  have hstable : (prefixWord ++ tailWord_1364540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364540).length < 2 ^ (prefixWord ++ tailWord_1364540).sum := by decide
  have hdescent : baseEnd_1364540 < baseStart_1364540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364556 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1364556 : Nat := 118140960795 + 1364556 * 2 ^ 59
def prefixEnd_1364556 : Nat := 4983230072969 + 3 ^ 40 * 1364556 * 2
def baseEnd_1364556 : Nat := 700673107976668402074527

theorem tailTrace_1364556 : CollatzResearch.WordTrace tailWord_1364556 prefixEnd_1364556 700673107976668402074527 := by
  unfold tailWord_1364556
  simp only [CollatzResearch.WordTrace]
  refine ⟨24884723022227067228020761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33179630696302756304027681 24884723022227067228020761)
  ·
    refine ⟨18663542266670300421015571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24884723022227067228020761 18663542266670300421015571)
    ·
      refine ⟨27995313400005450631523357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18663542266670300421015571 27995313400005450631523357)
      ·
        refine ⟨10498242525002043986821259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27995313400005450631523357 10498242525002043986821259)
        ·
          refine ⟨15747363787503065980231889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498242525002043986821259 15747363787503065980231889)
          ·
            refine ⟨11810522840627299485173917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15747363787503065980231889 11810522840627299485173917)
            ·
              refine ⟨4428946065235237306940219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11810522840627299485173917 4428946065235237306940219)
              ·
                refine ⟨6643419097852855960410329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428946065235237306940219 6643419097852855960410329)
                ·
                  refine ⟨4982564323389641970307747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643419097852855960410329 4982564323389641970307747)
                  ·
                    refine ⟨7473846485084462955461621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982564323389641970307747 7473846485084462955461621)
                    ·
                      refine ⟨700673107976668402074527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7473846485084462955461621 700673107976668402074527)
                      ·
                        rfl

theorem cell23_1364556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1364556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364556 prefixEnd_1364556 := by exact prefixLift 1364556
  have htrace : WordTrace (prefixWord ++ tailWord_1364556) baseStart_1364556 baseEnd_1364556 := by
    simpa [prefixWord, tailWord_1364556, baseEnd_1364556] using wordTrace_append hprefix tailTrace_1364556
  have hstable : (prefixWord ++ tailWord_1364556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364556).length < 2 ^ (prefixWord ++ tailWord_1364556).sum := by decide
  have hdescent : baseEnd_1364556 < baseStart_1364556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364557 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1364557 : Nat := 118140960795 + 1364557 * 2 ^ 59
def prefixEnd_1364557 : Nat := 4983230072969 + 3 ^ 40 * 1364557 * 2
def baseEnd_1364557 : Nat := 700673621457322898162023

theorem tailTrace_1364557 : CollatzResearch.WordTrace tailWord_1364557 prefixEnd_1364557 700673621457322898162023 := by
  unfold tailWord_1364557
  simp only [CollatzResearch.WordTrace]
  refine ⟨49769482517450511626827925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33179655011633674417885283 49769482517450511626827925)
  ·
    refine ⟨2332944493005492732507559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49769482517450511626827925 2332944493005492732507559)
    ·
      refine ⟨3499416739508239098761339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332944493005492732507559 3499416739508239098761339)
      ·
        refine ⟨5249125109262358648142009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499416739508239098761339 5249125109262358648142009)
        ·
          refine ⟨3936843831946768986106507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5249125109262358648142009 3936843831946768986106507)
          ·
            refine ⟨5905265747920153479159761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936843831946768986106507 5905265747920153479159761)
            ·
              refine ⟨4428949310940115109369821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5905265747920153479159761 4428949310940115109369821)
              ·
                refine ⟨1660855991602543166013683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4428949310940115109369821 1660855991602543166013683)
                ·
                  refine ⟨2491283987403814749020525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660855991602543166013683 2491283987403814749020525)
                  ·
                    refine ⟨934231495276430530882697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491283987403814749020525 934231495276430530882697)
                    ·
                      refine ⟨700673621457322898162023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934231495276430530882697 700673621457322898162023)
                      ·
                        rfl

theorem cell23_1364557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1364557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364557 prefixEnd_1364557 := by exact prefixLift 1364557
  have htrace : WordTrace (prefixWord ++ tailWord_1364557) baseStart_1364557 baseEnd_1364557 := by
    simpa [prefixWord, tailWord_1364557, baseEnd_1364557] using wordTrace_append hprefix tailTrace_1364557
  have hstable : (prefixWord ++ tailWord_1364557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364557).length < 2 ^ (prefixWord ++ tailWord_1364557).sum := by decide
  have hdescent : baseEnd_1364557 < baseStart_1364557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364559 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 9]
def baseStart_1364559 : Nat := 118140960795 + 1364559 * 2 ^ 59
def prefixEnd_1364559 : Nat := 4983230072969 + 3 ^ 40 * 1364559 * 2
def baseEnd_1364559 : Nat := 77852738713181321148557

theorem tailTrace_1364559 : CollatzResearch.WordTrace tailWord_1364559 prefixEnd_1364559 77852738713181321148557 := by
  unfold tailWord_1364559
  simp only [CollatzResearch.WordTrace]
  refine ⟨49769555463443265968400731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33179703642295510645600487 49769555463443265968400731)
  ·
    refine ⟨74654333195164898952601097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49769555463443265968400731 74654333195164898952601097)
    ·
      refine ⟨55990749896373674214450823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74654333195164898952601097 55990749896373674214450823)
      ·
        refine ⟨83986124844560511321676235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55990749896373674214450823 83986124844560511321676235)
        ·
          refine ⟨125979187266840766982514353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83986124844560511321676235 125979187266840766982514353)
          ·
            refine ⟨94484390450130575236885765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125979187266840766982514353 94484390450130575236885765)
            ·
              refine ⟨17715823209399482856916081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94484390450130575236885765 17715823209399482856916081)
              ·
                refine ⟨13286867407049612142687061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17715823209399482856916081 13286867407049612142687061)
                ·
                  refine ⟨77852738713181321148557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13286867407049612142687061 77852738713181321148557)
                  ·
                    rfl

theorem cell23_1364559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 9].length) (baseStart_1364559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364559 prefixEnd_1364559 := by exact prefixLift 1364559
  have htrace : WordTrace (prefixWord ++ tailWord_1364559) baseStart_1364559 baseEnd_1364559 := by
    simpa [prefixWord, tailWord_1364559, baseEnd_1364559] using wordTrace_append hprefix tailTrace_1364559
  have hstable : (prefixWord ++ tailWord_1364559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364559).length < 2 ^ (prefixWord ++ tailWord_1364559).sum := by decide
  have hdescent : baseEnd_1364559 < baseStart_1364559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364576 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 7]
def baseStart_1364576 : Nat := 118140960795 + 1364576 * 2 ^ 59
def prefixEnd_1364576 : Nat := 4983230072969 + 3 ^ 40 * 1364576 * 2
def baseEnd_1364576 : Nat := 77853708621084258202715

theorem tailTrace_1364576 : CollatzResearch.WordTrace tailWord_1364576 prefixEnd_1364576 77853708621084258202715 := by
  unfold tailWord_1364576
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885087752190838935884791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33180117002921118581179721 24885087752190838935884791)
  ·
    refine ⟨37327631628286258403827187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24885087752190838935884791 37327631628286258403827187)
    ·
      refine ⟨55991447442429387605740781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37327631628286258403827187 55991447442429387605740781)
      ·
        refine ⟨20996792790911020352152793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55991447442429387605740781 20996792790911020352152793)
        ·
          refine ⟨15747594593183265264114595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20996792790911020352152793 15747594593183265264114595)
          ·
            refine ⟨23621391889774897896171893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747594593183265264114595 23621391889774897896171893)
            ·
              refine ⟨2214505489666396677766115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23621391889774897896171893 2214505489666396677766115)
              ·
                refine ⟨3321758234499595016649173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214505489666396677766115 3321758234499595016649173)
                ·
                  refine ⟨77853708621084258202715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3321758234499595016649173 77853708621084258202715)
                  ·
                    rfl

theorem cell23_1364576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_1364576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364576 prefixEnd_1364576 := by exact prefixLift 1364576
  have htrace : WordTrace (prefixWord ++ tailWord_1364576) baseStart_1364576 baseEnd_1364576 := by
    simpa [prefixWord, tailWord_1364576, baseEnd_1364576] using wordTrace_append hprefix tailTrace_1364576
  have hstable : (prefixWord ++ tailWord_1364576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364576).length < 2 ^ (prefixWord ++ tailWord_1364576).sum := by decide
  have hdescent : baseEnd_1364576 < baseStart_1364576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364657 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_1364657 : Nat := 118140960795 + 1364657 * 2 ^ 59
def prefixEnd_1364657 : Nat := 4983230072969 + 3 ^ 40 * 1364657 * 2
def baseEnd_1364657 : Nat := 233574989840924168970521

theorem tailTrace_1364657 : CollatzResearch.WordTrace tailWord_1364657 prefixEnd_1364657 233574989840924168970521 := by
  unfold tailWord_1364657
  simp only [CollatzResearch.WordTrace]
  refine ⟨49773129817088228705468225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33182086544725485803645483 49773129817088228705468225)
  ·
    refine ⟨37329847362816171529101169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49773129817088228705468225 37329847362816171529101169)
    ·
      refine ⟨27997385522112128646825877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37329847362816171529101169 27997385522112128646825877)
      ·
        refine ⟨1312377446349006030319963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27997385522112128646825877 1312377446349006030319963)
        ·
          refine ⟨1968566169523509045479945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312377446349006030319963 1968566169523509045479945)
          ·
            refine ⟨1476424627142631784109959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968566169523509045479945 1476424627142631784109959)
            ·
              refine ⟨2214636940713947676164939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476424627142631784109959 2214636940713947676164939)
              ·
                refine ⟨3321955411070921514247409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214636940713947676164939 3321955411070921514247409)
                ·
                  refine ⟨2491466558303191135685557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3321955411070921514247409 2491466558303191135685557)
                  ·
                    refine ⟨233574989840924168970521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2491466558303191135685557 233574989840924168970521)
                    ·
                      rfl

theorem cell23_1364657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_1364657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364657 prefixEnd_1364657 := by exact prefixLift 1364657
  have htrace : WordTrace (prefixWord ++ tailWord_1364657) baseStart_1364657 baseEnd_1364657 := by
    simpa [prefixWord, tailWord_1364657, baseEnd_1364657] using wordTrace_append hprefix tailTrace_1364657
  have hstable : (prefixWord ++ tailWord_1364657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364657).length < 2 ^ (prefixWord ++ tailWord_1364657).sum := by decide
  have hdescent : baseEnd_1364657 < baseStart_1364657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364666 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_1364666 : Nat := 118140960795 + 1364666 * 2 ^ 59
def prefixEnd_1364666 : Nat := 4983230072969 + 3 ^ 40 * 1364666 * 2
def baseEnd_1364666 : Nat := 77858843427629219077669

theorem tailTrace_1364666 : CollatzResearch.WordTrace tailWord_1364666 prefixEnd_1364666 77858843427629219077669 := by
  unfold tailWord_1364666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443364518513905810636463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33182305382703748828363901 12443364518513905810636463)
  ·
    refine ⟨18665046777770858715954695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12443364518513905810636463 18665046777770858715954695)
    ·
      refine ⟨27997570166656288073932043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18665046777770858715954695 27997570166656288073932043)
      ·
        refine ⟨41996355249984432110898065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27997570166656288073932043 41996355249984432110898065)
        ·
          refine ⟨31497266437488324083173549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41996355249984432110898065 31497266437488324083173549)
          ·
            refine ⟨11811474914058121531190081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31497266437488324083173549 11811474914058121531190081)
            ·
              refine ⟨8858606185543591148392561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11811474914058121531190081 8858606185543591148392561)
              ·
                refine ⟨6643954639157693361294421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8858606185543591148392561 6643954639157693361294421)
                ·
                  refine ⟨77858843427629219077669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6643954639157693361294421 77858843427629219077669)
                  ·
                    rfl

theorem cell23_1364666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_1364666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364666 prefixEnd_1364666 := by exact prefixLift 1364666
  have htrace : WordTrace (prefixWord ++ tailWord_1364666) baseStart_1364666 baseEnd_1364666 := by
    simpa [prefixWord, tailWord_1364666, baseEnd_1364666] using wordTrace_append hprefix tailTrace_1364666
  have hstable : (prefixWord ++ tailWord_1364666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364666).length < 2 ^ (prefixWord ++ tailWord_1364666).sum := by decide
  have hdescent : baseEnd_1364666 < baseStart_1364666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364713 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_1364713 : Nat := 118140960795 + 1364713 * 2 ^ 59
def prefixEnd_1364713 : Nat := 4983230072969 + 3 ^ 40 * 1364713 * 2
def baseEnd_1364713 : Nat := 233584574813141429270435

theorem tailTrace_1364713 : CollatzResearch.WordTrace tailWord_1364713 prefixEnd_1364713 233584574813141429270435 := by
  unfold tailWord_1364713
  simp only [CollatzResearch.WordTrace]
  refine ⟨49775172304885350269506793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33183448203256900179671195 49775172304885350269506793)
  ·
    refine ⟨37331379228664012702130095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49775172304885350269506793 37331379228664012702130095)
    ·
      refine ⟨55997068842996019053195143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37331379228664012702130095 55997068842996019053195143)
      ·
        refine ⟨83995603264494028579792715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55997068842996019053195143 83995603264494028579792715)
        ·
          refine ⟨125993404896741042869689073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83995603264494028579792715 125993404896741042869689073)
          ·
            refine ⟨94495053672555782152266805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125993404896741042869689073 94495053672555782152266805)
            ·
              refine ⟨8858911281802104576775013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94495053672555782152266805 8858911281802104576775013)
              ·
                refine ⟨1661045865337894608145315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8858911281802104576775013 1661045865337894608145315)
                ·
                  refine ⟨2491568798006841912217973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661045865337894608145315 2491568798006841912217973)
                  ·
                    refine ⟨233584574813141429270435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2491568798006841912217973 233584574813141429270435)
                    ·
                      rfl

theorem cell23_1364713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_1364713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364713 prefixEnd_1364713 := by exact prefixLift 1364713
  have htrace : WordTrace (prefixWord ++ tailWord_1364713) baseStart_1364713 baseEnd_1364713 := by
    simpa [prefixWord, tailWord_1364713, baseEnd_1364713] using wordTrace_append hprefix tailTrace_1364713
  have hstable : (prefixWord ++ tailWord_1364713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364713).length < 2 ^ (prefixWord ++ tailWord_1364713).sum := by decide
  have hdescent : baseEnd_1364713 < baseStart_1364713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364720 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2]
def baseStart_1364720 : Nat := 118140960795 + 1364720 * 2 ^ 59
def prefixEnd_1364720 : Nat := 4983230072969 + 3 ^ 40 * 1364720 * 2
def baseEnd_1364720 : Nat := 700757318804005760423773

theorem tailTrace_1364720 : CollatzResearch.WordTrace tailWord_1364720 prefixEnd_1364720 700757318804005760423773 := by
  unfold tailWord_1364720
  simp only [CollatzResearch.WordTrace]
  refine ⟨24887713807929995232505807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33183618410573326976674409 24887713807929995232505807)
  ·
    refine ⟨37331570711894992848758711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24887713807929995232505807 37331570711894992848758711)
    ·
      refine ⟨55997356067842489273138067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37331570711894992848758711 55997356067842489273138067)
      ·
        refine ⟨83996034101763733909707101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55997356067842489273138067 83996034101763733909707101)
        ·
          refine ⟨31498512788161400216140163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83996034101763733909707101 31498512788161400216140163)
          ·
            refine ⟨47247769182242100324210245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31498512788161400216140163 47247769182242100324210245)
            ·
              refine ⟨8858956721670393810789421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47247769182242100324210245 8858956721670393810789421)
              ·
                refine ⟨3322108770626397679046033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8858956721670393810789421 3322108770626397679046033)
                ·
                  refine ⟨2491581577969798259284525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322108770626397679046033 2491581577969798259284525)
                  ·
                    refine ⟨934343091738674347231697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2491581577969798259284525 934343091738674347231697)
                    ·
                      refine ⟨700757318804005760423773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934343091738674347231697 700757318804005760423773)
                      ·
                        rfl

theorem cell23_1364720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 3, 2].length) (baseStart_1364720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364720 prefixEnd_1364720 := by exact prefixLift 1364720
  have htrace : WordTrace (prefixWord ++ tailWord_1364720) baseStart_1364720 baseEnd_1364720 := by
    simpa [prefixWord, tailWord_1364720, baseEnd_1364720] using wordTrace_append hprefix tailTrace_1364720
  have hstable : (prefixWord ++ tailWord_1364720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364720).length < 2 ^ (prefixWord ++ tailWord_1364720).sum := by decide
  have hdescent : baseEnd_1364720 < baseStart_1364720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364753 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_1364753 : Nat := 118140960795 + 1364753 * 2 ^ 59
def prefixEnd_1364753 : Nat := 4983230072969 + 3 ^ 40 * 1364753 * 2
def baseEnd_1364753 : Nat := 700774263665604131311121

theorem tailTrace_1364753 : CollatzResearch.WordTrace tailWord_1364753 prefixEnd_1364753 700774263665604131311121 := by
  unfold tailWord_1364753
  simp only [CollatzResearch.WordTrace]
  refine ⟨49776631224740437100962913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33184420816493624733975275 49776631224740437100962913)
  ·
    refine ⟨37332473418555327825722185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49776631224740437100962913 37332473418555327825722185)
    ·
      refine ⟨27999355063916495869291639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37332473418555327825722185 27999355063916495869291639)
      ·
        refine ⟨41999032595874743803937459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27999355063916495869291639 41999032595874743803937459)
        ·
          refine ⟨62998548893812115705906189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41999032595874743803937459 62998548893812115705906189)
          ·
            refine ⟨23624455835179543389714821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62998548893812115705906189 23624455835179543389714821)
            ·
              refine ⟨4429585469096164385571529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23624455835179543389714821 4429585469096164385571529)
              ·
                refine ⟨3322189101822123289178647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429585469096164385571529 3322189101822123289178647)
                ·
                  refine ⟨4983283652733184933767971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322189101822123289178647 4983283652733184933767971)
                  ·
                    refine ⟨7474925479099777400651957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983283652733184933767971 7474925479099777400651957)
                    ·
                      refine ⟨700774263665604131311121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7474925479099777400651957 700774263665604131311121)
                      ·
                        rfl

theorem cell23_1364753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_1364753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364753 prefixEnd_1364753 := by exact prefixLift 1364753
  have htrace : WordTrace (prefixWord ++ tailWord_1364753) baseStart_1364753 baseEnd_1364753 := by
    simpa [prefixWord, tailWord_1364753, baseEnd_1364753] using wordTrace_append hprefix tailTrace_1364753
  have hstable : (prefixWord ++ tailWord_1364753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364753).length < 2 ^ (prefixWord ++ tailWord_1364753).sum := by decide
  have hdescent : baseEnd_1364753 < baseStart_1364753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364767 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_1364767 : Nat := 118140960795 + 1364767 * 2 ^ 59
def prefixEnd_1364767 : Nat := 4983230072969 + 3 ^ 40 * 1364767 * 2
def baseEnd_1364767 : Nat := 700781452394767076536057

theorem tailTrace_1364767 : CollatzResearch.WordTrace tailWord_1364767 prefixEnd_1364767 700781452394767076536057 := by
  unfold tailWord_1364767
  simp only [CollatzResearch.WordTrace]
  refine ⟨49777141846689717491972555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33184761231126478327981703 49777141846689717491972555)
  ·
    refine ⟨74665712770034576237958833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49777141846689717491972555 74665712770034576237958833)
    ·
      refine ⟨55999284577525932178469125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74665712770034576237958833 55999284577525932178469125)
      ·
        refine ⟨10499865858286112283462961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55999284577525932178469125 10499865858286112283462961)
        ·
          refine ⟨7874899393714584212597221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10499865858286112283462961 7874899393714584212597221)
          ·
            refine ⟨1476543636321484539861979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7874899393714584212597221 1476543636321484539861979)
            ·
              refine ⟨2214815454482226809792969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476543636321484539861979 2214815454482226809792969)
              ·
                refine ⟨1661111590861670107344727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214815454482226809792969 1661111590861670107344727)
                ·
                  refine ⟨2491667386292505161017091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661111590861670107344727 2491667386292505161017091)
                  ·
                    refine ⟨3737501079438757741525637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2491667386292505161017091 3737501079438757741525637)
                    ·
                      refine ⟨700781452394767076536057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3737501079438757741525637 700781452394767076536057)
                      ·
                        rfl

theorem cell23_1364767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_1364767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364767 prefixEnd_1364767 := by exact prefixLift 1364767
  have htrace : WordTrace (prefixWord ++ tailWord_1364767) baseStart_1364767 baseEnd_1364767 := by
    simpa [prefixWord, tailWord_1364767, baseEnd_1364767] using wordTrace_append hprefix tailTrace_1364767
  have hstable : (prefixWord ++ tailWord_1364767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364767).length < 2 ^ (prefixWord ++ tailWord_1364767).sum := by decide
  have hdescent : baseEnd_1364767 < baseStart_1364767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364781 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1364781 : Nat := 118140960795 + 1364781 * 2 ^ 59
def prefixEnd_1364781 : Nat := 4983230072969 + 3 ^ 40 * 1364781 * 2
def baseEnd_1364781 : Nat := 233596213707976673920331

theorem tailTrace_1364781 : CollatzResearch.WordTrace tailWord_1364781 prefixEnd_1364781 233596213707976673920331 := by
  unfold tailWord_1364781
  simp only [CollatzResearch.WordTrace]
  refine ⟨49777652468638997882982197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33185101645759331921988131 49777652468638997882982197)
  ·
    refine ⟨4666654918934906051529581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49777652468638997882982197 4666654918934906051529581)
    ·
      refine ⟨1749995594600589769323593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4666654918934906051529581 1749995594600589769323593)
      ·
        refine ⟨1312496695950442326992695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749995594600589769323593 1312496695950442326992695)
        ·
          refine ⟨1968745043925663490489043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312496695950442326992695 1968745043925663490489043)
          ·
            refine ⟨2953117565888495235733565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968745043925663490489043 2953117565888495235733565)
            ·
              refine ⟨1107419087208185713400087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2953117565888495235733565 1107419087208185713400087)
              ·
                refine ⟨1661128630812278570100131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107419087208185713400087 1661128630812278570100131)
                ·
                  refine ⟨2491692946218417855150197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661128630812278570100131 2491692946218417855150197)
                  ·
                    refine ⟨233596213707976673920331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2491692946218417855150197 233596213707976673920331)
                    ·
                      rfl

theorem cell23_1364781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1364781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364781 prefixEnd_1364781 := by exact prefixLift 1364781
  have htrace : WordTrace (prefixWord ++ tailWord_1364781) baseStart_1364781 baseEnd_1364781 := by
    simpa [prefixWord, tailWord_1364781, baseEnd_1364781] using wordTrace_append hprefix tailTrace_1364781
  have hstable : (prefixWord ++ tailWord_1364781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364781).length < 2 ^ (prefixWord ++ tailWord_1364781).sum := by decide
  have hdescent : baseEnd_1364781 < baseStart_1364781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364790 : List Nat := [5, 1, 2, 2, 2, 11]
def baseStart_1364790 : Nat := 118140960795 + 1364790 * 2 ^ 59
def prefixEnd_1364790 : Nat := 4983230072969 + 3 ^ 40 * 1364790 * 2
def baseEnd_1364790 : Nat := 2883922890740002002257

theorem tailTrace_1364790 : CollatzResearch.WordTrace tailWord_1364790 prefixEnd_1364790 2883922890740002002257 := by
  unfold tailWord_1364790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111123795350399526253739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33185320483737594946706549 3111123795350399526253739)
  ·
    refine ⟨4666685693025599289380609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111123795350399526253739 4666685693025599289380609)
    ·
      refine ⟨3500014269769199467035457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4666685693025599289380609 3500014269769199467035457)
      ·
        refine ⟨2625010702326899600276593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3500014269769199467035457 2625010702326899600276593)
        ·
          refine ⟨1968758026745174700207445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625010702326899600276593 1968758026745174700207445)
          ·
            refine ⟨2883922890740002002257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1968758026745174700207445 2883922890740002002257)
            ·
              rfl

theorem cell23_1364790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 11].length) (baseStart_1364790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364790 prefixEnd_1364790 := by exact prefixLift 1364790
  have htrace : WordTrace (prefixWord ++ tailWord_1364790) baseStart_1364790 baseEnd_1364790 := by
    simpa [prefixWord, tailWord_1364790, baseEnd_1364790] using wordTrace_append hprefix tailTrace_1364790
  have hstable : (prefixWord ++ tailWord_1364790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364790).length < 2 ^ (prefixWord ++ tailWord_1364790).sum := by decide
  have hdescent : baseEnd_1364790 < baseStart_1364790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364800 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3]
def baseStart_1364800 : Nat := 118140960795 + 1364800 * 2 ^ 59
def prefixEnd_1364800 : Nat := 4983230072969 + 3 ^ 40 * 1364800 * 2
def baseEnd_1364800 : Nat := 700798397256365447423405

theorem tailTrace_1364800 : CollatzResearch.WordTrace tailWord_1364800 prefixEnd_1364800 700798397256365447423405 := by
  unfold tailWord_1364800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24889172727785082063961927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33185563637046776085282569 24889172727785082063961927)
  ·
    refine ⟨37333759091677623095942891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24889172727785082063961927 37333759091677623095942891)
    ·
      refine ⟨56000638637516434643914337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37333759091677623095942891 56000638637516434643914337)
      ·
        refine ⟨42000478978137325982935753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56000638637516434643914337 42000478978137325982935753)
        ·
          refine ⟨31500359233602994487201815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42000478978137325982935753 31500359233602994487201815)
          ·
            refine ⟨47250538850404491730802723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31500359233602994487201815 47250538850404491730802723)
            ·
              refine ⟨70875808275606737596204085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47250538850404491730802723 70875808275606737596204085)
              ·
                refine ⟨6644607025838131649644133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70875808275606737596204085 6644607025838131649644133)
                ·
                  refine ⟨1245863817344649684308275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6644607025838131649644133 1245863817344649684308275)
                  ·
                    refine ⟨1868795726016974526462413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1245863817344649684308275 1868795726016974526462413)
                    ·
                      refine ⟨700798397256365447423405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1868795726016974526462413 700798397256365447423405)
                      ·
                        rfl

theorem cell23_1364800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_1364800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364800 prefixEnd_1364800 := by exact prefixLift 1364800
  have htrace : WordTrace (prefixWord ++ tailWord_1364800) baseStart_1364800 baseEnd_1364800 := by
    simpa [prefixWord, tailWord_1364800, baseEnd_1364800] using wordTrace_append hprefix tailTrace_1364800
  have hstable : (prefixWord ++ tailWord_1364800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364800).length < 2 ^ (prefixWord ++ tailWord_1364800).sum := by decide
  have hdescent : baseEnd_1364800 < baseStart_1364800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364817 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_1364817 : Nat := 118140960795 + 1364817 * 2 ^ 59
def prefixEnd_1364817 : Nat := 4983230072969 + 3 ^ 40 * 1364817 * 2
def baseEnd_1364817 : Nat := 700807126427491880910827

theorem tailTrace_1364817 : CollatzResearch.WordTrace tailWord_1364817 prefixEnd_1364817 700807126427491880910827 := by
  unfold tailWord_1364817
  simp only [CollatzResearch.WordTrace]
  refine ⟨49778965496508576031292705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33185976997672384020861803 49778965496508576031292705)
  ·
    refine ⟨37334224122381432023469529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49778965496508576031292705 37334224122381432023469529)
    ·
      refine ⟨28000668091786074017602147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37334224122381432023469529 28000668091786074017602147)
      ·
        refine ⟨42001002137679111026403221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28000668091786074017602147 42001002137679111026403221)
        ·
          refine ⟨1968796975203708329362651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42001002137679111026403221 1968796975203708329362651)
          ·
            refine ⟨2953195462805562494043977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968796975203708329362651 2953195462805562494043977)
            ·
              refine ⟨2214896597104171870532983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953195462805562494043977 2214896597104171870532983)
              ·
                refine ⟨3322344895656257805799475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214896597104171870532983 3322344895656257805799475)
                ·
                  refine ⟨4983517343484386708699213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322344895656257805799475 4983517343484386708699213)
                  ·
                    refine ⟨1868819003806645015762205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4983517343484386708699213 1868819003806645015762205)
                    ·
                      refine ⟨700807126427491880910827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1868819003806645015762205 700807126427491880910827)
                      ·
                        rfl

theorem cell23_1364817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_1364817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364817 prefixEnd_1364817 := by exact prefixLift 1364817
  have htrace : WordTrace (prefixWord ++ tailWord_1364817) baseStart_1364817 baseEnd_1364817 := by
    simpa [prefixWord, tailWord_1364817, baseEnd_1364817] using wordTrace_append hprefix tailTrace_1364817
  have hstable : (prefixWord ++ tailWord_1364817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364817).length < 2 ^ (prefixWord ++ tailWord_1364817).sum := by decide
  have hdescent : baseEnd_1364817 < baseStart_1364817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364843 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_1364843 : Nat := 118140960795 + 1364843 * 2 ^ 59
def prefixEnd_1364843 : Nat := 4983230072969 + 3 ^ 40 * 1364843 * 2
def baseEnd_1364843 : Nat := 700820476924508779185707

theorem tailTrace_1364843 : CollatzResearch.WordTrace tailWord_1364843 prefixEnd_1364843 700820476924508779185707 := by
  unfold tailWord_1364843
  simp only [CollatzResearch.WordTrace]
  refine ⟨49779913794414382471739183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33186609196276254981159455 49779913794414382471739183)
  ·
    refine ⟨74669870691621573707608775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49779913794414382471739183 74669870691621573707608775)
    ·
      refine ⟨112004806037432360561413163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74669870691621573707608775 112004806037432360561413163)
      ·
        refine ⟨168007209056148540842119745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112004806037432360561413163 168007209056148540842119745)
        ·
          refine ⟨126005406792111405631589809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168007209056148540842119745 126005406792111405631589809)
          ·
            refine ⟨94504055094083554223692357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126005406792111405631589809 94504055094083554223692357)
            ·
              refine ⟨17719510330140666416942317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94504055094083554223692357 17719510330140666416942317)
              ·
                refine ⟨6644816373802749906353369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17719510330140666416942317 6644816373802749906353369)
                ·
                  refine ⟨4983612280352062429765027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644816373802749906353369 4983612280352062429765027)
                  ·
                    refine ⟨7475418420528093644647541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983612280352062429765027 7475418420528093644647541)
                    ·
                      refine ⟨700820476924508779185707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7475418420528093644647541 700820476924508779185707)
                      ·
                        rfl

theorem cell23_1364843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_1364843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364843 prefixEnd_1364843 := by exact prefixLift 1364843
  have htrace : WordTrace (prefixWord ++ tailWord_1364843) baseStart_1364843 baseEnd_1364843 := by
    simpa [prefixWord, tailWord_1364843, baseEnd_1364843] using wordTrace_append hprefix tailTrace_1364843
  have hstable : (prefixWord ++ tailWord_1364843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364843).length < 2 ^ (prefixWord ++ tailWord_1364843).sum := by decide
  have hdescent : baseEnd_1364843 < baseStart_1364843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364863 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 7]
def baseStart_1364863 : Nat := 118140960795 + 1364863 * 2 ^ 59
def prefixEnd_1364863 : Nat := 4983230072969 + 3 ^ 40 * 1364863 * 2
def baseEnd_1364863 : Nat := 77870082948622077881735

theorem tailTrace_1364863 : CollatzResearch.WordTrace tailWord_1364863 prefixEnd_1364863 77870082948622077881735 := by
  unfold tailWord_1364863
  simp only [CollatzResearch.WordTrace]
  refine ⟨49780643254341925887467243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33187095502894617258311495 49780643254341925887467243)
  ·
    refine ⟨74670964881512888831200865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49780643254341925887467243 74670964881512888831200865)
    ·
      refine ⟨56003223661134666623400649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74670964881512888831200865 56003223661134666623400649)
      ·
        refine ⟨42002417745850999967550487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56003223661134666623400649 42002417745850999967550487)
        ·
          refine ⟨63003626618776499951325731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42002417745850999967550487 63003626618776499951325731)
          ·
            refine ⟨94505439928164749926988597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63003626618776499951325731 94505439928164749926988597)
            ·
              refine ⟨8859884993265445305655181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94505439928164749926988597 8859884993265445305655181)
              ·
                refine ⟨3322456872474541989620693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8859884993265445305655181 3322456872474541989620693)
                ·
                  refine ⟨77870082948622077881735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3322456872474541989620693 77870082948622077881735)
                  ·
                    rfl

theorem cell23_1364863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 7].length) (baseStart_1364863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364863 prefixEnd_1364863 := by exact prefixLift 1364863
  have htrace : WordTrace (prefixWord ++ tailWord_1364863) baseStart_1364863 baseEnd_1364863 := by
    simpa [prefixWord, tailWord_1364863, baseEnd_1364863] using wordTrace_append hprefix tailTrace_1364863
  have hstable : (prefixWord ++ tailWord_1364863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364863).length < 2 ^ (prefixWord ++ tailWord_1364863).sum := by decide
  have hdescent : baseEnd_1364863 < baseStart_1364863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364874 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1364874 : Nat := 118140960795 + 1364874 * 2 ^ 59
def prefixEnd_1364874 : Nat := 4983230072969 + 3 ^ 40 * 1364874 * 2
def baseEnd_1364874 : Nat := 700836394824798157898065

theorem tailTrace_1364874 : CollatzResearch.WordTrace tailWord_1364874 prefixEnd_1364874 700836394824798157898065 := by
  unfold tailWord_1364874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12445261114325518691529419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33187362971534716510745117 12445261114325518691529419)
  ·
    refine ⟨18667891671488278037294129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12445261114325518691529419 18667891671488278037294129)
    ·
      refine ⟨14000918753616208527970597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18667891671488278037294129 14000918753616208527970597)
      ·
        refine ⟨2625172266303039098994487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14000918753616208527970597 2625172266303039098994487)
        ·
          refine ⟨3937758399454558648491731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625172266303039098994487 3937758399454558648491731)
          ·
            refine ⟨5906637599181837972737597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937758399454558648491731 5906637599181837972737597)
            ·
              refine ⟨2214989099693189239776599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5906637599181837972737597 2214989099693189239776599)
              ·
                refine ⟨3322483649539783859664899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214989099693189239776599 3322483649539783859664899)
                ·
                  refine ⟨4983725474309675789497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322483649539783859664899 4983725474309675789497349)
                  ·
                    refine ⟨934448526433064210530753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4983725474309675789497349 934448526433064210530753)
                    ·
                      refine ⟨700836394824798157898065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934448526433064210530753 700836394824798157898065)
                      ·
                        rfl

theorem cell23_1364874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1364874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364874 prefixEnd_1364874 := by exact prefixLift 1364874
  have htrace : WordTrace (prefixWord ++ tailWord_1364874) baseStart_1364874 baseEnd_1364874 := by
    simpa [prefixWord, tailWord_1364874, baseEnd_1364874] using wordTrace_append hprefix tailTrace_1364874
  have hstable : (prefixWord ++ tailWord_1364874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364874).length < 2 ^ (prefixWord ++ tailWord_1364874).sum := by decide
  have hdescent : baseEnd_1364874 < baseStart_1364874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364917 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_1364917 : Nat := 118140960795 + 1364917 * 2 ^ 59
def prefixEnd_1364917 : Nat := 4983230072969 + 3 ^ 40 * 1364917 * 2
def baseEnd_1364917 : Nat := 700858474492941489660367

theorem tailTrace_1364917 : CollatzResearch.WordTrace tailWord_1364917 prefixEnd_1364917 700858474492941489660367 := by
  unfold tailWord_1364917
  simp only [CollatzResearch.WordTrace]
  refine ⟨49782612796146293109933005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33188408530764195406622003 49782612796146293109933005)
  ·
    refine ⟨18668479798554859916224877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49782612796146293109933005 18668479798554859916224877)
    ·
      refine ⟨7000679924458072468584329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18668479798554859916224877 7000679924458072468584329)
      ·
        refine ⟨5250509943343554351438247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7000679924458072468584329 5250509943343554351438247)
        ·
          refine ⟨7875764915015331527157371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250509943343554351438247 7875764915015331527157371)
          ·
            refine ⟨11813647372522997290736057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875764915015331527157371 11813647372522997290736057)
            ·
              refine ⟨8860235529392247968052043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11813647372522997290736057 8860235529392247968052043)
              ·
                refine ⟨13290353294088371952078065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8860235529392247968052043 13290353294088371952078065)
                ·
                  refine ⟨9967764970566278964058549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13290353294088371952078065 9967764970566278964058549)
                  ·
                    refine ⟨934477965990588652880489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9967764970566278964058549 934477965990588652880489)
                    ·
                      refine ⟨700858474492941489660367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934477965990588652880489 700858474492941489660367)
                      ·
                        rfl

theorem cell23_1364917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_1364917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364917 prefixEnd_1364917 := by exact prefixLift 1364917
  have htrace : WordTrace (prefixWord ++ tailWord_1364917) baseStart_1364917 baseEnd_1364917 := by
    simpa [prefixWord, tailWord_1364917, baseEnd_1364917] using wordTrace_append hprefix tailTrace_1364917
  have hstable : (prefixWord ++ tailWord_1364917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364917).length < 2 ^ (prefixWord ++ tailWord_1364917).sum := by decide
  have hdescent : baseEnd_1364917 < baseStart_1364917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364920 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1364920 : Nat := 118140960795 + 1364920 * 2 ^ 59
def prefixEnd_1364920 : Nat := 4983230072969 + 3 ^ 40 * 1364920 * 2
def baseEnd_1364920 : Nat := 700860014934904977922853

theorem tailTrace_1364920 : CollatzResearch.WordTrace tailWord_1364920 prefixEnd_1364920 700860014934904977922853 := by
  unfold tailWord_1364920
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891361107567712311146107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33188481476756949748194809 24891361107567712311146107)
  ·
    refine ⟨37337041661351568466719161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24891361107567712311146107 37337041661351568466719161)
    ·
      refine ⟨28002781246013676350039371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37337041661351568466719161 28002781246013676350039371)
      ·
        refine ⟨42004171869020514525059057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002781246013676350039371 42004171869020514525059057)
        ·
          refine ⟨31503128901765385893794293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42004171869020514525059057 31503128901765385893794293)
          ·
            refine ⟨2953418334540504927543215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31503128901765385893794293 2953418334540504927543215)
            ·
              refine ⟨4430127501810757391314823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953418334540504927543215 4430127501810757391314823)
              ·
                refine ⟨6645191252716136086972235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430127501810757391314823 6645191252716136086972235)
                ·
                  refine ⟨9967786879074204130458353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645191252716136086972235 9967786879074204130458353)
                  ·
                    refine ⟨7475840159305653097843765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9967786879074204130458353 7475840159305653097843765)
                    ·
                      refine ⟨700860014934904977922853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7475840159305653097843765 700860014934904977922853)
                      ·
                        rfl

theorem cell23_1364920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1364920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364920 prefixEnd_1364920 := by exact prefixLift 1364920
  have htrace : WordTrace (prefixWord ++ tailWord_1364920) baseStart_1364920 baseEnd_1364920 := by
    simpa [prefixWord, tailWord_1364920, baseEnd_1364920] using wordTrace_append hprefix tailTrace_1364920
  have hstable : (prefixWord ++ tailWord_1364920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364920).length < 2 ^ (prefixWord ++ tailWord_1364920).sum := by decide
  have hdescent : baseEnd_1364920 < baseStart_1364920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364925 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_1364925 : Nat := 118140960795 + 1364925 * 2 ^ 59
def prefixEnd_1364925 : Nat := 4983230072969 + 3 ^ 40 * 1364925 * 2
def baseEnd_1364925 : Nat := 700862582338177458360331

theorem tailTrace_1364925 : CollatzResearch.WordTrace tailWord_1364925 prefixEnd_1364925 700862582338177458360331 := by
  unfold tailWord_1364925
  simp only [CollatzResearch.WordTrace]
  refine ⟨49782904580117310476224229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33188603053411540317482819 49782904580117310476224229)
  ·
    refine ⟨9334294608771995714292043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49782904580117310476224229 9334294608771995714292043)
    ·
      refine ⟨14001441913157993571438065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9334294608771995714292043 14001441913157993571438065)
      ·
        refine ⟨10501081434868495178578549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14001441913157993571438065 10501081434868495178578549)
        ·
          refine ⟨984476384518921422991739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10501081434868495178578549 984476384518921422991739)
          ·
            refine ⟨1476714576778382134487609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984476384518921422991739 1476714576778382134487609)
            ·
              refine ⟨1107535932583786600865707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476714576778382134487609 1107535932583786600865707)
              ·
                refine ⟨1661303898875679901298561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107535932583786600865707 1661303898875679901298561)
                ·
                  refine ⟨1245977924156759925973921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1661303898875679901298561 1245977924156759925973921)
                  ·
                    refine ⟨934483443117569944480441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245977924156759925973921 934483443117569944480441)
                    ·
                      refine ⟨700862582338177458360331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934483443117569944480441 700862582338177458360331)
                      ·
                        rfl

theorem cell23_1364925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_1364925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364925 prefixEnd_1364925 := by exact prefixLift 1364925
  have htrace : WordTrace (prefixWord ++ tailWord_1364925) baseStart_1364925 baseEnd_1364925 := by
    simpa [prefixWord, tailWord_1364925, baseEnd_1364925] using wordTrace_append hprefix tailTrace_1364925
  have hstable : (prefixWord ++ tailWord_1364925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364925).length < 2 ^ (prefixWord ++ tailWord_1364925).sum := by decide
  have hdescent : baseEnd_1364925 < baseStart_1364925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364933 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_1364933 : Nat := 118140960795 + 1364933 * 2 ^ 59
def prefixEnd_1364933 : Nat := 4983230072969 + 3 ^ 40 * 1364933 * 2
def baseEnd_1364933 : Nat := 700866690183413427060293

theorem tailTrace_1364933 : CollatzResearch.WordTrace tailWord_1364933 prefixEnd_1364933 700866690183413427060293 := by
  unfold tailWord_1364933
  simp only [CollatzResearch.WordTrace]
  refine ⟨49783196364088327842515453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33188797576058885228343635 49783196364088327842515453)
  ·
    refine ⟨18668698636533122940943295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49783196364088327842515453 18668698636533122940943295)
    ·
      refine ⟨28003047954799684411414943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18668698636533122940943295 28003047954799684411414943)
      ·
        refine ⟨42004571932199526617122415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28003047954799684411414943 42004571932199526617122415)
        ·
          refine ⟨63006857898299289925683623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42004571932199526617122415 63006857898299289925683623)
          ·
            refine ⟨94510286847448934888525435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63006857898299289925683623 94510286847448934888525435)
            ·
              refine ⟨141765430271173402332788153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94510286847448934888525435 141765430271173402332788153)
              ·
                refine ⟨106324072703380051749591115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141765430271173402332788153 106324072703380051749591115)
                ·
                  refine ⟨159486109055070077624386673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106324072703380051749591115 159486109055070077624386673)
                  ·
                    refine ⟨119614581791302558218290005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159486109055070077624386673 119614581791302558218290005)
                    ·
                      refine ⟨700866690183413427060293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 119614581791302558218290005 700866690183413427060293)
                      ·
                        rfl

theorem cell23_1364933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_1364933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1364933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1364933 prefixEnd_1364933 := by exact prefixLift 1364933
  have htrace : WordTrace (prefixWord ++ tailWord_1364933) baseStart_1364933 baseEnd_1364933 := by
    simpa [prefixWord, tailWord_1364933, baseEnd_1364933] using wordTrace_append hprefix tailTrace_1364933
  have hstable : (prefixWord ++ tailWord_1364933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364933).length < 2 ^ (prefixWord ++ tailWord_1364933).sum := by decide
  have hdescent : baseEnd_1364933 < baseStart_1364933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365007 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 8, 3, 2]
def baseStart_1365007 : Nat := 118140960795 + 1365007 * 2 ^ 59
def prefixEnd_1365007 : Nat := 4983230072969 + 3 ^ 40 * 1365007 * 2
def baseEnd_1365007 : Nat := 700904687751846137534953

theorem tailTrace_1365007 : CollatzResearch.WordTrace tailWord_1365007 prefixEnd_1365007 700904687751846137534953 := by
  unfold tailWord_1365007
  simp only [CollatzResearch.WordTrace]
  refine ⟨49785895365820238480709275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33190596910546825653806183 49785895365820238480709275)
  ·
    refine ⟨74678843048730357721063913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49785895365820238480709275 74678843048730357721063913)
    ·
      refine ⟨56009132286547768290797935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74678843048730357721063913 56009132286547768290797935)
      ·
        refine ⟨84013698429821652436196903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56009132286547768290797935 84013698429821652436196903)
        ·
          refine ⟨126020547644732478654295355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84013698429821652436196903 126020547644732478654295355)
          ·
            refine ⟨189030821467098717981443033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126020547644732478654295355 189030821467098717981443033)
            ·
              refine ⟨141773116100324038486082275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189030821467098717981443033 141773116100324038486082275)
              ·
                refine ⟨212659674150486057729123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141773116100324038486082275 212659674150486057729123413)
                ·
                  refine ⟨2492105556451008489013165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 212659674150486057729123413 2492105556451008489013165)
                  ·
                    refine ⟨934539583669128183379937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492105556451008489013165 934539583669128183379937)
                    ·
                      refine ⟨700904687751846137534953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934539583669128183379937 700904687751846137534953)
                      ·
                        rfl

theorem cell23_1365007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3, 2].length) (baseStart_1365007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365007 prefixEnd_1365007 := by exact prefixLift 1365007
  have htrace : WordTrace (prefixWord ++ tailWord_1365007) baseStart_1365007 baseEnd_1365007 := by
    simpa [prefixWord, tailWord_1365007, baseEnd_1365007] using wordTrace_append hprefix tailTrace_1365007
  have hstable : (prefixWord ++ tailWord_1365007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365007).length < 2 ^ (prefixWord ++ tailWord_1365007).sum := by decide
  have hdescent : baseEnd_1365007 < baseStart_1365007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365021 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 6]
def baseStart_1365021 : Nat := 118140960795 + 1365021 * 2 ^ 59
def prefixEnd_1365021 : Nat := 4983230072969 + 3 ^ 40 * 1365021 * 2
def baseEnd_1365021 : Nat := 77879097386778786973321

theorem tailTrace_1365021 : CollatzResearch.WordTrace tailWord_1365021 prefixEnd_1365021 77879097386778786973321 := by
  unfold tailWord_1365021
  simp only [CollatzResearch.WordTrace]
  refine ⟨49786405987769518871718917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33190937325179679247812611 49786405987769518871718917)
  ·
    refine ⟨9334951122706784788447297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49786405987769518871718917 9334951122706784788447297)
    ·
      refine ⟨7001213342030088591335473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334951122706784788447297 7001213342030088591335473)
      ·
        refine ⟨5250910006522566443501605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7001213342030088591335473 5250910006522566443501605)
        ·
          refine ⟨984545626222981208156551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5250910006522566443501605 984545626222981208156551)
          ·
            refine ⟨1476818439334471812234827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984545626222981208156551 1476818439334471812234827)
            ·
              refine ⟨2215227659001707718352241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476818439334471812234827 2215227659001707718352241)
              ·
                refine ⟨1661420744251280788764181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215227659001707718352241 1661420744251280788764181)
                ·
                  refine ⟨77879097386778786973321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1661420744251280788764181 77879097386778786973321)
                  ·
                    rfl

theorem cell23_1365021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_1365021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365021 prefixEnd_1365021 := by exact prefixLift 1365021
  have htrace : WordTrace (prefixWord ++ tailWord_1365021) baseStart_1365021 baseEnd_1365021 := by
    simpa [prefixWord, tailWord_1365021, baseEnd_1365021] using wordTrace_append hprefix tailTrace_1365021
  have hstable : (prefixWord ++ tailWord_1365021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365021).length < 2 ^ (prefixWord ++ tailWord_1365021).sum := by decide
  have hdescent : baseEnd_1365021 < baseStart_1365021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365031 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1365031 : Nat := 118140960795 + 1365031 * 2 ^ 59
def prefixEnd_1365031 : Nat := 4983230072969 + 3 ^ 40 * 1365031 * 2
def baseEnd_1365031 : Nat := 700917011287554043634843

theorem tailTrace_1365031 : CollatzResearch.WordTrace tailWord_1365031 prefixEnd_1365031 700917011287554043634843 := by
  unfold tailWord_1365031
  simp only [CollatzResearch.WordTrace]
  refine ⟨49786770717733290579582947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33191180478488860386388631 49786770717733290579582947)
  ·
    refine ⟨74680156076599935869374421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49786770717733290579582947 74680156076599935869374421)
    ·
      refine ⟨1750316158045310996938463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74680156076599935869374421 1750316158045310996938463)
      ·
        refine ⟨2625474237067966495407695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750316158045310996938463 2625474237067966495407695)
        ·
          refine ⟨3938211355601949743111543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625474237067966495407695 3938211355601949743111543)
          ·
            refine ⟨5907317033402924614667315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938211355601949743111543 5907317033402924614667315)
            ·
              refine ⟨8860975550104386922000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907317033402924614667315 8860975550104386922000973)
              ·
                refine ⟨3322865831289145095750365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8860975550104386922000973 3322865831289145095750365)
                ·
                  refine ⟨1246074686733429410906387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3322865831289145095750365 1246074686733429410906387)
                  ·
                    refine ⟨1869112030100144116359581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246074686733429410906387 1869112030100144116359581)
                    ·
                      refine ⟨700917011287554043634843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869112030100144116359581 700917011287554043634843)
                      ·
                        rfl

theorem cell23_1365031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1365031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365031 prefixEnd_1365031 := by exact prefixLift 1365031
  have htrace : WordTrace (prefixWord ++ tailWord_1365031) baseStart_1365031 baseEnd_1365031 := by
    simpa [prefixWord, tailWord_1365031, baseEnd_1365031] using wordTrace_append hprefix tailTrace_1365031
  have hstable : (prefixWord ++ tailWord_1365031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365031).length < 2 ^ (prefixWord ++ tailWord_1365031).sum := by decide
  have hdescent : baseEnd_1365031 < baseStart_1365031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365074 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1365074 : Nat := 118140960795 + 1365074 * 2 ^ 59
def prefixEnd_1365074 : Nat := 4983230072969 + 3 ^ 40 * 1365074 * 2
def baseEnd_1365074 : Nat := 700939090955697375397145

theorem tailTrace_1365074 : CollatzResearch.WordTrace tailWord_1365074 prefixEnd_1365074 700939090955697375397145 := by
  unfold tailWord_1365074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447084764144377230849569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33192226037718339282265517 12447084764144377230849569)
  ·
    refine ⟨9335313573108282923137177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12447084764144377230849569 9335313573108282923137177)
    ·
      refine ⟨7001485179831212192352883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9335313573108282923137177 7001485179831212192352883)
      ·
        refine ⟨10502227769746818288529325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001485179831212192352883 10502227769746818288529325)
        ·
          refine ⟨3938335413655056858198497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10502227769746818288529325 3938335413655056858198497)
          ·
            refine ⟨2953751560241292643648873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3938335413655056858198497 2953751560241292643648873)
            ·
              refine ⟨2215313670180969482736655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953751560241292643648873 2215313670180969482736655)
              ·
                refine ⟨3322970505271454224104983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215313670180969482736655 3322970505271454224104983)
                ·
                  refine ⟨4984455757907181336157475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322970505271454224104983 4984455757907181336157475)
                  ·
                    refine ⟨7476683636860772004236213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4984455757907181336157475 7476683636860772004236213)
                    ·
                      refine ⟨700939090955697375397145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7476683636860772004236213 700939090955697375397145)
                      ·
                        rfl

theorem cell23_1365074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1365074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365074 prefixEnd_1365074 := by exact prefixLift 1365074
  have htrace : WordTrace (prefixWord ++ tailWord_1365074) baseStart_1365074 baseEnd_1365074 := by
    simpa [prefixWord, tailWord_1365074, baseEnd_1365074] using wordTrace_append hprefix tailTrace_1365074
  have hstable : (prefixWord ++ tailWord_1365074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365074).length < 2 ^ (prefixWord ++ tailWord_1365074).sum := by decide
  have hdescent : baseEnd_1365074 < baseStart_1365074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365098 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1365098 : Nat := 118140960795 + 1365098 * 2 ^ 59
def prefixEnd_1365098 : Nat := 4983230072969 + 3 ^ 40 * 1365098 * 2
def baseEnd_1365098 : Nat := 233650471497135093832345

theorem tailTrace_1365098 : CollatzResearch.WordTrace tailWord_1365098 prefixEnd_1365098 233650471497135093832345 := by
  unfold tailWord_1365098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447303602122640255567987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33192809605660374014847965 12447303602122640255567987)
  ·
    refine ⟨18670955403183960383351981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12447303602122640255567987 18670955403183960383351981)
    ·
      refine ⟨7001608276193985143756993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18670955403183960383351981 7001608276193985143756993)
      ·
        refine ⟨5251206207145488857817745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7001608276193985143756993 5251206207145488857817745)
        ·
          refine ⟨3938404655359116643363309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5251206207145488857817745 3938404655359116643363309)
          ·
            refine ⟨1476901745759668741261241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3938404655359116643363309 1476901745759668741261241)
            ·
              refine ⟨1107676309319751555945931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476901745759668741261241 1107676309319751555945931)
              ·
                refine ⟨1661514463979627333918897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107676309319751555945931 1661514463979627333918897)
                ·
                  refine ⟨1246135847984720500439173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1661514463979627333918897 1246135847984720500439173)
                  ·
                    refine ⟨233650471497135093832345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246135847984720500439173 233650471497135093832345)
                    ·
                      rfl

theorem cell23_1365098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1365098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365098 prefixEnd_1365098 := by exact prefixLift 1365098
  have htrace : WordTrace (prefixWord ++ tailWord_1365098) baseStart_1365098 baseEnd_1365098 := by
    simpa [prefixWord, tailWord_1365098, baseEnd_1365098] using wordTrace_append hprefix tailTrace_1365098
  have hstable : (prefixWord ++ tailWord_1365098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365098).length < 2 ^ (prefixWord ++ tailWord_1365098).sum := by decide
  have hdescent : baseEnd_1365098 < baseStart_1365098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365138 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1365138 : Nat := 118140960795 + 1365138 * 2 ^ 59
def prefixEnd_1365138 : Nat := 4983230072969 + 3 ^ 40 * 1365138 * 2
def baseEnd_1365138 : Nat := 700971953717585124996851

theorem tailTrace_1365138 : CollatzResearch.WordTrace tailWord_1365138 prefixEnd_1365138 700971953717585124996851 := by
  unfold tailWord_1365138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447668332086411963432017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33193782218897098569152045 12447668332086411963432017)
  ·
    refine ⟨9335751249064808972574013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12447668332086411963432017 9335751249064808972574013)
    ·
      refine ⟨3500906718399303364715255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9335751249064808972574013 3500906718399303364715255)
      ·
        refine ⟨5251360077598955047072883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500906718399303364715255 5251360077598955047072883)
        ·
          refine ⟨7877040116398432570609325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251360077598955047072883 7877040116398432570609325)
          ·
            refine ⟨2953890043649412213978497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7877040116398432570609325 2953890043649412213978497)
            ·
              refine ⟨2215417532737059160483873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953890043649412213978497 2215417532737059160483873)
              ·
                refine ⟨1661563149552794370362905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215417532737059160483873 1661563149552794370362905)
                ·
                  refine ⟨1246172362164595777772179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1661563149552794370362905 1246172362164595777772179)
                  ·
                    refine ⟨1869258543246893666658269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246172362164595777772179 1869258543246893666658269)
                    ·
                      refine ⟨700971953717585124996851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869258543246893666658269 700971953717585124996851)
                      ·
                        rfl

theorem cell23_1365138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1365138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365138 prefixEnd_1365138 := by exact prefixLift 1365138
  have htrace : WordTrace (prefixWord ++ tailWord_1365138) baseStart_1365138 baseEnd_1365138 := by
    simpa [prefixWord, tailWord_1365138, baseEnd_1365138] using wordTrace_append hprefix tailTrace_1365138
  have hstable : (prefixWord ++ tailWord_1365138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365138).length < 2 ^ (prefixWord ++ tailWord_1365138).sum := by decide
  have hdescent : baseEnd_1365138 < baseStart_1365138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365157 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_1365157 : Nat := 118140960795 + 1365157 * 2 ^ 59
def prefixEnd_1365157 : Nat := 4983230072969 + 3 ^ 40 * 1365157 * 2
def baseEnd_1365157 : Nat := 700981709850020550659263

theorem tailTrace_1365157 : CollatzResearch.WordTrace tailWord_1365157 prefixEnd_1365157 700981709850020550659263 := by
  unfold tailWord_1365157
  simp only [CollatzResearch.WordTrace]
  refine ⟨49791366315276814098669725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33194244210184542732446483 49791366315276814098669725)
  ·
    refine ⟨18671762368228805287001147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49791366315276814098669725 18671762368228805287001147)
    ·
      refine ⟨28007643552343207930501721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18671762368228805287001147 28007643552343207930501721)
      ·
        refine ⟨21005732664257405947876291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28007643552343207930501721 21005732664257405947876291)
        ·
          refine ⟨31508598996386108921814437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21005732664257405947876291 31508598996386108921814437)
          ·
            refine ⟨5907862311822395422840207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31508598996386108921814437 5907862311822395422840207)
            ·
              refine ⟨8861793467733593134260311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907862311822395422840207 8861793467733593134260311)
              ·
                refine ⟨13292690201600389701390467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8861793467733593134260311 13292690201600389701390467)
                ·
                  refine ⟨19939035302400584552085701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13292690201600389701390467 19939035302400584552085701)
                  ·
                    refine ⟨3738569119200109603516069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19939035302400584552085701 3738569119200109603516069)
                    ·
                      refine ⟨700981709850020550659263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3738569119200109603516069 700981709850020550659263)
                      ·
                        rfl

theorem cell23_1365157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_1365157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365157 prefixEnd_1365157 := by exact prefixLift 1365157
  have htrace : WordTrace (prefixWord ++ tailWord_1365157) baseStart_1365157 baseEnd_1365157 := by
    simpa [prefixWord, tailWord_1365157, baseEnd_1365157] using wordTrace_append hprefix tailTrace_1365157
  have hstable : (prefixWord ++ tailWord_1365157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365157).length < 2 ^ (prefixWord ++ tailWord_1365157).sum := by decide
  have hdescent : baseEnd_1365157 < baseStart_1365157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365194 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1365194 : Nat := 118140960795 + 1365194 * 2 ^ 59
def prefixEnd_1365194 : Nat := 4983230072969 + 3 ^ 40 * 1365194 * 2
def baseEnd_1365194 : Nat := 701000708634236905896593

theorem tailTrace_1365194 : CollatzResearch.WordTrace tailWord_1365194 prefixEnd_1365194 701000708634236905896593 := by
  unfold tailWord_1365194
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448178954035692354441659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33195143877428512945177757 12448178954035692354441659)
  ·
    refine ⟨18672268431053538531662489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12448178954035692354441659 18672268431053538531662489)
    ·
      refine ⟨14004201323290153898746867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18672268431053538531662489 14004201323290153898746867)
      ·
        refine ⟨21006301984935230848120301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14004201323290153898746867 21006301984935230848120301)
        ·
          refine ⟨7877363244350711568045113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21006301984935230848120301 7877363244350711568045113)
          ·
            refine ⟨5908022433263033676033835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7877363244350711568045113 5908022433263033676033835)
            ·
              refine ⟨8862033649894550514050753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908022433263033676033835 8862033649894550514050753)
              ·
                refine ⟨6646525237420912885538065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8862033649894550514050753 6646525237420912885538065)
                ·
                  refine ⟨4984893928065684664153549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6646525237420912885538065 4984893928065684664153549)
                  ·
                    refine ⟨1869335223024631749057581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4984893928065684664153549 1869335223024631749057581)
                    ·
                      refine ⟨701000708634236905896593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869335223024631749057581 701000708634236905896593)
                      ·
                        rfl

theorem cell23_1365194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1365194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365194 prefixEnd_1365194 := by exact prefixLift 1365194
  have htrace : WordTrace (prefixWord ++ tailWord_1365194) baseStart_1365194 baseEnd_1365194 := by
    simpa [prefixWord, tailWord_1365194, baseEnd_1365194] using wordTrace_append hprefix tailTrace_1365194
  have hstable : (prefixWord ++ tailWord_1365194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365194).length < 2 ^ (prefixWord ++ tailWord_1365194).sum := by decide
  have hdescent : baseEnd_1365194 < baseStart_1365194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365207 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1365207 : Nat := 118140960795 + 1365207 * 2 ^ 59
def prefixEnd_1365207 : Nat := 4983230072969 + 3 ^ 40 * 1365207 * 2
def baseEnd_1365207 : Nat := 701007383882745355034033

theorem tailTrace_1365207 : CollatzResearch.WordTrace tailWord_1365207 prefixEnd_1365207 701007383882745355034033 := by
  unfold tailWord_1365207
  simp only [CollatzResearch.WordTrace]
  refine ⟨49793189965095672637989875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33195459976730448425326583 49793189965095672637989875)
  ·
    refine ⟨74689784947643508956984813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49793189965095672637989875 74689784947643508956984813)
    ·
      refine ⟨28008669355366315858869305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74689784947643508956984813 28008669355366315858869305)
      ·
        refine ⟨21006502016524736894151979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28008669355366315858869305 21006502016524736894151979)
        ·
          refine ⟨31509753024787105341227969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21006502016524736894151979 31509753024787105341227969)
          ·
            refine ⟨23632314768590329005920977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31509753024787105341227969 23632314768590329005920977)
            ·
              refine ⟨17724236076442746754440733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23632314768590329005920977 17724236076442746754440733)
              ·
                refine ⟨6646588528666030032915275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17724236076442746754440733 6646588528666030032915275)
                ·
                  refine ⟨9969882792999045049372913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6646588528666030032915275 9969882792999045049372913)
                  ·
                    refine ⟨7477412094749283787029685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9969882792999045049372913 7477412094749283787029685)
                    ·
                      refine ⟨701007383882745355034033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7477412094749283787029685 701007383882745355034033)
                      ·
                        rfl

theorem cell23_1365207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1365207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365207 prefixEnd_1365207 := by exact prefixLift 1365207
  have htrace : WordTrace (prefixWord ++ tailWord_1365207) baseStart_1365207 baseEnd_1365207 := by
    simpa [prefixWord, tailWord_1365207, baseEnd_1365207] using wordTrace_append hprefix tailTrace_1365207
  have hstable : (prefixWord ++ tailWord_1365207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365207).length < 2 ^ (prefixWord ++ tailWord_1365207).sum := by decide
  have hdescent : baseEnd_1365207 < baseStart_1365207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365257 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 8]
def baseStart_1365257 : Nat := 118140960795 + 1365257 * 2 ^ 59
def prefixEnd_1365257 : Nat := 4983230072969 + 3 ^ 40 * 1365257 * 2
def baseEnd_1365257 : Nat := 77892561990607795489867

theorem tailTrace_1365257 : CollatzResearch.WordTrace tailWord_1365257 prefixEnd_1365257 77892561990607795489867 := by
  unfold tailWord_1365257
  simp only [CollatzResearch.WordTrace]
  refine ⟨49795013614914531177310025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33196675743276354118206683 49795013614914531177310025)
  ·
    refine ⟨37346260211185898382982519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49795013614914531177310025 37346260211185898382982519)
    ·
      refine ⟨56019390316778847574473779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37346260211185898382982519 56019390316778847574473779)
      ·
        refine ⟨84029085475168271361710669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56019390316778847574473779 84029085475168271361710669)
        ·
          refine ⟨31510907053188101760641501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84029085475168271361710669 31510907053188101760641501)
          ·
            refine ⟨11816590144945538160240563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31510907053188101760641501 11816590144945538160240563)
            ·
              refine ⟨17724885217418307240360845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816590144945538160240563 17724885217418307240360845)
              ·
                refine ⟨6646831956531865215135317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17724885217418307240360845 6646831956531865215135317)
                ·
                  refine ⟨77892561990607795489867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6646831956531865215135317 77892561990607795489867)
                  ·
                    rfl

theorem cell23_1365257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_1365257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365257 prefixEnd_1365257 := by exact prefixLift 1365257
  have htrace : WordTrace (prefixWord ++ tailWord_1365257) baseStart_1365257 baseEnd_1365257 := by
    simpa [prefixWord, tailWord_1365257, baseEnd_1365257] using wordTrace_append hprefix tailTrace_1365257
  have hstable : (prefixWord ++ tailWord_1365257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365257).length < 2 ^ (prefixWord ++ tailWord_1365257).sum := by decide
  have hdescent : baseEnd_1365257 < baseStart_1365257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365288 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1365288 : Nat := 118140960795 + 1365288 * 2 ^ 59
def prefixEnd_1365288 : Nat := 4983230072969 + 3 ^ 40 * 1365288 * 2
def baseEnd_1365288 : Nat := 701048975815759538121161

theorem tailTrace_1365288 : CollatzResearch.WordTrace tailWord_1365288 prefixEnd_1365288 701048975815759538121161 := by
  unfold tailWord_1365288
  simp only [CollatzResearch.WordTrace]
  refine ⟨24898072138901111735844259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33197429518534815647792345 24898072138901111735844259)
  ·
    refine ⟨37347108208351667603766389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24898072138901111735844259 37347108208351667603766389)
    ·
      refine ⟨3501291394532968837853099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37347108208351667603766389 3501291394532968837853099)
      ·
        refine ⟨5251937091799453256779649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501291394532968837853099 5251937091799453256779649)
        ·
          refine ⟨3938952818849589942584737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5251937091799453256779649 3938952818849589942584737)
          ·
            refine ⟨2954214614137192456938553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3938952818849589942584737 2954214614137192456938553)
            ·
              refine ⟨2215660960602894342703915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954214614137192456938553 2215660960602894342703915)
              ·
                refine ⟨3323491440904341514055873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215660960602894342703915 3323491440904341514055873)
                ·
                  refine ⟨2492618580678256135541905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3323491440904341514055873 2492618580678256135541905)
                  ·
                    refine ⟨1869463935508692101656429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2492618580678256135541905 1869463935508692101656429)
                    ·
                      refine ⟨701048975815759538121161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869463935508692101656429 701048975815759538121161)
                      ·
                        rfl

theorem cell23_1365288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1365288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365288 prefixEnd_1365288 := by exact prefixLift 1365288
  have htrace : WordTrace (prefixWord ++ tailWord_1365288) baseStart_1365288 baseEnd_1365288 := by
    simpa [prefixWord, tailWord_1365288, baseEnd_1365288] using wordTrace_append hprefix tailTrace_1365288
  have hstable : (prefixWord ++ tailWord_1365288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365288).length < 2 ^ (prefixWord ++ tailWord_1365288).sum := by decide
  have hdescent : baseEnd_1365288 < baseStart_1365288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365352 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1365352 : Nat := 118140960795 + 1365352 * 2 ^ 59
def prefixEnd_1365352 : Nat := 4983230072969 + 3 ^ 40 * 1365352 * 2
def baseEnd_1365352 : Nat := 701081838577647287720867

theorem tailTrace_1365352 : CollatzResearch.WordTrace tailWord_1365352 prefixEnd_1365352 701081838577647287720867 := by
  unfold tailWord_1365352
  simp only [CollatzResearch.WordTrace]
  refine ⟨24899239274785181201009155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33198985699713574934678873 24899239274785181201009155)
  ·
    refine ⟨37348858912177771801513733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24899239274785181201009155 37348858912177771801513733)
    ·
      refine ⟨7002911046033332212783825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37348858912177771801513733 7002911046033332212783825)
      ·
        refine ⟨5252183284524999159587869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7002911046033332212783825 5252183284524999159587869)
        ·
          refine ⟨1969568731696874684845451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5252183284524999159587869 1969568731696874684845451)
          ·
            refine ⟨2954353097545312027268177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969568731696874684845451 2954353097545312027268177)
            ·
              refine ⟨2215764823158984020451133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954353097545312027268177 2215764823158984020451133)
              ·
                refine ⟨830911808684619007669175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2215764823158984020451133 830911808684619007669175)
                ·
                  refine ⟨1246367713026928511503763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830911808684619007669175 1246367713026928511503763)
                  ·
                    refine ⟨1869551569540392767255645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246367713026928511503763 1869551569540392767255645)
                    ·
                      refine ⟨701081838577647287720867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869551569540392767255645 701081838577647287720867)
                      ·
                        rfl

theorem cell23_1365352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1365352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365352 prefixEnd_1365352 := by exact prefixLift 1365352
  have htrace : WordTrace (prefixWord ++ tailWord_1365352) baseStart_1365352 baseEnd_1365352 := by
    simpa [prefixWord, tailWord_1365352, baseEnd_1365352] using wordTrace_append hprefix tailTrace_1365352
  have hstable : (prefixWord ++ tailWord_1365352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365352).length < 2 ^ (prefixWord ++ tailWord_1365352).sum := by decide
  have hdescent : baseEnd_1365352 < baseStart_1365352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365378 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1365378 : Nat := 118140960795 + 1365378 * 2 ^ 59
def prefixEnd_1365378 : Nat := 4983230072969 + 3 ^ 40 * 1365378 * 2
def baseEnd_1365378 : Nat := 701095189074664185995747

theorem tailTrace_1365378 : CollatzResearch.WordTrace tailWord_1365378 prefixEnd_1365378 701095189074664185995747 := by
  unfold tailWord_1365378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12449856711869042210616197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33199617898317445894976525 12449856711869042210616197)
  ·
    refine ⟨2334348133475445414490537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12449856711869042210616197 2334348133475445414490537)
    ·
      refine ⟨1750761100106584060867903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334348133475445414490537 1750761100106584060867903)
      ·
        refine ⟨2626141650159876091301855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750761100106584060867903 2626141650159876091301855)
        ·
          refine ⟨3939212475239814136952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626141650159876091301855 3939212475239814136952783)
          ·
            refine ⟨5908818712859721205429175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939212475239814136952783 5908818712859721205429175)
            ·
              refine ⟨8863228069289581808143763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908818712859721205429175 8863228069289581808143763)
              ·
                refine ⟨13294842103934372712215645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8863228069289581808143763 13294842103934372712215645)
                ·
                  refine ⟨4985565788975389767080867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13294842103934372712215645 4985565788975389767080867)
                  ·
                    refine ⟨7478348683463084650621301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4985565788975389767080867 7478348683463084650621301)
                    ·
                      refine ⟨701095189074664185995747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7478348683463084650621301 701095189074664185995747)
                      ·
                        rfl

theorem cell23_1365378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1365378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365378 prefixEnd_1365378 := by exact prefixLift 1365378
  have htrace : WordTrace (prefixWord ++ tailWord_1365378) baseStart_1365378 baseEnd_1365378 := by
    simpa [prefixWord, tailWord_1365378, baseEnd_1365378] using wordTrace_append hprefix tailTrace_1365378
  have hstable : (prefixWord ++ tailWord_1365378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365378).length < 2 ^ (prefixWord ++ tailWord_1365378).sum := by decide
  have hdescent : baseEnd_1365378 < baseStart_1365378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365385 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 2, 4]
def baseStart_1365385 : Nat := 118140960795 + 1365385 * 2 ^ 59
def prefixEnd_1365385 : Nat := 4983230072969 + 3 ^ 40 * 1365385 * 2
def baseEnd_1365385 : Nat := 233699594479748552869405

theorem tailTrace_1365385 : CollatzResearch.WordTrace tailWord_1365385 prefixEnd_1365385 233699594479748552869405 := by
  unfold tailWord_1365385
  simp only [CollatzResearch.WordTrace]
  refine ⟨49799682158450809037969609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33199788105633872691979739 49799682158450809037969609)
  ·
    refine ⟨37349761618838106778477207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49799682158450809037969609 37349761618838106778477207)
    ·
      refine ⟨56024642428257160167715811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37349761618838106778477207 56024642428257160167715811)
      ·
        refine ⟨84036963642385740251573717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56024642428257160167715811 84036963642385740251573717)
        ·
          refine ⟨1969616335368415787146259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84036963642385740251573717 1969616335368415787146259)
          ·
            refine ⟨2954424503052623680719389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969616335368415787146259 2954424503052623680719389)
            ·
              refine ⟨1107909188644733880269771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2954424503052623680719389 1107909188644733880269771)
              ·
                refine ⟨1661863782967100820404657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107909188644733880269771 1661863782967100820404657)
                ·
                  refine ⟨1246397837225325615303493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1661863782967100820404657 1246397837225325615303493)
                  ·
                    refine ⟨233699594479748552869405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246397837225325615303493 233699594479748552869405)
                    ·
                      rfl

theorem cell23_1365385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_1365385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365385 prefixEnd_1365385 := by exact prefixLift 1365385
  have htrace : WordTrace (prefixWord ++ tailWord_1365385) baseStart_1365385 baseEnd_1365385 := by
    simpa [prefixWord, tailWord_1365385, baseEnd_1365385] using wordTrace_append hprefix tailTrace_1365385
  have hstable : (prefixWord ++ tailWord_1365385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365385).length < 2 ^ (prefixWord ++ tailWord_1365385).sum := by decide
  have hdescent : baseEnd_1365385 < baseStart_1365385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365424 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_1365424 : Nat := 118140960795 + 1365424 * 2 ^ 59
def prefixEnd_1365424 : Nat := 4983230072969 + 3 ^ 40 * 1365424 * 2
def baseEnd_1365424 : Nat := 233706269728257002006845

theorem tailTrace_1365424 : CollatzResearch.WordTrace tailWord_1365424 prefixEnd_1365424 233706269728257002006845 := by
  unfold tailWord_1365424
  simp only [CollatzResearch.WordTrace]
  refine ⟨24900552302654759349319663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33200736403539679132426217 24900552302654759349319663)
  ·
    refine ⟨37350828453982139023979495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24900552302654759349319663 37350828453982139023979495)
    ·
      refine ⟨56026242680973208535969243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37350828453982139023979495 56026242680973208535969243)
      ·
        refine ⟨84039364021459812803953865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56026242680973208535969243 84039364021459812803953865)
        ·
          refine ⟨63029523016094859602965399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84039364021459812803953865 63029523016094859602965399)
          ·
            refine ⟨94544284524142289404448099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63029523016094859602965399 94544284524142289404448099)
            ·
              refine ⟨141816426786213434106672149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94544284524142289404448099 141816426786213434106672149)
              ·
                refine ⟨6647645005603754723750257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141816426786213434106672149 6647645005603754723750257)
                ·
                  refine ⟨4985733754202816042812693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6647645005603754723750257 4985733754202816042812693)
                  ·
                    refine ⟨233706269728257002006845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4985733754202816042812693 233706269728257002006845)
                    ·
                      rfl

theorem cell23_1365424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_1365424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365424 prefixEnd_1365424 := by exact prefixLift 1365424
  have htrace : WordTrace (prefixWord ++ tailWord_1365424) baseStart_1365424 baseEnd_1365424 := by
    simpa [prefixWord, tailWord_1365424, baseEnd_1365424] using wordTrace_append hprefix tailTrace_1365424
  have hstable : (prefixWord ++ tailWord_1365424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365424).length < 2 ^ (prefixWord ++ tailWord_1365424).sum := by decide
  have hdescent : baseEnd_1365424 < baseStart_1365424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365448 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_1365448 : Nat := 118140960795 + 1365448 * 2 ^ 59
def prefixEnd_1365448 : Nat := 4983230072969 + 3 ^ 40 * 1365448 * 2
def baseEnd_1365448 : Nat := 701131132720478912120425

theorem tailTrace_1365448 : CollatzResearch.WordTrace tailWord_1365448 prefixEnd_1365448 701131132720478912120425 := by
  unfold tailWord_1365448
  simp only [CollatzResearch.WordTrace]
  refine ⟨24900989978611285398756499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33201319971481713865008665 24900989978611285398756499)
  ·
    refine ⟨37351484967916928098134749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24900989978611285398756499 37351484967916928098134749)
    ·
      refine ⟨14006806862968848036800531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37351484967916928098134749 14006806862968848036800531)
      ·
        refine ⟨21010210294453272055200797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14006806862968848036800531 21010210294453272055200797)
        ·
          refine ⟨7878828860419977020700299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21010210294453272055200797 7878828860419977020700299)
          ·
            refine ⟨11818243290629965531050449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7878828860419977020700299 11818243290629965531050449)
            ·
              refine ⟨8863682467972474148287837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11818243290629965531050449 8863682467972474148287837)
              ·
                refine ⟨3323880925489677805607939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8863682467972474148287837 3323880925489677805607939)
                ·
                  refine ⟨4985821388234516708411909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323880925489677805607939 4985821388234516708411909)
                  ·
                    refine ⟨934841510293971882827233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4985821388234516708411909 934841510293971882827233)
                    ·
                      refine ⟨701131132720478912120425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934841510293971882827233 701131132720478912120425)
                      ·
                        rfl

theorem cell23_1365448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_1365448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365448 prefixEnd_1365448 := by exact prefixLift 1365448
  have htrace : WordTrace (prefixWord ++ tailWord_1365448) baseStart_1365448 baseEnd_1365448 := by
    simpa [prefixWord, tailWord_1365448, baseEnd_1365448] using wordTrace_append hprefix tailTrace_1365448
  have hstable : (prefixWord ++ tailWord_1365448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365448).length < 2 ^ (prefixWord ++ tailWord_1365448).sum := by decide
  have hdescent : baseEnd_1365448 < baseStart_1365448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365452 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1365452 : Nat := 118140960795 + 1365452 * 2 ^ 59
def prefixEnd_1365452 : Nat := 4983230072969 + 3 ^ 40 * 1365452 * 2
def baseEnd_1365452 : Nat := 701133186643096896470407

theorem tailTrace_1365452 : CollatzResearch.WordTrace tailWord_1365452 prefixEnd_1365452 701133186643096896470407 := by
  unfold tailWord_1365452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24901062924604039740329305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33201417232805386320439073 24901062924604039740329305)
  ·
    refine ⟨18675797193453029805246979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24901062924604039740329305 18675797193453029805246979)
    ·
      refine ⟨28013695790179544707870469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18675797193453029805246979 28013695790179544707870469)
      ·
        refine ⟨5252567960658664632725713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28013695790179544707870469 5252567960658664632725713)
        ·
          refine ⟨3939425970493998474544285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252567960658664632725713 3939425970493998474544285)
          ·
            refine ⟨1477284738935249427954107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3939425970493998474544285 1477284738935249427954107)
            ·
              refine ⟨2215927108402874141931161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477284738935249427954107 2215927108402874141931161)
              ·
                refine ⟨1661945331302155606448371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215927108402874141931161 1661945331302155606448371)
                ·
                  refine ⟨2492917996953233409672557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661945331302155606448371 2492917996953233409672557)
                  ·
                    refine ⟨934844248857462528627209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2492917996953233409672557 934844248857462528627209)
                    ·
                      refine ⟨701133186643096896470407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 934844248857462528627209 701133186643096896470407)
                      ·
                        rfl

theorem cell23_1365452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1365452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365452 prefixEnd_1365452 := by exact prefixLift 1365452
  have htrace : WordTrace (prefixWord ++ tailWord_1365452) baseStart_1365452 baseEnd_1365452 := by
    simpa [prefixWord, tailWord_1365452, baseEnd_1365452] using wordTrace_append hprefix tailTrace_1365452
  have hstable : (prefixWord ++ tailWord_1365452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365452).length < 2 ^ (prefixWord ++ tailWord_1365452).sum := by decide
  have hdescent : baseEnd_1365452 < baseStart_1365452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365488 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 5]
def baseStart_1365488 : Nat := 118140960795 + 1365488 * 2 ^ 59
def prefixEnd_1365488 : Nat := 4983230072969 + 3 ^ 40 * 1365488 * 2
def baseEnd_1365488 : Nat := 77905741327406528402249

theorem tailTrace_1365488 : CollatzResearch.WordTrace tailWord_1365488 prefixEnd_1365488 77905741327406528402249 := by
  unfold tailWord_1365488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24901719438538828814484559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33202292584718438419312745 24901719438538828814484559)
  ·
    refine ⟨37352579157808243221726839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24901719438538828814484559 37352579157808243221726839)
    ·
      refine ⟨56028868736712364832590259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37352579157808243221726839 56028868736712364832590259)
      ·
        refine ⟨84043303105068547248885389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56028868736712364832590259 84043303105068547248885389)
        ·
          refine ⟨31516238664400705218332021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84043303105068547248885389 31516238664400705218332021)
          ·
            refine ⟨2954647374787566114218627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31516238664400705218332021 2954647374787566114218627)
            ·
              refine ⟨4431971062181349171327941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954647374787566114218627 4431971062181349171327941)
              ·
                refine ⟨830994574159002969623989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4431971062181349171327941 830994574159002969623989)
                ·
                  refine ⟨77905741327406528402249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830994574159002969623989 77905741327406528402249)
                  ·
                    rfl

theorem cell23_1365488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 5].length) (baseStart_1365488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365488 prefixEnd_1365488 := by exact prefixLift 1365488
  have htrace : WordTrace (prefixWord ++ tailWord_1365488) baseStart_1365488 baseEnd_1365488 := by
    simpa [prefixWord, tailWord_1365488, baseEnd_1365488] using wordTrace_append hprefix tailTrace_1365488
  have hstable : (prefixWord ++ tailWord_1365488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365488).length < 2 ^ (prefixWord ++ tailWord_1365488).sum := by decide
  have hdescent : baseEnd_1365488 < baseStart_1365488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365518 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1365518 : Nat := 118140960795 + 1365518 * 2 ^ 59
def prefixEnd_1365518 : Nat := 4983230072969 + 3 ^ 40 * 1365518 * 2
def baseEnd_1365518 : Nat := 233722358788764546081701

theorem tailTrace_1365518 : CollatzResearch.WordTrace tailWord_1365518 prefixEnd_1365518 233722358788764546081701 := by
  unfold tailWord_1365518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225566633371121594070151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33203022044645981835040805 6225566633371121594070151)
  ·
    refine ⟨9338349950056682391105227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6225566633371121594070151 9338349950056682391105227)
    ·
      refine ⟨14007524925085023586657841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9338349950056682391105227 14007524925085023586657841)
      ·
        refine ⟨10505643693813767689993381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14007524925085023586657841 10505643693813767689993381)
        ·
          refine ⟨1969808192590081441873759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10505643693813767689993381 1969808192590081441873759)
          ·
            refine ⟨2954712288885122162810639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969808192590081441873759 2954712288885122162810639)
            ·
              refine ⟨4432068433327683244215959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954712288885122162810639 4432068433327683244215959)
              ·
                refine ⟨6648102649991524866323939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432068433327683244215959 6648102649991524866323939)
                ·
                  refine ⟨9972153974987287299485909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648102649991524866323939 9972153974987287299485909)
                  ·
                    refine ⟨233722358788764546081701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9972153974987287299485909 233722358788764546081701)
                    ·
                      rfl

theorem cell23_1365518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1365518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365518 prefixEnd_1365518 := by exact prefixLift 1365518
  have htrace : WordTrace (prefixWord ++ tailWord_1365518) baseStart_1365518 baseEnd_1365518 := by
    simpa [prefixWord, tailWord_1365518, baseEnd_1365518] using wordTrace_append hprefix tailTrace_1365518
  have hstable : (prefixWord ++ tailWord_1365518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365518).length < 2 ^ (prefixWord ++ tailWord_1365518).sum := by decide
  have hdescent : baseEnd_1365518 < baseStart_1365518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365521 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_1365521 : Nat := 118140960795 + 1365521 * 2 ^ 59
def prefixEnd_1365521 : Nat := 4983230072969 + 3 ^ 40 * 1365521 * 2
def baseEnd_1365521 : Nat := 701168616808257126507589

theorem tailTrace_1365521 : CollatzResearch.WordTrace tailWord_1365521 prefixEnd_1365521 701168616808257126507589 := by
  unfold tailWord_1365521
  simp only [CollatzResearch.WordTrace]
  refine ⟨49804642485958104264920417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33203094990638736176613611 49804642485958104264920417)
  ·
    refine ⟨37353481864468578198690313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49804642485958104264920417 37353481864468578198690313)
    ·
      refine ⟨28015111398351433649017735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37353481864468578198690313 28015111398351433649017735)
      ·
        refine ⟨42022667097527150473526603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28015111398351433649017735 42022667097527150473526603)
        ·
          refine ⟨63034000646290725710289905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42022667097527150473526603 63034000646290725710289905)
          ·
            refine ⟨47275500484718044282717429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63034000646290725710289905 47275500484718044282717429)
            ·
              refine ⟨4432078170442316651504759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47275500484718044282717429 4432078170442316651504759)
              ·
                refine ⟨6648117255663474977257139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432078170442316651504759 6648117255663474977257139)
                ·
                  refine ⟨9972175883495212465885709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648117255663474977257139 9972175883495212465885709)
                  ·
                    refine ⟨3739565956310704674707141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9972175883495212465885709 3739565956310704674707141)
                    ·
                      refine ⟨701168616808257126507589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3739565956310704674707141 701168616808257126507589)
                      ·
                        rfl

theorem cell23_1365521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_1365521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365521 prefixEnd_1365521 := by exact prefixLift 1365521
  have htrace : WordTrace (prefixWord ++ tailWord_1365521) baseStart_1365521 baseEnd_1365521 := by
    simpa [prefixWord, tailWord_1365521, baseEnd_1365521] using wordTrace_append hprefix tailTrace_1365521
  have hstable : (prefixWord ++ tailWord_1365521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365521).length < 2 ^ (prefixWord ++ tailWord_1365521).sum := by decide
  have hdescent : baseEnd_1365521 < baseStart_1365521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365538 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1365538 : Nat := 118140960795 + 1365538 * 2 ^ 59
def prefixEnd_1365538 : Nat := 4983230072969 + 3 ^ 40 * 1365538 * 2
def baseEnd_1365538 : Nat := 701177345979383559995011

theorem tailTrace_1365538 : CollatzResearch.WordTrace tailWord_1365538 prefixEnd_1365538 701177345979383559995011 := by
  unfold tailWord_1365538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451315631724129042072317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33203508351264344112192845 12451315631724129042072317)
  ·
    refine ⟨4669243361896548390777119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12451315631724129042072317 4669243361896548390777119)
    ·
      refine ⟨7003865042844822586165679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669243361896548390777119 7003865042844822586165679)
      ·
        refine ⟨10505797564267233879248519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7003865042844822586165679 10505797564267233879248519)
        ·
          refine ⟨15758696346400850818872779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505797564267233879248519 15758696346400850818872779)
          ·
            refine ⟨23638044519601276228309169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15758696346400850818872779 23638044519601276228309169)
            ·
              refine ⟨17728533389700957171231877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23638044519601276228309169 17728533389700957171231877)
              ·
                refine ⟨3324100010568929469605977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17728533389700957171231877 3324100010568929469605977)
                ·
                  refine ⟨2493075007926697102204483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324100010568929469605977 2493075007926697102204483)
                  ·
                    refine ⟨3739612511890045653306725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493075007926697102204483 3739612511890045653306725)
                    ·
                      refine ⟨701177345979383559995011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3739612511890045653306725 701177345979383559995011)
                      ·
                        rfl

theorem cell23_1365538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1365538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365538 prefixEnd_1365538 := by exact prefixLift 1365538
  have htrace : WordTrace (prefixWord ++ tailWord_1365538) baseStart_1365538 baseEnd_1365538 := by
    simpa [prefixWord, tailWord_1365538, baseEnd_1365538] using wordTrace_append hprefix tailTrace_1365538
  have hstable : (prefixWord ++ tailWord_1365538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365538).length < 2 ^ (prefixWord ++ tailWord_1365538).sum := by decide
  have hdescent : baseEnd_1365538 < baseStart_1365538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365642 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_1365642 : Nat := 118140960795 + 1365642 * 2 ^ 59
def prefixEnd_1365642 : Nat := 4983230072969 + 3 ^ 40 * 1365642 * 2
def baseEnd_1365642 : Nat := 233743582655817051031511

theorem tailTrace_1365642 : CollatzResearch.WordTrace tailWord_1365642 prefixEnd_1365642 233743582655817051031511 := by
  unfold tailWord_1365642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452263929629935482518795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33206037145679827953383453 12452263929629935482518795)
  ·
    refine ⟨18678395894444903223778193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452263929629935482518795 18678395894444903223778193)
    ·
      refine ⟨14008796920833677417833645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18678395894444903223778193 14008796920833677417833645)
      ·
        refine ⟨5253298845312629031687617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14008796920833677417833645 5253298845312629031687617)
        ·
          refine ⟨3939974133984471773765713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253298845312629031687617 3939974133984471773765713)
          ·
            refine ⟨2954980600488353830324285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939974133984471773765713 2954980600488353830324285)
            ·
              refine ⟨1108117725183132686371607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2954980600488353830324285 1108117725183132686371607)
              ·
                refine ⟨1662176587774699029557411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108117725183132686371607 1662176587774699029557411)
                ·
                  refine ⟨2493264881662048544336117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662176587774699029557411 2493264881662048544336117)
                  ·
                    refine ⟨233743582655817051031511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2493264881662048544336117 233743582655817051031511)
                    ·
                      rfl

theorem cell23_1365642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_1365642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365642 prefixEnd_1365642 := by exact prefixLift 1365642
  have htrace : WordTrace (prefixWord ++ tailWord_1365642) baseStart_1365642 baseEnd_1365642 := by
    simpa [prefixWord, tailWord_1365642, baseEnd_1365642] using wordTrace_append hprefix tailTrace_1365642
  have hstable : (prefixWord ++ tailWord_1365642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365642).length < 2 ^ (prefixWord ++ tailWord_1365642).sum := by decide
  have hdescent : baseEnd_1365642 < baseStart_1365642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365655 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 2, 4]
def baseStart_1365655 : Nat := 118140960795 + 1365655 * 2 ^ 59
def prefixEnd_1365655 : Nat := 4983230072969 + 3 ^ 40 * 1365655 * 2
def baseEnd_1365655 : Nat := 233745807738653200743991

theorem tailTrace_1365655 : CollatzResearch.WordTrace tailWord_1365655 prefixEnd_1365655 233745807738653200743991 := by
  unfold tailWord_1365655
  simp only [CollatzResearch.WordTrace]
  refine ⟨49809529867472645150298419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33206353244981763433532279 49809529867472645150298419)
  ·
    refine ⟨74714294801208967725447629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49809529867472645150298419 74714294801208967725447629)
    ·
      refine ⟨28017860550453362897042861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74714294801208967725447629 28017860550453362897042861)
      ·
        refine ⟨10506697706420011086391073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28017860550453362897042861 10506697706420011086391073)
        ·
          refine ⟨7880023279815008314793305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10506697706420011086391073 7880023279815008314793305)
          ·
            refine ⟨5910017459861256236094979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7880023279815008314793305 5910017459861256236094979)
            ·
              refine ⟨8865026189791884354142469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910017459861256236094979 8865026189791884354142469)
              ·
                refine ⟨1662192410585978316401713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8865026189791884354142469 1662192410585978316401713)
                ·
                  refine ⟨1246644307939483737301285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1662192410585978316401713 1246644307939483737301285)
                  ·
                    refine ⟨233745807738653200743991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246644307939483737301285 233745807738653200743991)
                    ·
                      rfl

theorem cell23_1365655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_1365655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365655 prefixEnd_1365655 := by exact prefixLift 1365655
  have htrace : WordTrace (prefixWord ++ tailWord_1365655) baseStart_1365655 baseEnd_1365655 := by
    simpa [prefixWord, tailWord_1365655, baseEnd_1365655] using wordTrace_append hprefix tailTrace_1365655
  have hstable : (prefixWord ++ tailWord_1365655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365655).length < 2 ^ (prefixWord ++ tailWord_1365655).sum := by decide
  have hdescent : baseEnd_1365655 < baseStart_1365655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365656 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1365656 : Nat := 118140960795 + 1365656 * 2 ^ 59
def prefixEnd_1365656 : Nat := 4983230072969 + 3 ^ 40 * 1365656 * 2
def baseEnd_1365656 : Nat := 701237936696614098319469

theorem tailTrace_1365656 : CollatzResearch.WordTrace tailWord_1365656 prefixEnd_1365656 701237936696614098319469 := by
  unfold tailWord_1365656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24904783170234511160542411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33206377560312681547389881 24904783170234511160542411)
  ·
    refine ⟨37357174755351766740813617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24904783170234511160542411 37357174755351766740813617)
    ·
      refine ⟨28017881066513825055610213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37357174755351766740813617 28017881066513825055610213)
      ·
        refine ⟨5253352699971342197926915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28017881066513825055610213 5253352699971342197926915)
        ·
          refine ⟨7880029049957013296890373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253352699971342197926915 7880029049957013296890373)
          ·
            refine ⟨1477505446866939993166945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7880029049957013296890373 1477505446866939993166945)
            ·
              refine ⟨1108129085150204994875209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477505446866939993166945 1108129085150204994875209)
              ·
                refine ⟨831096813862653746156407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108129085150204994875209 831096813862653746156407)
                ·
                  refine ⟨1246645220793980619234611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831096813862653746156407 1246645220793980619234611)
                  ·
                    refine ⟨1869967831190970928851917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246645220793980619234611 1869967831190970928851917)
                    ·
                      refine ⟨701237936696614098319469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869967831190970928851917 701237936696614098319469)
                      ·
                        rfl

theorem cell23_1365656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1365656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365656 prefixEnd_1365656 := by exact prefixLift 1365656
  have htrace : WordTrace (prefixWord ++ tailWord_1365656) baseStart_1365656 baseEnd_1365656 := by
    simpa [prefixWord, tailWord_1365656, baseEnd_1365656] using wordTrace_append hprefix tailTrace_1365656
  have hstable : (prefixWord ++ tailWord_1365656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365656).length < 2 ^ (prefixWord ++ tailWord_1365656).sum := by decide
  have hdescent : baseEnd_1365656 < baseStart_1365656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
