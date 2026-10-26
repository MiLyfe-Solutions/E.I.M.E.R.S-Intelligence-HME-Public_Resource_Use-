import V185TrunkScan21Chunk030

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_375429 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_375429 : Nat := 118140960795 + 375429 * 2 ^ 59
def prefixEnd_375429 : Nat := 4983230072969 + 3 ^ 40 * 375429 * 2
def baseEnd_375429 : Nat := 85678012727518607115973

theorem tailTrace_375429 : CollatzResearch.WordTrace tailWord_375429 prefixEnd_375429 85678012727518607115973 := by
  unfold tailWord_375429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13693020556892326013601341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9128680371261550675734227 13693020556892326013601341)
  ·
    refine ⟨5134882708834622255100503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13693020556892326013601341 5134882708834622255100503)
    ·
      refine ⟨7702324063251933382650755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134882708834622255100503 7702324063251933382650755)
      ·
        refine ⟨11553486094877900073976133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7702324063251933382650755 11553486094877900073976133)
        ·
          refine ⟨2166278642789606263870525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11553486094877900073976133 2166278642789606263870525)
          ·
            refine ⟨812354491046102348951447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2166278642789606263870525 812354491046102348951447)
            ·
              refine ⟨1218531736569153523427171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812354491046102348951447 1218531736569153523427171)
              ·
                refine ⟨1827797604853730285140757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218531736569153523427171 1827797604853730285140757)
                ·
                  refine ⟨85678012727518607115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1827797604853730285140757 85678012727518607115973)
                  ·
                    rfl

theorem cell21_375429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_375429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375429 prefixEnd_375429 := by exact prefixLift 375429
  have htrace : WordTrace (prefixWord ++ tailWord_375429) baseStart_375429 baseEnd_375429 := by
    simpa [prefixWord, tailWord_375429, baseEnd_375429] using wordTrace_append hprefix tailTrace_375429
  have hstable : (prefixWord ++ tailWord_375429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375429).length < 2 ^ (prefixWord ++ tailWord_375429).sum := by decide
  have hdescent : baseEnd_375429 < baseStart_375429 := by decide
  rcases family_descends (prefixWord ++ tailWord_375429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375505 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_375505 : Nat := 118140960795 + 375505 * 2 ^ 59
def prefixEnd_375505 : Nat := 4983230072969 + 3 ^ 40 * 375505 * 2
def baseEnd_375505 : Nat := 85695356962959363849151

theorem tailTrace_375505 : CollatzResearch.WordTrace tailWord_375505 prefixEnd_375505 85695356962959363849151 := by
  unfold tailWord_375505
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695792504616990993367969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9130528336411327328911979 13695792504616990993367969)
  ·
    refine ⟨10271844378462743245025977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13695792504616990993367969 10271844378462743245025977)
    ·
      refine ⟨7703883283847057433769483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10271844378462743245025977 7703883283847057433769483)
      ·
        refine ⟨11555824925770586150654225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703883283847057433769483 11555824925770586150654225)
        ·
          refine ⟨8666868694327939612990669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11555824925770586150654225 8666868694327939612990669)
          ·
            refine ⟨3250075760372977354871501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8666868694327939612990669 3250075760372977354871501)
            ·
              refine ⟨1218778410139866508076813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3250075760372977354871501 1218778410139866508076813)
              ·
                refine ⟨457041903802449940528805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218778410139866508076813 457041903802449940528805)
                ·
                  refine ⟨85695356962959363849151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457041903802449940528805 85695356962959363849151)
                  ·
                    rfl

theorem cell21_375505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_375505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375505 prefixEnd_375505 := by exact prefixLift 375505
  have htrace : WordTrace (prefixWord ++ tailWord_375505) baseStart_375505 baseEnd_375505 := by
    simpa [prefixWord, tailWord_375505, baseEnd_375505] using wordTrace_append hprefix tailTrace_375505
  have hstable : (prefixWord ++ tailWord_375505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375505).length < 2 ^ (prefixWord ++ tailWord_375505).sum := by decide
  have hdescent : baseEnd_375505 < baseStart_375505 := by decide
  rcases family_descends (prefixWord ++ tailWord_375505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375519 : List Nat := [1, 1, 2, 3, 2, 3, 2, 7]
def baseStart_375519 : Nat := 118140960795 + 375519 * 2 ^ 59
def prefixEnd_375519 : Nat := 4983230072969 + 3 ^ 40 * 375519 * 2
def baseEnd_375519 : Nat := 28566183984566150205263

theorem tailTrace_375519 : CollatzResearch.WordTrace tailWord_375519 prefixEnd_375519 28566183984566150205263 := by
  unfold tailWord_375519
  simp only [CollatzResearch.WordTrace]
  refine ⟨13696303126566271384377611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9130868751044180922918407 13696303126566271384377611)
  ·
    refine ⟨20544454689849407076566417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13696303126566271384377611 20544454689849407076566417)
    ·
      refine ⟨15408341017387055307424813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20544454689849407076566417 15408341017387055307424813)
      ·
        refine ⟨5778127881520145740284305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15408341017387055307424813 5778127881520145740284305)
        ·
          refine ⟨4333595911140109305213229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5778127881520145740284305 4333595911140109305213229)
          ·
            refine ⟨1625098466677540989454961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4333595911140109305213229 1625098466677540989454961)
            ·
              refine ⟨1218823850008155742091221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625098466677540989454961 1218823850008155742091221)
              ·
                refine ⟨28566183984566150205263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1218823850008155742091221 28566183984566150205263)
                ·
                  rfl

theorem cell21_375519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_375519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375519 prefixEnd_375519 := by exact prefixLift 375519
  have htrace : WordTrace (prefixWord ++ tailWord_375519) baseStart_375519 baseEnd_375519 := by
    simpa [prefixWord, tailWord_375519, baseEnd_375519] using wordTrace_append hprefix tailTrace_375519
  have hstable : (prefixWord ++ tailWord_375519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375519).length < 2 ^ (prefixWord ++ tailWord_375519).sum := by decide
  have hdescent : baseEnd_375519 < baseStart_375519 := by decide
  rcases family_descends (prefixWord ++ tailWord_375519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375564 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_375564 : Nat := 118140960795 + 375564 * 2 ^ 59
def prefixEnd_375564 : Nat := 4983230072969 + 3 ^ 40 * 375564 * 2
def baseEnd_375564 : Nat := 85708821566788372365697

theorem tailTrace_375564 : CollatzResearch.WordTrace tailWord_375564 prefixEnd_375564 85708821566788372365697 := by
  unfold tailWord_375564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848972205701622034882873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9131962940935496046510497 6848972205701622034882873)
  ·
    refine ⟨5136729154276216526162155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6848972205701622034882873 5136729154276216526162155)
    ·
      refine ⟨7705093731414324789243233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5136729154276216526162155 7705093731414324789243233)
      ·
        refine ⟨5778820298560743591932425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7705093731414324789243233 5778820298560743591932425)
        ·
          refine ⟨4334115223920557693949319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5778820298560743591932425 4334115223920557693949319)
          ·
            refine ⟨6501172835880836540923979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334115223920557693949319 6501172835880836540923979)
            ·
              refine ⟨9751759253821254811385969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501172835880836540923979 9751759253821254811385969)
              ·
                refine ⟨7313819440365941108539477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9751759253821254811385969 7313819440365941108539477)
                ·
                  refine ⟨85708821566788372365697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7313819440365941108539477 85708821566788372365697)
                  ·
                    rfl

theorem cell21_375564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_375564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375564 prefixEnd_375564 := by exact prefixLift 375564
  have htrace : WordTrace (prefixWord ++ tailWord_375564) baseStart_375564 baseEnd_375564 := by
    simpa [prefixWord, tailWord_375564, baseEnd_375564] using wordTrace_append hprefix tailTrace_375564
  have hstable : (prefixWord ++ tailWord_375564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375564).length < 2 ^ (prefixWord ++ tailWord_375564).sum := by decide
  have hdescent : baseEnd_375564 < baseStart_375564 := by decide
  rcases family_descends (prefixWord ++ tailWord_375564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375570 : List Nat := [3, 2, 4, 1, 2, 1, 3, 5]
def baseStart_375570 : Nat := 118140960795 + 375570 * 2 ^ 59
def prefixEnd_375570 : Nat := 4983230072969 + 3 ^ 40 * 375570 * 2
def baseEnd_375570 : Nat := 28570063616177898421895

theorem tailTrace_375570 : CollatzResearch.WordTrace tailWord_375570 prefixEnd_375570 28570063616177898421895 := by
  unfold tailWord_375570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424540812345376773621041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9132108832921004729656109 3424540812345376773621041)
  ·
    refine ⟨2568405609259032580215781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424540812345376773621041 2568405609259032580215781)
    ·
      refine ⟨481576051736068608790459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2568405609259032580215781 481576051736068608790459)
      ·
        refine ⟨722364077604102913185689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481576051736068608790459 722364077604102913185689)
        ·
          refine ⟨541773058203077184889267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722364077604102913185689 541773058203077184889267)
          ·
            refine ⟨812659587304615777333901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541773058203077184889267 812659587304615777333901)
            ·
              refine ⟨304747345239230916500213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812659587304615777333901 304747345239230916500213)
              ·
                refine ⟨28570063616177898421895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304747345239230916500213 28570063616177898421895)
                ·
                  rfl

theorem cell21_375570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_375570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375570 prefixEnd_375570 := by exact prefixLift 375570
  have htrace : WordTrace (prefixWord ++ tailWord_375570) baseStart_375570 baseEnd_375570 := by
    simpa [prefixWord, tailWord_375570, baseEnd_375570] using wordTrace_append hprefix tailTrace_375570
  have hstable : (prefixWord ++ tailWord_375570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375570).length < 2 ^ (prefixWord ++ tailWord_375570).sum := by decide
  have hdescent : baseEnd_375570 < baseStart_375570 := by decide
  rcases family_descends (prefixWord ++ tailWord_375570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375584 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_375584 : Nat := 118140960795 + 375584 * 2 ^ 59
def prefixEnd_375584 : Nat := 4983230072969 + 3 ^ 40 * 375584 * 2
def baseEnd_375584 : Nat := 85713385839272782032323

theorem tailTrace_375584 : CollatzResearch.WordTrace tailWord_375584 prefixEnd_375584 85713385839272782032323 := by
  unfold tailWord_375584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849336935665393742746903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9132449247553858323662537 6849336935665393742746903)
  ·
    refine ⟨10274005403498090614120355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6849336935665393742746903 10274005403498090614120355)
    ·
      refine ⟨15411008105247135921180533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10274005403498090614120355 15411008105247135921180533)
      ·
        refine ⟨1444782009866918992610675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15411008105247135921180533 1444782009866918992610675)
        ·
          refine ⟨2167173014800378488916013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444782009866918992610675 2167173014800378488916013)
          ·
            refine ⟨812689880550141933343505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2167173014800378488916013 812689880550141933343505)
            ·
              refine ⟨609517410412606450007629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812689880550141933343505 609517410412606450007629)
              ·
                refine ⟨228569028904727418752861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609517410412606450007629 228569028904727418752861)
                ·
                  refine ⟨85713385839272782032323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228569028904727418752861 85713385839272782032323)
                  ·
                    rfl

theorem cell21_375584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_375584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375584 prefixEnd_375584 := by exact prefixLift 375584
  have htrace : WordTrace (prefixWord ++ tailWord_375584) baseStart_375584 baseEnd_375584 := by
    simpa [prefixWord, tailWord_375584, baseEnd_375584] using wordTrace_append hprefix tailTrace_375584
  have hstable : (prefixWord ++ tailWord_375584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375584).length < 2 ^ (prefixWord ++ tailWord_375584).sum := by decide
  have hdescent : baseEnd_375584 < baseStart_375584 := by decide
  rcases family_descends (prefixWord ++ tailWord_375584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375598 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_375598 : Nat := 118140960795 + 375598 * 2 ^ 59
def prefixEnd_375598 : Nat := 4983230072969 + 3 ^ 40 * 375598 * 2
def baseEnd_375598 : Nat := 85716580830011868798961

theorem tailTrace_375598 : CollatzResearch.WordTrace tailWord_375598 prefixEnd_375598 85716580830011868798961 := by
  unfold tailWord_375598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712398061660008484562931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9132789662186711917668965 1712398061660008484562931)
  ·
    refine ⟨2568597092490012726844397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1712398061660008484562931 2568597092490012726844397)
    ·
      refine ⟨963223909683754772566649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2568597092490012726844397 963223909683754772566649)
      ·
        refine ⟨722417932262816079424987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963223909683754772566649 722417932262816079424987)
        ·
          refine ⟨1083626898394224119137481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722417932262816079424987 1083626898394224119137481)
          ·
            refine ⟨812720173795668089353111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083626898394224119137481 812720173795668089353111)
            ·
              refine ⟨1219080260693502134029667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812720173795668089353111 1219080260693502134029667)
              ·
                refine ⟨1828620391040253201044501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219080260693502134029667 1828620391040253201044501)
                ·
                  refine ⟨85716580830011868798961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1828620391040253201044501 85716580830011868798961)
                  ·
                    rfl

theorem cell21_375598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_375598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375598 prefixEnd_375598 := by exact prefixLift 375598
  have htrace : WordTrace (prefixWord ++ tailWord_375598) baseStart_375598 baseEnd_375598 := by
    simpa [prefixWord, tailWord_375598, baseEnd_375598] using wordTrace_append hprefix tailTrace_375598
  have hstable : (prefixWord ++ tailWord_375598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375598).length < 2 ^ (prefixWord ++ tailWord_375598).sum := by decide
  have hdescent : baseEnd_375598 < baseStart_375598 := by decide
  rcases family_descends (prefixWord ++ tailWord_375598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375629 : List Nat := [1, 6, 1, 2, 2, 1, 1, 7]
def baseStart_375629 : Nat := 118140960795 + 375629 * 2 ^ 59
def prefixEnd_375629 : Nat := 4983230072969 + 3 ^ 40 * 375629 * 2
def baseEnd_375629 : Nat := 28574551817454234594077

theorem tailTrace_375629 : CollatzResearch.WordTrace tailWord_375629 prefixEnd_375629 28574551817454234594077 := by
  unfold tailWord_375629
  simp only [CollatzResearch.WordTrace]
  refine ⟨13700315156167760170881941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9133543437445173447254627 13700315156167760170881941)
  ·
    refine ⟨642202272945363758010091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13700315156167760170881941 642202272945363758010091)
    ·
      refine ⟨963303409418045637015137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642202272945363758010091 963303409418045637015137)
      ·
        refine ⟨722477557063534227761353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963303409418045637015137 722477557063534227761353)
        ·
          refine ⟨541858167797650670821015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722477557063534227761353 541858167797650670821015)
          ·
            refine ⟨812787251696476006231523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541858167797650670821015 812787251696476006231523)
            ·
              refine ⟨1219180877544714009347285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812787251696476006231523 1219180877544714009347285)
              ·
                refine ⟨28574551817454234594077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1219180877544714009347285 28574551817454234594077)
                ·
                  rfl

theorem cell21_375629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_375629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375629 prefixEnd_375629 := by exact prefixLift 375629
  have htrace : WordTrace (prefixWord ++ tailWord_375629) baseStart_375629 baseEnd_375629 := by
    simpa [prefixWord, tailWord_375629, baseEnd_375629] using wordTrace_append hprefix tailTrace_375629
  have hstable : (prefixWord ++ tailWord_375629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375629).length < 2 ^ (prefixWord ++ tailWord_375629).sum := by decide
  have hdescent : baseEnd_375629 < baseStart_375629 := by decide
  rcases family_descends (prefixWord ++ tailWord_375629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375660 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_375660 : Nat := 118140960795 + 375660 * 2 ^ 59
def prefixEnd_375660 : Nat := 4983230072969 + 3 ^ 40 * 375660 * 2
def baseEnd_375660 : Nat := 85730730074713538765501

theorem tailTrace_375660 : CollatzResearch.WordTrace tailWord_375660 prefixEnd_375660 85730730074713538765501 := by
  unfold tailWord_375660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850722909527726232630217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9134297212703634976840289 6850722909527726232630217)
  ·
    refine ⟨5138042182145794674472663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6850722909527726232630217 5138042182145794674472663)
    ·
      refine ⟨7707063273218692011708995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138042182145794674472663 7707063273218692011708995)
      ·
        refine ⟨11560594909828038017563493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7707063273218692011708995 11560594909828038017563493)
        ·
          refine ⟨2167611545592757128293155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11560594909828038017563493 2167611545592757128293155)
          ·
            refine ⟨3251417318389135692439733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167611545592757128293155 3251417318389135692439733)
            ·
              refine ⟨304820373598981471166225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3251417318389135692439733 304820373598981471166225)
              ·
                refine ⟨228615280199236103374669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304820373598981471166225 228615280199236103374669)
                ·
                  refine ⟨85730730074713538765501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228615280199236103374669 85730730074713538765501)
                  ·
                    rfl

theorem cell21_375660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_375660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375660 prefixEnd_375660 := by exact prefixLift 375660
  have htrace : WordTrace (prefixWord ++ tailWord_375660) baseStart_375660 baseEnd_375660 := by
    simpa [prefixWord, tailWord_375660, baseEnd_375660] using wordTrace_append hprefix tailTrace_375660
  have hstable : (prefixWord ++ tailWord_375660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375660).length < 2 ^ (prefixWord ++ tailWord_375660).sum := by decide
  have hdescent : baseEnd_375660 < baseStart_375660 := by decide
  rcases family_descends (prefixWord ++ tailWord_375660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375733 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_375733 : Nat := 118140960795 + 375733 * 2 ^ 59
def prefixEnd_375733 : Nat := 4983230072969 + 3 ^ 40 * 375733 * 2
def baseEnd_375733 : Nat := 85747389669281634048685

theorem tailTrace_375733 : CollatzResearch.WordTrace tailWord_375733 prefixEnd_375733 85747389669281634048685 := by
  unfold tailWord_375733
  simp only [CollatzResearch.WordTrace]
  refine ⟨13704108347790985932667853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9136072231860657288445235 13704108347790985932667853)
  ·
    refine ⟨5139040630421619724750445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13704108347790985932667853 5139040630421619724750445)
    ·
      refine ⟨1927140236408107396781417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5139040630421619724750445 1927140236408107396781417)
      ·
        refine ⟨1445355177306080547586063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927140236408107396781417 1445355177306080547586063)
        ·
          refine ⟨2168032765959120821379095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445355177306080547586063 2168032765959120821379095)
          ·
            refine ⟨3252049148938681232068643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168032765959120821379095 3252049148938681232068643)
            ·
              refine ⟨4878073723408021848102965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252049148938681232068643 4878073723408021848102965)
              ·
                refine ⟨457319411569502048259653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4878073723408021848102965 457319411569502048259653)
                ·
                  refine ⟨85747389669281634048685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457319411569502048259653 85747389669281634048685)
                  ·
                    rfl

theorem cell21_375733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_375733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375733 prefixEnd_375733 := by exact prefixLift 375733
  have htrace : WordTrace (prefixWord ++ tailWord_375733) baseStart_375733 baseEnd_375733 := by
    simpa [prefixWord, tailWord_375733, baseEnd_375733] using wordTrace_append hprefix tailTrace_375733
  have hstable : (prefixWord ++ tailWord_375733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375733).length < 2 ^ (prefixWord ++ tailWord_375733).sum := by decide
  have hdescent : baseEnd_375733 < baseStart_375733 := by decide
  rcases family_descends (prefixWord ++ tailWord_375733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375761 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_375761 : Nat := 118140960795 + 375761 * 2 ^ 59
def prefixEnd_375761 : Nat := 4983230072969 + 3 ^ 40 * 375761 * 2
def baseEnd_375761 : Nat := 85753779650759807581961

theorem tailTrace_375761 : CollatzResearch.WordTrace tailWord_375761 prefixEnd_375761 85753779650759807581961 := by
  unfold tailWord_375761
  simp only [CollatzResearch.WordTrace]
  refine ⟨13705129591689546714687137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9136753061126364476458091 13705129591689546714687137)
  ·
    refine ⟨10278847193767160036015353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13705129591689546714687137 10278847193767160036015353)
    ·
      refine ⟨7709135395325370027011515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10278847193767160036015353 7709135395325370027011515)
      ·
        refine ⟨11563703092988055040517273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709135395325370027011515 11563703092988055040517273)
        ·
          refine ⟨8672777319741041280387955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11563703092988055040517273 8672777319741041280387955)
          ·
            refine ⟨13009165979611561920581933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672777319741041280387955 13009165979611561920581933)
            ·
              refine ⟨4878437242354335720218225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13009165979611561920581933 4878437242354335720218225)
              ·
                refine ⟨3658827931765751790163669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4878437242354335720218225 3658827931765751790163669)
                ·
                  refine ⟨85753779650759807581961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3658827931765751790163669 85753779650759807581961)
                  ·
                    rfl

theorem cell21_375761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_375761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375761 prefixEnd_375761 := by exact prefixLift 375761
  have htrace : WordTrace (prefixWord ++ tailWord_375761) baseStart_375761 baseEnd_375761 := by
    simpa [prefixWord, tailWord_375761, baseEnd_375761] using wordTrace_append hprefix tailTrace_375761
  have hstable : (prefixWord ++ tailWord_375761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375761).length < 2 ^ (prefixWord ++ tailWord_375761).sum := by decide
  have hdescent : baseEnd_375761 < baseStart_375761 := by decide
  rcases family_descends (prefixWord ++ tailWord_375761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375854 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_375854 : Nat := 118140960795 + 375854 * 2 ^ 59
def prefixEnd_375854 : Nat := 4983230072969 + 3 ^ 40 * 375854 * 2
def baseEnd_375854 : Nat := 85775003517812312531771

theorem tailTrace_375854 : CollatzResearch.WordTrace tailWord_375854 prefixEnd_375854 85775003517812312531771 := by
  unfold tailWord_375854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713565197544077949727827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9139014386901749065215077 1713565197544077949727827)
  ·
    refine ⟨2570347796316116924591741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1713565197544077949727827 2570347796316116924591741)
    ·
      refine ⟨963880423618543846721903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2570347796316116924591741 963880423618543846721903)
      ·
        refine ⟨1445820635427815770082855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963880423618543846721903 1445820635427815770082855)
        ·
          refine ⟨2168730953141723655124283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445820635427815770082855 2168730953141723655124283)
          ·
            refine ⟨3253096429712585482686425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168730953141723655124283 3253096429712585482686425)
            ·
              refine ⟨2439822322284439112014819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253096429712585482686425 2439822322284439112014819)
              ·
                refine ⟨3659733483426658668022229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439822322284439112014819 3659733483426658668022229)
                ·
                  refine ⟨85775003517812312531771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3659733483426658668022229 85775003517812312531771)
                  ·
                    rfl

theorem cell21_375854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_375854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375854 prefixEnd_375854 := by exact prefixLift 375854
  have htrace : WordTrace (prefixWord ++ tailWord_375854) baseStart_375854 baseEnd_375854 := by
    simpa [prefixWord, tailWord_375854, baseEnd_375854] using wordTrace_append hprefix tailTrace_375854
  have hstable : (prefixWord ++ tailWord_375854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375854).length < 2 ^ (prefixWord ++ tailWord_375854).sum := by decide
  have hdescent : baseEnd_375854 < baseStart_375854 := by decide
  rcases family_descends (prefixWord ++ tailWord_375854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375913 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_375913 : Nat := 118140960795 + 375913 * 2 ^ 59
def prefixEnd_375913 : Nat := 4983230072969 + 3 ^ 40 * 375913 * 2
def baseEnd_375913 : Nat := 85788468121641321048317

theorem tailTrace_375913 : CollatzResearch.WordTrace tailWord_375913 prefixEnd_375913 85788468121641321048317 := by
  unfold tailWord_375913
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710673487138876674220393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9140448991425917782813595 13710673487138876674220393)
  ·
    refine ⟨10283005115354157505665295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13710673487138876674220393 10283005115354157505665295)
    ·
      refine ⟨15424507673031236258497943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10283005115354157505665295 15424507673031236258497943)
      ·
        refine ⟨23136761509546854387746915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15424507673031236258497943 23136761509546854387746915)
        ·
          refine ⟨34705142264320281581620373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23136761509546854387746915 34705142264320281581620373)
          ·
            refine ⟨1626803543640013199138455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34705142264320281581620373 1626803543640013199138455)
            ·
              refine ⟨2440205315460019798707683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626803543640013199138455 2440205315460019798707683)
              ·
                refine ⟨3660307973190029698061525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440205315460019798707683 3660307973190029698061525)
                ·
                  refine ⟨85788468121641321048317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3660307973190029698061525 85788468121641321048317)
                  ·
                    rfl

theorem cell21_375913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_375913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375913 prefixEnd_375913 := by exact prefixLift 375913
  have htrace : WordTrace (prefixWord ++ tailWord_375913) baseStart_375913 baseEnd_375913 := by
    simpa [prefixWord, tailWord_375913, baseEnd_375913] using wordTrace_append hprefix tailTrace_375913
  have hstable : (prefixWord ++ tailWord_375913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375913).length < 2 ^ (prefixWord ++ tailWord_375913).sum := by decide
  have hdescent : baseEnd_375913 < baseStart_375913 := by decide
  rcases family_descends (prefixWord ++ tailWord_375913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375981 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 3]
def baseStart_375981 : Nat := 118140960795 + 375981 * 2 ^ 59
def prefixEnd_375981 : Nat := 4983230072969 + 3 ^ 40 * 375981 * 2
def baseEnd_375981 : Nat := 85803986648088313914845

theorem tailTrace_375981 : CollatzResearch.WordTrace tailWord_375981 prefixEnd_375981 85803986648088313914845 := by
  unfold tailWord_375981
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713153650892524287695797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9142102433928349525130531 13713153650892524287695797)
  ·
    refine ⟨1285608154771174151971481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13713153650892524287695797 1285608154771174151971481)
    ·
      refine ⟨964206116078380613978611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1285608154771174151971481 964206116078380613978611)
      ·
        refine ⟨1446309174117570920967917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964206116078380613978611 1446309174117570920967917)
        ·
          refine ⟨542365940294089095362969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1446309174117570920967917 542365940294089095362969)
          ·
            refine ⟨406774455220566821522227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542365940294089095362969 406774455220566821522227)
            ·
              refine ⟨610161682830850232283341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406774455220566821522227 610161682830850232283341)
              ·
                refine ⟨228810631061568837106253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610161682830850232283341 228810631061568837106253)
                ·
                  refine ⟨85803986648088313914845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228810631061568837106253 85803986648088313914845)
                  ·
                    rfl

theorem cell21_375981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_375981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375981 prefixEnd_375981 := by exact prefixLift 375981
  have htrace : WordTrace (prefixWord ++ tailWord_375981) baseStart_375981 baseEnd_375981 := by
    simpa [prefixWord, tailWord_375981, baseEnd_375981] using wordTrace_append hprefix tailTrace_375981
  have hstable : (prefixWord ++ tailWord_375981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375981).length < 2 ^ (prefixWord ++ tailWord_375981).sum := by decide
  have hdescent : baseEnd_375981 < baseStart_375981 := by decide
  rcases family_descends (prefixWord ++ tailWord_375981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376068 : List Nat := [2, 3, 2, 2, 2, 3, 1, 6]
def baseStart_376068 : Nat := 118140960795 + 376068 * 2 ^ 59
def prefixEnd_376068 : Nat := 4983230072969 + 3 ^ 40 * 376068 * 2
def baseEnd_376068 : Nat := 28607947077798498654889

theorem tailTrace_376068 : CollatzResearch.WordTrace tailWord_376068 prefixEnd_376068 28607947077798498654889 := by
  unfold tailWord_376068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858163400788669073056429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9144217867718225430741905 6858163400788669073056429)
  ·
    refine ⟨2571811275295750902396161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6858163400788669073056429 2571811275295750902396161)
    ·
      refine ⟨1928858456471813176797121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571811275295750902396161 1928858456471813176797121)
      ·
        refine ⟨1446643842353859882597841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1928858456471813176797121 1446643842353859882597841)
        ·
          refine ⟨1084982881765394911948381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446643842353859882597841 1084982881765394911948381)
          ·
            refine ⟨406868580662023091980643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084982881765394911948381 406868580662023091980643)
            ·
              refine ⟨610302870993034637970965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406868580662023091980643 610302870993034637970965)
              ·
                refine ⟨28607947077798498654889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 610302870993034637970965 28607947077798498654889)
                ·
                  rfl

theorem cell21_376068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_376068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376068 prefixEnd_376068 := by exact prefixLift 376068
  have htrace : WordTrace (prefixWord ++ tailWord_376068) baseStart_376068 baseEnd_376068 := by
    simpa [prefixWord, tailWord_376068, baseEnd_376068] using wordTrace_append hprefix tailTrace_376068
  have hstable : (prefixWord ++ tailWord_376068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376068).length < 2 ^ (prefixWord ++ tailWord_376068).sum := by decide
  have hdescent : baseEnd_376068 < baseStart_376068 := by decide
  rcases family_descends (prefixWord ++ tailWord_376068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376079 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_376079 : Nat := 118140960795 + 376079 * 2 ^ 59
def prefixEnd_376079 : Nat := 4983230072969 + 3 ^ 40 * 376079 * 2
def baseEnd_376079 : Nat := 85826351583261921281311

theorem tailTrace_376079 : CollatzResearch.WordTrace tailWord_376079 prefixEnd_376079 85826351583261921281311 := by
  unfold tailWord_376079
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716728004537487024763291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9144485336358324683175527 13716728004537487024763291)
  ·
    refine ⟨20575092006806230537144937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716728004537487024763291 20575092006806230537144937)
    ·
      refine ⟨15431319005104672902858703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20575092006806230537144937 15431319005104672902858703)
      ·
        refine ⟨23146978507657009354288055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431319005104672902858703 23146978507657009354288055)
        ·
          refine ⟨34720467761485514031432083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23146978507657009354288055 34720467761485514031432083)
          ·
            refine ⟨52080701642228271047148125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34720467761485514031432083 52080701642228271047148125)
            ·
              refine ⟨19530263115835601642680547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52080701642228271047148125 19530263115835601642680547)
              ·
                refine ⟨29295394673753402464020821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19530263115835601642680547 29295394673753402464020821)
                ·
                  refine ⟨85826351583261921281311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29295394673753402464020821 85826351583261921281311)
                  ·
                    rfl

theorem cell21_376079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_376079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376079 prefixEnd_376079 := by exact prefixLift 376079
  have htrace : WordTrace (prefixWord ++ tailWord_376079) baseStart_376079 baseEnd_376079 := by
    simpa [prefixWord, tailWord_376079, baseEnd_376079] using wordTrace_append hprefix tailTrace_376079
  have hstable : (prefixWord ++ tailWord_376079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376079).length < 2 ^ (prefixWord ++ tailWord_376079).sum := by decide
  have hdescent : baseEnd_376079 < baseStart_376079 := by decide
  rcases family_descends (prefixWord ++ tailWord_376079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376099 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 3]
def baseStart_376099 : Nat := 118140960795 + 376099 * 2 ^ 59
def prefixEnd_376099 : Nat := 4983230072969 + 3 ^ 40 * 376099 * 2
def baseEnd_376099 : Nat := 85830915855746330947937

theorem tailTrace_376099 : CollatzResearch.WordTrace tailWord_376099 prefixEnd_376099 85830915855746330947937 := by
  unfold tailWord_376099
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717457464465030440491351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9144971642976686960327567 13717457464465030440491351)
  ·
    refine ⟨20576186196697545660737027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13717457464465030440491351 20576186196697545660737027)
    ·
      refine ⟨30864279295046318491105541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20576186196697545660737027 30864279295046318491105541)
      ·
        refine ⟨5787052367821184717082289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30864279295046318491105541 5787052367821184717082289)
        ·
          refine ⟨4340289275865888537811717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787052367821184717082289 4340289275865888537811717)
          ·
            refine ⟨813804239224854100839697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4340289275865888537811717 813804239224854100839697)
            ·
              refine ⟨610353179418640575629773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813804239224854100839697 610353179418640575629773)
              ·
                refine ⟨228882442281990215861165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610353179418640575629773 228882442281990215861165)
                ·
                  refine ⟨85830915855746330947937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228882442281990215861165 85830915855746330947937)
                  ·
                    rfl

theorem cell21_376099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3].length) (baseStart_376099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376099 prefixEnd_376099 := by exact prefixLift 376099
  have htrace : WordTrace (prefixWord ++ tailWord_376099) baseStart_376099 baseEnd_376099 := by
    simpa [prefixWord, tailWord_376099, baseEnd_376099] using wordTrace_append hprefix tailTrace_376099
  have hstable : (prefixWord ++ tailWord_376099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376099).length < 2 ^ (prefixWord ++ tailWord_376099).sum := by decide
  have hdescent : baseEnd_376099 < baseStart_376099 := by decide
  rcases family_descends (prefixWord ++ tailWord_376099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376113 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_376113 : Nat := 118140960795 + 376113 * 2 ^ 59
def prefixEnd_376113 : Nat := 4983230072969 + 3 ^ 40 * 376113 * 2
def baseEnd_376113 : Nat := 85834110846485417714575

theorem tailTrace_376113 : CollatzResearch.WordTrace tailWord_376113 prefixEnd_376113 85834110846485417714575 := by
  unfold tailWord_376113
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717968086414310831500993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9145312057609540554333995 13717968086414310831500993)
  ·
    refine ⟨10288476064810733123625745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13717968086414310831500993 10288476064810733123625745)
    ·
      refine ⟨7716357048608049842719309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10288476064810733123625745 7716357048608049842719309)
      ·
        refine ⟨2893633893228018691019741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7716357048608049842719309 2893633893228018691019741)
        ·
          refine ⟨1085112709960507009132403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2893633893228018691019741 1085112709960507009132403)
          ·
            refine ⟨1627669064940760513698605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085112709960507009132403 1627669064940760513698605)
            ·
              refine ⟨610375899352785192636977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1627669064940760513698605 610375899352785192636977)
              ·
                refine ⟨457781924514588894477733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610375899352785192636977 457781924514588894477733)
                ·
                  refine ⟨85834110846485417714575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457781924514588894477733 85834110846485417714575)
                  ·
                    rfl

theorem cell21_376113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_376113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376113 prefixEnd_376113 := by exact prefixLift 376113
  have htrace : WordTrace (prefixWord ++ tailWord_376113) baseStart_376113 baseEnd_376113 := by
    simpa [prefixWord, tailWord_376113, baseEnd_376113] using wordTrace_append hprefix tailTrace_376113
  have hstable : (prefixWord ++ tailWord_376113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376113).length < 2 ^ (prefixWord ++ tailWord_376113).sum := by decide
  have hdescent : baseEnd_376113 < baseStart_376113 := by decide
  rcases family_descends (prefixWord ++ tailWord_376113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376172 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_376172 : Nat := 118140960795 + 376172 * 2 ^ 59
def prefixEnd_376172 : Nat := 4983230072969 + 3 ^ 40 * 376172 * 2
def baseEnd_376172 : Nat := 85847575450314426231121

theorem tailTrace_376172 : CollatzResearch.WordTrace tailWord_376172 prefixEnd_376172 85847575450314426231121 := by
  unfold tailWord_376172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860059996600281953949385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9146746662133709271932513 6860059996600281953949385)
  ·
    refine ⟨5145044997450211465462039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6860059996600281953949385 5145044997450211465462039)
    ·
      refine ⟨7717567496175317198193059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145044997450211465462039 7717567496175317198193059)
      ·
        refine ⟨11576351244262975797289589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717567496175317198193059 11576351244262975797289589)
        ·
          refine ⟨1085282929149653980995899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11576351244262975797289589 1085282929149653980995899)
          ·
            refine ⟨1627924393724480971493849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085282929149653980995899 1627924393724480971493849)
            ·
              refine ⟨1220943295293360728620387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627924393724480971493849 1220943295293360728620387)
              ·
                refine ⟨1831414942940041092930581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220943295293360728620387 1831414942940041092930581)
                ·
                  refine ⟨85847575450314426231121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1831414942940041092930581 85847575450314426231121)
                  ·
                    rfl

theorem cell21_376172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_376172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376172 prefixEnd_376172 := by exact prefixLift 376172
  have htrace : WordTrace (prefixWord ++ tailWord_376172) baseStart_376172 baseEnd_376172 := by
    simpa [prefixWord, tailWord_376172, baseEnd_376172] using wordTrace_append hprefix tailTrace_376172
  have hstable : (prefixWord ++ tailWord_376172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376172).length < 2 ^ (prefixWord ++ tailWord_376172).sum := by decide
  have hdescent : baseEnd_376172 < baseStart_376172 := by decide
  rcases family_descends (prefixWord ++ tailWord_376172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376175 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 3]
def baseStart_376175 : Nat := 118140960795 + 376175 * 2 ^ 59
def prefixEnd_376175 : Nat := 4983230072969 + 3 ^ 40 * 376175 * 2
def baseEnd_376175 : Nat := 85848260091187087681115

theorem tailTrace_376175 : CollatzResearch.WordTrace tailWord_376175 prefixEnd_376175 85848260091187087681115 := by
  unfold tailWord_376175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13720229412189695420257979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9146819608126463613505319 13720229412189695420257979)
  ·
    refine ⟨20580344118284543130386969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13720229412189695420257979 20580344118284543130386969)
    ·
      refine ⟨15435258088713407347790227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20580344118284543130386969 15435258088713407347790227)
      ·
        refine ⟨23152887133070111021685341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15435258088713407347790227 23152887133070111021685341)
        ·
          refine ⟨8682332674901291633132003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23152887133070111021685341 8682332674901291633132003)
          ·
            refine ⟨13023499012351937449698005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682332674901291633132003 13023499012351937449698005)
            ·
              refine ⟨305238258101998533977297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13023499012351937449698005 305238258101998533977297)
              ·
                refine ⟨228928693576498900482973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305238258101998533977297 228928693576498900482973)
                ·
                  refine ⟨85848260091187087681115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228928693576498900482973 85848260091187087681115)
                  ·
                    rfl

theorem cell21_376175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 3].length) (baseStart_376175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376175 prefixEnd_376175 := by exact prefixLift 376175
  have htrace : WordTrace (prefixWord ++ tailWord_376175) baseStart_376175 baseEnd_376175 := by
    simpa [prefixWord, tailWord_376175, baseEnd_376175] using wordTrace_append hprefix tailTrace_376175
  have hstable : (prefixWord ++ tailWord_376175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376175).length < 2 ^ (prefixWord ++ tailWord_376175).sum := by decide
  have hdescent : baseEnd_376175 < baseStart_376175 := by decide
  rcases family_descends (prefixWord ++ tailWord_376175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376220 : List Nat := [2, 2, 3, 4, 2, 8]
def baseStart_376220 : Nat := 118140960795 + 376220 * 2 ^ 59
def prefixEnd_376220 : Nat := 4983230072969 + 3 ^ 40 * 376220 * 2
def baseEnd_376220 : Nat := 3179945544602852201149

theorem tailTrace_376220 : CollatzResearch.WordTrace tailWord_376220 prefixEnd_376220 3179945544602852201149 := by
  unfold tailWord_376220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860935348513334052823057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9147913798017778737097409 6860935348513334052823057)
  ·
    refine ⟨5145701511385000539617293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6860935348513334052823057 5145701511385000539617293)
    ·
      refine ⟨1929638066769375202356485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5145701511385000539617293 1929638066769375202356485)
      ·
        refine ⟨361807137519257850441841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1929638066769375202356485 361807137519257850441841)
        ·
          refine ⟨271355353139443387831381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361807137519257850441841 271355353139443387831381)
          ·
            refine ⟨3179945544602852201149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 271355353139443387831381 3179945544602852201149)
            ·
              rfl

theorem cell21_376220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 8].length) (baseStart_376220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376220 prefixEnd_376220 := by exact prefixLift 376220
  have htrace : WordTrace (prefixWord ++ tailWord_376220) baseStart_376220 baseEnd_376220 := by
    simpa [prefixWord, tailWord_376220, baseEnd_376220] using wordTrace_append hprefix tailTrace_376220
  have hstable : (prefixWord ++ tailWord_376220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376220).length < 2 ^ (prefixWord ++ tailWord_376220).sum := by decide
  have hdescent : baseEnd_376220 < baseStart_376220 := by decide
  rcases family_descends (prefixWord ++ tailWord_376220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376248 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_376248 : Nat := 118140960795 + 376248 * 2 ^ 59
def prefixEnd_376248 : Nat := 4983230072969 + 3 ^ 40 * 376248 * 2
def baseEnd_376248 : Nat := 85864919685755182964299

theorem tailTrace_376248 : CollatzResearch.WordTrace tailWord_376248 prefixEnd_376248 85864919685755182964299 := by
  unfold tailWord_376248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861445970462614443832699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9148594627283485925110265 6861445970462614443832699)
  ·
    refine ⟨10292168955693921665749049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6861445970462614443832699 10292168955693921665749049)
    ·
      refine ⟨7719126716770441249311787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10292168955693921665749049 7719126716770441249311787)
      ·
        refine ⟨11578690075155661873967681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719126716770441249311787 11578690075155661873967681)
        ·
          refine ⟨8684017556366746405475761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11578690075155661873967681 8684017556366746405475761)
          ·
            refine ⟨6513013167275059804106821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684017556366746405475761 6513013167275059804106821)
            ·
              refine ⟨1221189968864073713270029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6513013167275059804106821 1221189968864073713270029)
              ·
                refine ⟨457946238324027642476261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221189968864073713270029 457946238324027642476261)
                ·
                  refine ⟨85864919685755182964299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457946238324027642476261 85864919685755182964299)
                  ·
                    rfl

theorem cell21_376248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_376248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376248 prefixEnd_376248 := by exact prefixLift 376248
  have htrace : WordTrace (prefixWord ++ tailWord_376248) baseStart_376248 baseEnd_376248 := by
    simpa [prefixWord, tailWord_376248, baseEnd_376248] using wordTrace_append hprefix tailTrace_376248
  have hstable : (prefixWord ++ tailWord_376248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376248).length < 2 ^ (prefixWord ++ tailWord_376248).sum := by decide
  have hdescent : baseEnd_376248 < baseStart_376248 := by decide
  rcases family_descends (prefixWord ++ tailWord_376248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376310 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_376310 : Nat := 118140960795 + 376310 * 2 ^ 59
def prefixEnd_376310 : Nat := 4983230072969 + 3 ^ 40 * 376310 * 2
def baseEnd_376310 : Nat := 85879068930456852930839

theorem tailTrace_376310 : CollatzResearch.WordTrace tailWord_376310 prefixEnd_376310 85879068930456852930839 := by
  unfold tailWord_376310
  simp only [CollatzResearch.WordTrace]
  refine ⟨857822079168788342276399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9150102177800408984281589 857822079168788342276399)
  ·
    refine ⟨1286733118753182513414599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 857822079168788342276399 1286733118753182513414599)
    ·
      refine ⟨1930099678129773770121899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286733118753182513414599 1930099678129773770121899)
      ·
        refine ⟨2895149517194660655182849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930099678129773770121899 2895149517194660655182849)
        ·
          refine ⟨2171362137895995491387137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895149517194660655182849 2171362137895995491387137)
          ·
            refine ⟨1628521603421996618540353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171362137895995491387137 1628521603421996618540353)
            ·
              refine ⟨1221391202566497463905265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628521603421996618540353 1221391202566497463905265)
              ·
                refine ⟨916043401924873097928949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221391202566497463905265 916043401924873097928949)
                ·
                  refine ⟨85879068930456852930839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916043401924873097928949 85879068930456852930839)
                  ·
                    rfl

theorem cell21_376310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_376310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376310 prefixEnd_376310 := by exact prefixLift 376310
  have htrace : WordTrace (prefixWord ++ tailWord_376310) baseStart_376310 baseEnd_376310 := by
    simpa [prefixWord, tailWord_376310, baseEnd_376310] using wordTrace_append hprefix tailTrace_376310
  have hstable : (prefixWord ++ tailWord_376310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376310).length < 2 ^ (prefixWord ++ tailWord_376310).sum := by decide
  have hdescent : baseEnd_376310 < baseStart_376310 := by decide
  rcases family_descends (prefixWord ++ tailWord_376310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376327 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 3]
def baseStart_376327 : Nat := 118140960795 + 376327 * 2 ^ 59
def prefixEnd_376327 : Nat := 4983230072969 + 3 ^ 40 * 376327 * 2
def baseEnd_376327 : Nat := 85882948562068601147471

theorem tailTrace_376327 : CollatzResearch.WordTrace tailWord_376327 prefixEnd_376327 85882948562068601147471 := by
  unfold tailWord_376327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13725773307639025379791235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9150515538426016919860823 13725773307639025379791235)
  ·
    refine ⟨20588659961458538069686853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13725773307639025379791235 20588659961458538069686853)
    ·
      refine ⟨3860373742773475888066285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20588659961458538069686853 3860373742773475888066285)
      ·
        refine ⟨1447640153540053458024857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3860373742773475888066285 1447640153540053458024857)
        ·
          refine ⟨1085730115155040093518643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447640153540053458024857 1085730115155040093518643)
          ·
            refine ⟨1628595172732560140277965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085730115155040093518643 1628595172732560140277965)
            ·
              refine ⟨610723189774710052604237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1628595172732560140277965 610723189774710052604237)
              ·
                refine ⟨229021196165516269726589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610723189774710052604237 229021196165516269726589)
                ·
                  refine ⟨85882948562068601147471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229021196165516269726589 85882948562068601147471)
                  ·
                    rfl

theorem cell21_376327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 3].length) (baseStart_376327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376327 prefixEnd_376327 := by exact prefixLift 376327
  have htrace : WordTrace (prefixWord ++ tailWord_376327) baseStart_376327 baseEnd_376327 := by
    simpa [prefixWord, tailWord_376327, baseEnd_376327] using wordTrace_append hprefix tailTrace_376327
  have hstable : (prefixWord ++ tailWord_376327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376327).length < 2 ^ (prefixWord ++ tailWord_376327).sum := by decide
  have hdescent : baseEnd_376327 < baseStart_376327 := by decide
  rcases family_descends (prefixWord ++ tailWord_376327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376344 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_376344 : Nat := 118140960795 + 376344 * 2 ^ 59
def prefixEnd_376344 : Nat := 4983230072969 + 3 ^ 40 * 376344 * 2
def baseEnd_376344 : Nat := 85886828193680349364103

theorem tailTrace_376344 : CollatzResearch.WordTrace tailWord_376344 prefixEnd_376344 85886828193680349364103 := by
  unfold tailWord_376344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6863196674288718641580043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9150928899051624855440057 6863196674288718641580043)
  ·
    refine ⟨10294795011433077962370065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6863196674288718641580043 10294795011433077962370065)
    ·
      refine ⟨7721096258574808471777549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10294795011433077962370065 7721096258574808471777549)
      ·
        refine ⟨2895411096965553176916581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7721096258574808471777549 2895411096965553176916581)
        ·
          refine ⟨542889580681041220671859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2895411096965553176916581 542889580681041220671859)
          ·
            refine ⟨814334371021561831007789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542889580681041220671859 814334371021561831007789)
            ·
              refine ⟨305375389133085686627921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 814334371021561831007789 305375389133085686627921)
              ·
                refine ⟨229031541849814264970941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305375389133085686627921 229031541849814264970941)
                ·
                  refine ⟨85886828193680349364103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229031541849814264970941 85886828193680349364103)
                  ·
                    rfl

theorem cell21_376344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_376344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376344 prefixEnd_376344 := by exact prefixLift 376344
  have htrace : WordTrace (prefixWord ++ tailWord_376344) baseStart_376344 baseEnd_376344 := by
    simpa [prefixWord, tailWord_376344, baseEnd_376344] using wordTrace_append hprefix tailTrace_376344
  have hstable : (prefixWord ++ tailWord_376344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376344).length < 2 ^ (prefixWord ++ tailWord_376344).sum := by decide
  have hdescent : baseEnd_376344 < baseStart_376344 := by decide
  rcases family_descends (prefixWord ++ tailWord_376344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376350 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_376350 : Nat := 118140960795 + 376350 * 2 ^ 59
def prefixEnd_376350 : Nat := 4983230072969 + 3 ^ 40 * 376350 * 2
def baseEnd_376350 : Nat := 85888197475425672264091

theorem tailTrace_376350 : CollatzResearch.WordTrace tailWord_376350 prefixEnd_376350 85888197475425672264091 := by
  unfold tailWord_376350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715826523319462538484813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9151074791037133538585669 1715826523319462538484813)
  ·
    refine ⟨643434946244798451931805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1715826523319462538484813 643434946244798451931805)
    ·
      refine ⟨241288104841799419474427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 643434946244798451931805 241288104841799419474427)
      ·
        refine ⟨361932157262699129211641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241288104841799419474427 361932157262699129211641)
        ·
          refine ⟨271449117947024346908731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361932157262699129211641 271449117947024346908731)
          ·
            refine ⟨407173676920536520363097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271449117947024346908731 407173676920536520363097)
            ·
              refine ⟨305380257690402390272323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407173676920536520363097 305380257690402390272323)
              ·
                refine ⟨458070386535603585408485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305380257690402390272323 458070386535603585408485)
                ·
                  refine ⟨85888197475425672264091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458070386535603585408485 85888197475425672264091)
                  ·
                    rfl

theorem cell21_376350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_376350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376350 prefixEnd_376350 := by exact prefixLift 376350
  have htrace : WordTrace (prefixWord ++ tailWord_376350) baseStart_376350 baseEnd_376350 := by
    simpa [prefixWord, tailWord_376350, baseEnd_376350] using wordTrace_append hprefix tailTrace_376350
  have hstable : (prefixWord ++ tailWord_376350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376350).length < 2 ^ (prefixWord ++ tailWord_376350).sum := by decide
  have hdescent : baseEnd_376350 < baseStart_376350 := by decide
  rcases family_descends (prefixWord ++ tailWord_376350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376355 : List Nat := [1, 1, 1, 4, 5, 1, 2, 6]
def baseStart_376355 : Nat := 118140960795 + 376355 * 2 ^ 59
def prefixEnd_376355 : Nat := 4983230072969 + 3 ^ 40 * 376355 * 2
def baseEnd_376355 : Nat := 28629779514515591560249

theorem tailTrace_376355 : CollatzResearch.WordTrace tailWord_376355 prefixEnd_376355 28629779514515591560249 := by
  unfold tailWord_376355
  simp only [CollatzResearch.WordTrace]
  refine ⟨13726794551537586161810519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9151196367691724107873679 13726794551537586161810519)
  ·
    refine ⟨20590191827306379242715779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13726794551537586161810519 20590191827306379242715779)
    ·
      refine ⟨30885287740959568864073669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20590191827306379242715779 30885287740959568864073669)
      ·
        refine ⟨5790991451429919162013813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30885287740959568864073669 5790991451429919162013813)
        ·
          refine ⟨542905448571554921438795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5790991451429919162013813 542905448571554921438795)
          ·
            refine ⟨814358172857332382158193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542905448571554921438795 814358172857332382158193)
            ·
              refine ⟨610768629642999286618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814358172857332382158193 610768629642999286618645)
              ·
                refine ⟨28629779514515591560249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 610768629642999286618645 28629779514515591560249)
                ·
                  rfl

theorem cell21_376355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_376355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376355 prefixEnd_376355 := by exact prefixLift 376355
  have htrace : WordTrace (prefixWord ++ tailWord_376355) baseStart_376355 baseEnd_376355 := by
    simpa [prefixWord, tailWord_376355, baseEnd_376355] using wordTrace_append hprefix tailTrace_376355
  have hstable : (prefixWord ++ tailWord_376355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376355).length < 2 ^ (prefixWord ++ tailWord_376355).sum := by decide
  have hdescent : baseEnd_376355 < baseStart_376355 := by decide
  rcases family_descends (prefixWord ++ tailWord_376355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376400 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_376400 : Nat := 118140960795 + 376400 * 2 ^ 59
def prefixEnd_376400 : Nat := 4983230072969 + 3 ^ 40 * 376400 * 2
def baseEnd_376400 : Nat := 85899608156636696430655

theorem tailTrace_376400 : CollatzResearch.WordTrace tailWord_376400 prefixEnd_376400 85899608156636696430655 := by
  unfold tailWord_376400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864217918187279423599327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9152290557583039231465769 6864217918187279423599327)
  ·
    refine ⟨10296326877280919135398991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6864217918187279423599327 10296326877280919135398991)
    ·
      refine ⟨15444490315921378703098487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10296326877280919135398991 15444490315921378703098487)
      ·
        refine ⟨23166735473882068054647731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15444490315921378703098487 23166735473882068054647731)
        ·
          refine ⟨34750103210823102081971597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23166735473882068054647731 34750103210823102081971597)
          ·
            refine ⟨13031288704058663280739349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34750103210823102081971597 13031288704058663280739349)
            ·
              refine ⟨610841658002749841284657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13031288704058663280739349 610841658002749841284657)
              ·
                refine ⟨458131243502062380963493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610841658002749841284657 458131243502062380963493)
                ·
                  refine ⟨85899608156636696430655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458131243502062380963493 85899608156636696430655)
                  ·
                    rfl

theorem cell21_376400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_376400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376400 prefixEnd_376400 := by exact prefixLift 376400
  have htrace : WordTrace (prefixWord ++ tailWord_376400) baseStart_376400 baseEnd_376400 := by
    simpa [prefixWord, tailWord_376400, baseEnd_376400] using wordTrace_append hprefix tailTrace_376400
  have hstable : (prefixWord ++ tailWord_376400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376400).length < 2 ^ (prefixWord ++ tailWord_376400).sum := by decide
  have hdescent : baseEnd_376400 < baseStart_376400 := by decide
  rcases family_descends (prefixWord ++ tailWord_376400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376406 : List Nat := [5, 2, 2, 2, 1, 2, 1, 6]
def baseStart_376406 : Nat := 118140960795 + 376406 * 2 ^ 59
def prefixEnd_376406 : Nat := 4983230072969 + 3 ^ 40 * 376406 * 2
def baseEnd_376406 : Nat := 28633659146127339776881

theorem tailTrace_376406 : CollatzResearch.WordTrace tailWord_376406 prefixEnd_376406 28633659146127339776881 := by
  unfold tailWord_376406
  simp only [CollatzResearch.WordTrace]
  refine ⟨858040917147051366994817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9152436449568547914611381 858040917147051366994817)
  ·
    refine ⟨643530687860288525246113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 858040917147051366994817 643530687860288525246113)
    ·
      refine ⟨482648015895216393934585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643530687860288525246113 482648015895216393934585)
      ·
        refine ⟨361986011921412295450939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482648015895216393934585 361986011921412295450939)
        ·
          refine ⟨542979017882118443176409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361986011921412295450939 542979017882118443176409)
          ·
            refine ⟨407234263411588832382307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542979017882118443176409 407234263411588832382307)
            ·
              refine ⟨610851395117383248573461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407234263411588832382307 610851395117383248573461)
              ·
                refine ⟨28633659146127339776881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 610851395117383248573461 28633659146127339776881)
                ·
                  rfl

theorem cell21_376406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_376406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376406 prefixEnd_376406 := by exact prefixLift 376406
  have htrace : WordTrace (prefixWord ++ tailWord_376406) baseStart_376406 baseEnd_376406 := by
    simpa [prefixWord, tailWord_376406, baseEnd_376406] using wordTrace_append hprefix tailTrace_376406
  have hstable : (prefixWord ++ tailWord_376406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376406).length < 2 ^ (prefixWord ++ tailWord_376406).sum := by decide
  have hdescent : baseEnd_376406 < baseStart_376406 := by decide
  rcases family_descends (prefixWord ++ tailWord_376406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376459 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_376459 : Nat := 118140960795 + 376459 * 2 ^ 59
def prefixEnd_376459 : Nat := 4983230072969 + 3 ^ 40 * 376459 * 2
def baseEnd_376459 : Nat := 85913072760465704947201

theorem tailTrace_376459 : CollatzResearch.WordTrace tailWord_376459 prefixEnd_376459 85913072760465704947201 := by
  unfold tailWord_376459
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730587743160811923596431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9153725162107207949064287 13730587743160811923596431)
  ·
    refine ⟨20595881614741217885394647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13730587743160811923596431 20595881614741217885394647)
    ·
      refine ⟨30893822422111826828091971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595881614741217885394647 30893822422111826828091971)
      ·
        refine ⟨46340733633167740242137957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30893822422111826828091971 46340733633167740242137957)
        ·
          refine ⟨8688887556218951295400867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46340733633167740242137957 8688887556218951295400867)
          ·
            refine ⟨13033331334328426943101301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688887556218951295400867 13033331334328426943101301)
            ·
              refine ⟨1221874812593290025915747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13033331334328426943101301 1221874812593290025915747)
              ·
                refine ⟨1832812218889935038873621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221874812593290025915747 1832812218889935038873621)
                ·
                  refine ⟨85913072760465704947201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1832812218889935038873621 85913072760465704947201)
                  ·
                    rfl

theorem cell21_376459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_376459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376459 prefixEnd_376459 := by exact prefixLift 376459
  have htrace : WordTrace (prefixWord ++ tailWord_376459) baseStart_376459 baseEnd_376459 := by
    simpa [prefixWord, tailWord_376459, baseEnd_376459] using wordTrace_append hprefix tailTrace_376459
  have hstable : (prefixWord ++ tailWord_376459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376459).length < 2 ^ (prefixWord ++ tailWord_376459).sum := by decide
  have hdescent : baseEnd_376459 < baseStart_376459 := by decide
  rcases family_descends (prefixWord ++ tailWord_376459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376462 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_376462 : Nat := 118140960795 + 376462 * 2 ^ 59
def prefixEnd_376462 : Nat := 4983230072969 + 3 ^ 40 * 376462 * 2
def baseEnd_376462 : Nat := 85913757401338366397195

theorem tailTrace_376462 : CollatzResearch.WordTrace tailWord_376462 prefixEnd_376462 85913757401338366397195 := by
  unfold tailWord_376462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716337145268742929494455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9153798108099962290637093 1716337145268742929494455)
  ·
    refine ⟨2574505717903114394241683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716337145268742929494455 2574505717903114394241683)
    ·
      refine ⟨3861758576854671591362525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574505717903114394241683 3861758576854671591362525)
      ·
        refine ⟨1448159466320501846760947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3861758576854671591362525 1448159466320501846760947)
        ·
          refine ⟨2172239199480752770141421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448159466320501846760947 2172239199480752770141421)
          ·
            refine ⟨814589699805282288803033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2172239199480752770141421 814589699805282288803033)
            ·
              refine ⟨610942274853961716602275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814589699805282288803033 610942274853961716602275)
              ·
                refine ⟨916413412280942574903413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610942274853961716602275 916413412280942574903413)
                ·
                  refine ⟨85913757401338366397195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916413412280942574903413 85913757401338366397195)
                  ·
                    rfl

theorem cell21_376462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_376462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376462 prefixEnd_376462 := by exact prefixLift 376462
  have htrace : WordTrace (prefixWord ++ tailWord_376462) baseStart_376462 baseEnd_376462 := by
    simpa [prefixWord, tailWord_376462, baseEnd_376462] using wordTrace_append hprefix tailTrace_376462
  have hstable : (prefixWord ++ tailWord_376462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376462).length < 2 ^ (prefixWord ++ tailWord_376462).sum := by decide
  have hdescent : baseEnd_376462 < baseStart_376462 := by decide
  rcases family_descends (prefixWord ++ tailWord_376462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376482 : List Nat := [3, 3, 1, 4, 2, 1, 2, 5]
def baseStart_376482 : Nat := 118140960795 + 376482 * 2 ^ 59
def prefixEnd_376482 : Nat := 4983230072969 + 3 ^ 40 * 376482 * 2
def baseEnd_376482 : Nat := 28639440557940925354607

theorem tailTrace_376482 : CollatzResearch.WordTrace tailWord_376482 prefixEnd_376482 28639440557940925354607 := by
  unfold tailWord_376482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432856655519371712920925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9154284414718324567789133 3432856655519371712920925)
  ·
    refine ⟨1287321245819764392345347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3432856655519371712920925 1287321245819764392345347)
    ·
      refine ⟨1930981868729646588518021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287321245819764392345347 1930981868729646588518021)
      ·
        refine ⟨362059100386808735347129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1930981868729646588518021 362059100386808735347129)
        ·
          refine ⟨271544325290106551510347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362059100386808735347129 271544325290106551510347)
          ·
            refine ⟨407316487935159827265521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271544325290106551510347 407316487935159827265521)
            ·
              refine ⟨305487365951369870449141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407316487935159827265521 305487365951369870449141)
              ·
                refine ⟨28639440557940925354607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305487365951369870449141 28639440557940925354607)
                ·
                  rfl

theorem cell21_376482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_376482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376482 prefixEnd_376482 := by exact prefixLift 376482
  have htrace : WordTrace (prefixWord ++ tailWord_376482) baseStart_376482 baseEnd_376482 := by
    simpa [prefixWord, tailWord_376482, baseEnd_376482] using wordTrace_append hprefix tailTrace_376482
  have hstable : (prefixWord ++ tailWord_376482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376482).length < 2 ^ (prefixWord ++ tailWord_376482).sum := by decide
  have hdescent : baseEnd_376482 < baseStart_376482 := by decide
  rcases family_descends (prefixWord ++ tailWord_376482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376504 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_376504 : Nat := 118140960795 + 376504 * 2 ^ 59
def prefixEnd_376504 : Nat := 4983230072969 + 3 ^ 40 * 376504 * 2
def baseEnd_376504 : Nat := 85923342373555626697109

theorem tailTrace_376504 : CollatzResearch.WordTrace tailWord_376504 prefixEnd_376504 85923342373555626697109 := by
  unfold tailWord_376504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866114513998892304492283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9154819351998523072656377 6866114513998892304492283)
  ·
    refine ⟨10299171770998338456738425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6866114513998892304492283 10299171770998338456738425)
    ·
      refine ⟨7724378828248753842553819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10299171770998338456738425 7724378828248753842553819)
      ·
        refine ⟨11586568242373130763830729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724378828248753842553819 11586568242373130763830729)
        ·
          refine ⟨8689926181779848072873047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11586568242373130763830729 8689926181779848072873047)
          ·
            refine ⟨13034889272669772109309571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689926181779848072873047 13034889272669772109309571)
            ·
              refine ⟨19552333909004658163964357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13034889272669772109309571 19552333909004658163964357)
              ·
                refine ⟨3666062607938373405743317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19552333909004658163964357 3666062607938373405743317)
                ·
                  refine ⟨85923342373555626697109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3666062607938373405743317 85923342373555626697109)
                  ·
                    rfl

theorem cell21_376504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_376504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376504 prefixEnd_376504 := by exact prefixLift 376504
  have htrace : WordTrace (prefixWord ++ tailWord_376504) baseStart_376504 baseEnd_376504 := by
    simpa [prefixWord, tailWord_376504, baseEnd_376504] using wordTrace_append hprefix tailTrace_376504
  have hstable : (prefixWord ++ tailWord_376504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376504).length < 2 ^ (prefixWord ++ tailWord_376504).sum := by decide
  have hdescent : baseEnd_376504 < baseStart_376504 := by decide
  rcases family_descends (prefixWord ++ tailWord_376504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376566 : List Nat := [5, 1, 1, 1, 1, 12]
def baseStart_376566 : Nat := 118140960795 + 376566 * 2 ^ 59
def prefixEnd_376566 : Nat := 4983230072969 + 3 ^ 40 * 376566 * 2
def baseEnd_376566 : Nat := 3182870059935455431987

theorem tailTrace_376566 : CollatzResearch.WordTrace tailWord_376566 prefixEnd_376566 3182870059935455431987 := by
  unfold tailWord_376566
  simp only [CollatzResearch.WordTrace]
  refine ⟨858405647110823074858847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9156326902515446131827701 858405647110823074858847)
  ·
    refine ⟨1287608470666234612288271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 858405647110823074858847 1287608470666234612288271)
    ·
      refine ⟨1931412705999351918432407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1287608470666234612288271 1931412705999351918432407)
      ·
        refine ⟨2897119058999027877648611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931412705999351918432407 2897119058999027877648611)
        ·
          refine ⟨4345678588498541816472917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897119058999027877648611 4345678588498541816472917)
          ·
            refine ⟨3182870059935455431987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4345678588498541816472917 3182870059935455431987)
            ·
              rfl

theorem cell21_376566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 12].length) (baseStart_376566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376566 prefixEnd_376566 := by exact prefixLift 376566
  have htrace : WordTrace (prefixWord ++ tailWord_376566) baseStart_376566 baseEnd_376566 := by
    simpa [prefixWord, tailWord_376566, baseEnd_376566] using wordTrace_append hprefix tailTrace_376566
  have hstable : (prefixWord ++ tailWord_376566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376566).length < 2 ^ (prefixWord ++ tailWord_376566).sum := by decide
  have hdescent : baseEnd_376566 < baseStart_376566 := by decide
  rcases family_descends (prefixWord ++ tailWord_376566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376589 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 5]
def baseStart_376589 : Nat := 118140960795 + 376589 * 2 ^ 59
def prefixEnd_376589 : Nat := 4983230072969 + 3 ^ 40 * 376589 * 2
def baseEnd_376589 : Nat := 85942740531614367780269

theorem tailTrace_376589 : CollatzResearch.WordTrace tailWord_376589 prefixEnd_376589 85942740531614367780269 := by
  unfold tailWord_376589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13735329232689844125828821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9156886155126562750552547 13735329232689844125828821)
  ·
    refine ⟨321921778891168221699113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13735329232689844125828821 321921778891168221699113)
    ·
      refine ⟨241441334168376166274335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321921778891168221699113 241441334168376166274335)
      ·
        refine ⟨362162001252564249411503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241441334168376166274335 362162001252564249411503)
        ·
          refine ⟨543243001878846374117255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362162001252564249411503 543243001878846374117255)
          ·
            refine ⟨814864502818269561175883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543243001878846374117255 814864502818269561175883)
            ·
              refine ⟨1222296754227404341763825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814864502818269561175883 1222296754227404341763825)
              ·
                refine ⟨916722565670553256322869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222296754227404341763825 916722565670553256322869)
                ·
                  refine ⟨85942740531614367780269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916722565670553256322869 85942740531614367780269)
                  ·
                    rfl

theorem cell21_376589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_376589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376589 prefixEnd_376589 := by exact prefixLift 376589
  have htrace : WordTrace (prefixWord ++ tailWord_376589) baseStart_376589 baseEnd_376589 := by
    simpa [prefixWord, tailWord_376589, baseEnd_376589] using wordTrace_append hprefix tailTrace_376589
  have hstable : (prefixWord ++ tailWord_376589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376589).length < 2 ^ (prefixWord ++ tailWord_376589).sum := by decide
  have hdescent : baseEnd_376589 < baseStart_376589 := by decide
  rcases family_descends (prefixWord ++ tailWord_376589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376597 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_376597 : Nat := 118140960795 + 376597 * 2 ^ 59
def prefixEnd_376597 : Nat := 4983230072969 + 3 ^ 40 * 376597 * 2
def baseEnd_376597 : Nat := 85944566240608131646919

theorem tailTrace_376597 : CollatzResearch.WordTrace tailWord_376597 prefixEnd_376597 85944566240608131646919 := by
  unfold tailWord_376597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13735621016660861492120045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9157080677773907661413363 13735621016660861492120045)
  ·
    refine ⟨5150857881247823059545017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13735621016660861492120045 5150857881247823059545017)
    ·
      refine ⟨3863143410935867294658763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5150857881247823059545017 3863143410935867294658763)
      ·
        refine ⟨5794715116403800941988145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863143410935867294658763 5794715116403800941988145)
        ·
          refine ⟨4346036337302850706491109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794715116403800941988145 4346036337302850706491109)
          ·
            refine ⟨814881813244284507467083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4346036337302850706491109 814881813244284507467083)
            ·
              refine ⟨1222322719866426761200625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814881813244284507467083 1222322719866426761200625)
              ·
                refine ⟨916742039899820070900469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222322719866426761200625 916742039899820070900469)
                ·
                  refine ⟨85944566240608131646919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916742039899820070900469 85944566240608131646919)
                  ·
                    rfl

theorem cell21_376597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_376597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376597 prefixEnd_376597 := by exact prefixLift 376597
  have htrace : WordTrace (prefixWord ++ tailWord_376597) baseStart_376597 baseEnd_376597 := by
    simpa [prefixWord, tailWord_376597, baseEnd_376597] using wordTrace_append hprefix tailTrace_376597
  have hstable : (prefixWord ++ tailWord_376597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376597).length < 2 ^ (prefixWord ++ tailWord_376597).sum := by decide
  have hdescent : baseEnd_376597 < baseStart_376597 := by decide
  rcases family_descends (prefixWord ++ tailWord_376597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376794 : List Nat := [3, 1, 1, 2, 5, 1, 8]
def baseStart_376794 : Nat := 118140960795 + 376794 * 2 ^ 59
def prefixEnd_376794 : Nat := 4983230072969 + 3 ^ 40 * 376794 * 2
def baseEnd_376794 : Nat := 9554391591619951873687

theorem tailTrace_376794 : CollatzResearch.WordTrace tailWord_376794 prefixEnd_376794 9554391591619951873687 := by
  unfold tailWord_376794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435701549236791034260359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9161870797964776091360957 3435701549236791034260359)
  ·
    refine ⟨5153552323855186551390539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3435701549236791034260359 5153552323855186551390539)
    ·
      refine ⟨7730328485782779827085809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153552323855186551390539 7730328485782779827085809)
      ·
        refine ⟨5797746364337084870314357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7730328485782779827085809 5797746364337084870314357)
        ·
          refine ⟨543538721656601706591971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5797746364337084870314357 543538721656601706591971)
          ·
            refine ⟨815308082484902559887957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543538721656601706591971 815308082484902559887957)
            ·
              refine ⟨9554391591619951873687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 815308082484902559887957 9554391591619951873687)
              ·
                rfl

theorem cell21_376794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 8].length) (baseStart_376794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376794 prefixEnd_376794 := by exact prefixLift 376794
  have htrace : WordTrace (prefixWord ++ tailWord_376794) baseStart_376794 baseEnd_376794 := by
    simpa [prefixWord, tailWord_376794, baseEnd_376794] using wordTrace_append hprefix tailTrace_376794
  have hstable : (prefixWord ++ tailWord_376794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376794).length < 2 ^ (prefixWord ++ tailWord_376794).sum := by decide
  have hdescent : baseEnd_376794 < baseStart_376794 := by decide
  rcases family_descends (prefixWord ++ tailWord_376794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376839 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_376839 : Nat := 118140960795 + 376839 * 2 ^ 59
def prefixEnd_376839 : Nat := 4983230072969 + 3 ^ 40 * 376839 * 2
def baseEnd_376839 : Nat := 85999793937669488613091

theorem tailTrace_376839 : CollatzResearch.WordTrace tailWord_376839 prefixEnd_376839 85999793937669488613091 := by
  unfold tailWord_376839
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744447481784136822429571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162964987856091214953047 13744447481784136822429571)
  ·
    refine ⟨20616671222676205233644357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13744447481784136822429571 20616671222676205233644357)
    ·
      refine ⟨3865625854251788481308317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20616671222676205233644357 3865625854251788481308317)
      ·
        refine ⟨1449609695344420680490619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3865625854251788481308317 1449609695344420680490619)
        ·
          refine ⟨2174414543016631020735929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449609695344420680490619 2174414543016631020735929)
          ·
            refine ⟨1630810907262473265551947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174414543016631020735929 1630810907262473265551947)
            ·
              refine ⟨2446216360893709898327921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630810907262473265551947 2446216360893709898327921)
              ·
                refine ⟨1834662270670282423745941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446216360893709898327921 1834662270670282423745941)
                ·
                  refine ⟨85999793937669488613091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1834662270670282423745941 85999793937669488613091)
                  ·
                    rfl

theorem cell21_376839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_376839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376839 prefixEnd_376839 := by exact prefixLift 376839
  have htrace : WordTrace (prefixWord ++ tailWord_376839) baseStart_376839 baseEnd_376839 := by
    simpa [prefixWord, tailWord_376839, baseEnd_376839] using wordTrace_append hprefix tailTrace_376839
  have hstable : (prefixWord ++ tailWord_376839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376839).length < 2 ^ (prefixWord ++ tailWord_376839).sum := by decide
  have hdescent : baseEnd_376839 < baseStart_376839 := by decide
  rcases family_descends (prefixWord ++ tailWord_376839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376845 : List Nat := [1, 7, 1, 2, 1, 2, 7]
def baseStart_376845 : Nat := 118140960795 + 376845 * 2 ^ 59
def prefixEnd_376845 : Nat := 4983230072969 + 3 ^ 40 * 376845 * 2
def baseEnd_376845 : Nat := 9555684802157201279231

theorem tailTrace_376845 : CollatzResearch.WordTrace tailWord_376845 prefixEnd_376845 9555684802157201279231 := by
  unfold tailWord_376845
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744666319762399847147989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9163110879841599898098659 13744666319762399847147989)
  ·
    refine ⟨322140616869431246417531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13744666319762399847147989 322140616869431246417531)
    ·
      refine ⟨483210925304146869626297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322140616869431246417531 483210925304146869626297)
      ·
        refine ⟨362408193978110152219723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483210925304146869626297 362408193978110152219723)
        ·
          refine ⟨543612290967165228329585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362408193978110152219723 543612290967165228329585)
          ·
            refine ⟨407709218225373921247189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543612290967165228329585 407709218225373921247189)
            ·
              refine ⟨9555684802157201279231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 407709218225373921247189 9555684802157201279231)
              ·
                rfl

theorem cell21_376845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 7].length) (baseStart_376845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376845 prefixEnd_376845 := by exact prefixLift 376845
  have htrace : WordTrace (prefixWord ++ tailWord_376845) baseStart_376845 baseEnd_376845 := by
    simpa [prefixWord, tailWord_376845, baseEnd_376845] using wordTrace_append hprefix tailTrace_376845
  have hstable : (prefixWord ++ tailWord_376845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376845).length < 2 ^ (prefixWord ++ tailWord_376845).sum := by decide
  have hdescent : baseEnd_376845 < baseStart_376845 := by decide
  rcases family_descends (prefixWord ++ tailWord_376845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376901 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 3]
def baseStart_376901 : Nat := 118140960795 + 376901 * 2 ^ 59
def prefixEnd_376901 : Nat := 4983230072969 + 3 ^ 40 * 376901 * 2
def baseEnd_376901 : Nat := 86013943182371158579631

theorem tailTrace_376901 : CollatzResearch.WordTrace tailWord_376901 prefixEnd_376901 86013943182371158579631 := by
  unfold tailWord_376901
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746708807559521411186557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9164472538373014274124371 13746708807559521411186557)
  ·
    refine ⟨5155015802834820529194959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13746708807559521411186557 5155015802834820529194959)
    ·
      refine ⟨7732523704252230793792439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155015802834820529194959 7732523704252230793792439)
      ·
        refine ⟨11598785556378346190688659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7732523704252230793792439 11598785556378346190688659)
        ·
          refine ⟨17398178334567519286032989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598785556378346190688659 17398178334567519286032989)
          ·
            refine ⟨6524316875462819732262371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17398178334567519286032989 6524316875462819732262371)
            ·
              refine ⟨9786475313194229598393557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524316875462819732262371 9786475313194229598393557)
              ·
                refine ⟨229370515152989756212349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9786475313194229598393557 229370515152989756212349)
                ·
                  refine ⟨86013943182371158579631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229370515152989756212349 86013943182371158579631)
                  ·
                    rfl

theorem cell21_376901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_376901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_376901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_376901 prefixEnd_376901 := by exact prefixLift 376901
  have htrace : WordTrace (prefixWord ++ tailWord_376901) baseStart_376901 baseEnd_376901 := by
    simpa [prefixWord, tailWord_376901, baseEnd_376901] using wordTrace_append hprefix tailTrace_376901
  have hstable : (prefixWord ++ tailWord_376901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376901).length < 2 ^ (prefixWord ++ tailWord_376901).sum := by decide
  have hdescent : baseEnd_376901 < baseStart_376901 := by decide
  rcases family_descends (prefixWord ++ tailWord_376901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377084 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_377084 : Nat := 118140960795 + 377084 * 2 ^ 59
def prefixEnd_377084 : Nat := 4983230072969 + 3 ^ 40 * 377084 * 2
def baseEnd_377084 : Nat := 86055706275603507029257

theorem tailTrace_377084 : CollatzResearch.WordTrace tailWord_377084 prefixEnd_377084 86055706275603507029257 := by
  unfold tailWord_377084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876691682948271832549153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9168922243931029110065537 6876691682948271832549153)
  ·
    refine ⟨5157518762211203874411865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6876691682948271832549153 5157518762211203874411865)
    ·
      refine ⟨3868139071658402905808899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5157518762211203874411865 3868139071658402905808899)
      ·
        refine ⟨5802208607487604358713349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868139071658402905808899 5802208607487604358713349)
        ·
          refine ⟨1087914113903925817258753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5802208607487604358713349 1087914113903925817258753)
          ·
            refine ⟨815935585427944362944065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087914113903925817258753 815935585427944362944065)
            ·
              refine ⟨611951689070958272208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815935585427944362944065 611951689070958272208049)
              ·
                refine ⟨458963766803218704156037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611951689070958272208049 458963766803218704156037)
                ·
                  refine ⟨86055706275603507029257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458963766803218704156037 86055706275603507029257)
                  ·
                    rfl

theorem cell21_377084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_377084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377084 prefixEnd_377084 := by exact prefixLift 377084
  have htrace : WordTrace (prefixWord ++ tailWord_377084) baseStart_377084 baseEnd_377084 := by
    simpa [prefixWord, tailWord_377084, baseEnd_377084] using wordTrace_append hprefix tailTrace_377084
  have hstable : (prefixWord ++ tailWord_377084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377084).length < 2 ^ (prefixWord ++ tailWord_377084).sum := by decide
  have hdescent : baseEnd_377084 < baseStart_377084 := by decide
  rcases family_descends (prefixWord ++ tailWord_377084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377112 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_377112 : Nat := 118140960795 + 377112 * 2 ^ 59
def prefixEnd_377112 : Nat := 4983230072969 + 3 ^ 40 * 377112 * 2
def baseEnd_377112 : Nat := 86062096257081680562533

theorem tailTrace_377112 : CollatzResearch.WordTrace tailWord_377112 prefixEnd_377112 86062096257081680562533 := by
  unfold tailWord_377112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877202304897552223558795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9169603073196736298078393 6877202304897552223558795)
  ·
    refine ⟨10315803457346328335338193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6877202304897552223558795 10315803457346328335338193)
    ·
      refine ⟨7736852593009746251503645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10315803457346328335338193 7736852593009746251503645)
      ·
        refine ⟨2901319722378654844313867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7736852593009746251503645 2901319722378654844313867)
        ·
          refine ⟨4351979583567982266470801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901319722378654844313867 4351979583567982266470801)
          ·
            refine ⟨3263984687675986699853101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351979583567982266470801 3263984687675986699853101)
            ·
              refine ⟨1223994257878495012444913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3263984687675986699853101 1223994257878495012444913)
              ·
                refine ⟨917995693408871259333685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223994257878495012444913 917995693408871259333685)
                ·
                  refine ⟨86062096257081680562533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 917995693408871259333685 86062096257081680562533)
                  ·
                    rfl

theorem cell21_377112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_377112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377112 prefixEnd_377112 := by exact prefixLift 377112
  have htrace : WordTrace (prefixWord ++ tailWord_377112) baseStart_377112 baseEnd_377112 := by
    simpa [prefixWord, tailWord_377112, baseEnd_377112] using wordTrace_append hprefix tailTrace_377112
  have hstable : (prefixWord ++ tailWord_377112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377112).length < 2 ^ (prefixWord ++ tailWord_377112).sum := by decide
  have hdescent : baseEnd_377112 < baseStart_377112 := by decide
  rcases family_descends (prefixWord ++ tailWord_377112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377171 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_377171 : Nat := 118140960795 + 377171 * 2 ^ 59
def prefixEnd_377171 : Nat := 4983230072969 + 3 ^ 40 * 377171 * 2
def baseEnd_377171 : Nat := 86075560860910689079079

theorem tailTrace_377171 : CollatzResearch.WordTrace tailWord_377171 prefixEnd_377171 86075560860910689079079 := by
  unfold tailWord_377171
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756556516581357523515367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9171037677720905015676911 13756556516581357523515367)
  ·
    refine ⟨20634834774872036285273051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13756556516581357523515367 20634834774872036285273051)
    ·
      refine ⟨30952252162308054427909577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634834774872036285273051 30952252162308054427909577)
      ·
        refine ⟨23214189121731040820932183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30952252162308054427909577 23214189121731040820932183)
        ·
          refine ⟨34821283682596561231398275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23214189121731040820932183 34821283682596561231398275)
          ·
            refine ⟨52231925523894841847097413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34821283682596561231398275 52231925523894841847097413)
            ·
              refine ⟨9793486035730282846330765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52231925523894841847097413 9793486035730282846330765)
              ·
                refine ⟨3672557263398856067374037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9793486035730282846330765 3672557263398856067374037)
                ·
                  refine ⟨86075560860910689079079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3672557263398856067374037 86075560860910689079079)
                  ·
                    rfl

theorem cell21_377171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_377171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377171 prefixEnd_377171 := by exact prefixLift 377171
  have htrace : WordTrace (prefixWord ++ tailWord_377171) baseStart_377171 baseEnd_377171 := by
    simpa [prefixWord, tailWord_377171, baseEnd_377171] using wordTrace_append hprefix tailTrace_377171
  have hstable : (prefixWord ++ tailWord_377171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377171).length < 2 ^ (prefixWord ++ tailWord_377171).sum := by decide
  have hdescent : baseEnd_377171 < baseStart_377171 := by decide
  rcases family_descends (prefixWord ++ tailWord_377171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377180 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_377180 : Nat := 118140960795 + 377180 * 2 ^ 59
def prefixEnd_377180 : Nat := 4983230072969 + 3 ^ 40 * 377180 * 2
def baseEnd_377180 : Nat := 86077614783528673429061

theorem tailTrace_377180 : CollatzResearch.WordTrace tailWord_377180 prefixEnd_377180 86077614783528673429061 := by
  unfold tailWord_377180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878442386774376030296497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9171256515699168040395329 6878442386774376030296497)
  ·
    refine ⟨5158831790080782022722373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6878442386774376030296497 5158831790080782022722373)
    ·
      refine ⟨967280960640146629260445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5158831790080782022722373 967280960640146629260445)
      ·
        refine ⟨362730360240054985972667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 967280960640146629260445 362730360240054985972667)
        ·
          refine ⟨544095540360082478959001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362730360240054985972667 544095540360082478959001)
          ·
            refine ⟨408071655270061859219251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544095540360082478959001 408071655270061859219251)
            ·
              refine ⟨612107482905092788828877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408071655270061859219251 612107482905092788828877)
              ·
                refine ⟨229540306089409795810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612107482905092788828877 229540306089409795810829)
                ·
                  refine ⟨86077614783528673429061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229540306089409795810829 86077614783528673429061)
                  ·
                    rfl

theorem cell21_377180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_377180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377180 prefixEnd_377180 := by exact prefixLift 377180
  have htrace : WordTrace (prefixWord ++ tailWord_377180) baseStart_377180 baseEnd_377180 := by
    simpa [prefixWord, tailWord_377180, baseEnd_377180] using wordTrace_append hprefix tailTrace_377180
  have hstable : (prefixWord ++ tailWord_377180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377180).length < 2 ^ (prefixWord ++ tailWord_377180).sum := by decide
  have hdescent : baseEnd_377180 < baseStart_377180 := by decide
  rcases family_descends (prefixWord ++ tailWord_377180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377205 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_377205 : Nat := 118140960795 + 377205 * 2 ^ 59
def prefixEnd_377205 : Nat := 4983230072969 + 3 ^ 40 * 377205 * 2
def baseEnd_377205 : Nat := 86083320124134185512343

theorem tailTrace_377205 : CollatzResearch.WordTrace tailWord_377205 prefixEnd_377205 86083320124134185512343 := by
  unfold tailWord_377205
  simp only [CollatzResearch.WordTrace]
  refine ⟨13757796598458181330253069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9171864398972120886835379 13757796598458181330253069)
  ·
    refine ⟨5159173724421817998844901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13757796598458181330253069 5159173724421817998844901)
    ·
      refine ⟨967345073329090874783419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5159173724421817998844901 967345073329090874783419)
      ·
        refine ⟨1451017609993636312175129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967345073329090874783419 1451017609993636312175129)
        ·
          refine ⟨1088263207495227234131347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451017609993636312175129 1088263207495227234131347)
          ·
            refine ⟨1632394811242840851197021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088263207495227234131347 1632394811242840851197021)
            ·
              refine ⟨612148054216065319198883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1632394811242840851197021 612148054216065319198883)
              ·
                refine ⟨918222081324097978798325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612148054216065319198883 918222081324097978798325)
                ·
                  refine ⟨86083320124134185512343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918222081324097978798325 86083320124134185512343)
                  ·
                    rfl

theorem cell21_377205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_377205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377205 prefixEnd_377205 := by exact prefixLift 377205
  have htrace : WordTrace (prefixWord ++ tailWord_377205) baseStart_377205 baseEnd_377205 := by
    simpa [prefixWord, tailWord_377205, baseEnd_377205] using wordTrace_append hprefix tailTrace_377205
  have hstable : (prefixWord ++ tailWord_377205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377205).length < 2 ^ (prefixWord ++ tailWord_377205).sum := by decide
  have hdescent : baseEnd_377205 < baseStart_377205 := by decide
  rcases family_descends (prefixWord ++ tailWord_377205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377256 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_377256 : Nat := 118140960795 + 377256 * 2 ^ 59
def prefixEnd_377256 : Nat := 4983230072969 + 3 ^ 40 * 377256 * 2
def baseEnd_377256 : Nat := 86094959018969430162239

theorem tailTrace_377256 : CollatzResearch.WordTrace tailWord_377256 prefixEnd_377256 86094959018969430162239 := by
  unfold tailWord_377256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879828360636708520179811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9173104480848944693573081 6879828360636708520179811)
  ·
    refine ⟨10319742540955062780269717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879828360636708520179811 10319742540955062780269717)
    ·
      refine ⟨483737931607268567825143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10319742540955062780269717 483737931607268567825143)
      ·
        refine ⟨725606897410902851737715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483737931607268567825143 725606897410902851737715)
        ·
          refine ⟨1088410346116354277606573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725606897410902851737715 1088410346116354277606573)
          ·
            refine ⟨408153879793632854102465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1088410346116354277606573 408153879793632854102465)
            ·
              refine ⟨306115409845224640576849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408153879793632854102465 306115409845224640576849)
              ·
                refine ⟨229586557383918480432637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306115409845224640576849 229586557383918480432637)
                ·
                  refine ⟨86094959018969430162239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229586557383918480432637 86094959018969430162239)
                  ·
                    rfl

theorem cell21_377256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_377256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377256 prefixEnd_377256 := by exact prefixLift 377256
  have htrace : WordTrace (prefixWord ++ tailWord_377256) baseStart_377256 baseEnd_377256 := by
    simpa [prefixWord, tailWord_377256, baseEnd_377256] using wordTrace_append hprefix tailTrace_377256
  have hstable : (prefixWord ++ tailWord_377256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377256).length < 2 ^ (prefixWord ++ tailWord_377256).sum := by decide
  have hdescent : baseEnd_377256 < baseStart_377256 := by decide
  rcases family_descends (prefixWord ++ tailWord_377256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377309 : List Nat := [1, 4, 3, 1, 1, 1, 10]
def baseStart_377309 : Nat := 118140960795 + 377309 * 2 ^ 59
def prefixEnd_377309 : Nat := 4983230072969 + 3 ^ 40 * 377309 * 2
def baseEnd_377309 : Nat := 9567450482339235086533

theorem tailTrace_377309 : CollatzResearch.WordTrace tailWord_377309 prefixEnd_377309 9567450482339235086533 := by
  unfold tailWord_377309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761589790081407092038981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9174393193387604728025987 13761589790081407092038981)
  ·
    refine ⟨2580298085640263829757309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13761589790081407092038981 2580298085640263829757309)
    ·
      refine ⟨967611782115098936158991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2580298085640263829757309 967611782115098936158991)
      ·
        refine ⟨1451417673172648404238487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967611782115098936158991 1451417673172648404238487)
        ·
          refine ⟨2177126509758972606357731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451417673172648404238487 2177126509758972606357731)
          ·
            refine ⟨3265689764638458909536597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177126509758972606357731 3265689764638458909536597)
            ·
              refine ⟨9567450482339235086533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3265689764638458909536597 9567450482339235086533)
              ·
                rfl

theorem cell21_377309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 10].length) (baseStart_377309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377309 prefixEnd_377309 := by exact prefixLift 377309
  have htrace : WordTrace (prefixWord ++ tailWord_377309) baseStart_377309 baseEnd_377309 := by
    simpa [prefixWord, tailWord_377309, baseEnd_377309] using wordTrace_append hprefix tailTrace_377309
  have hstable : (prefixWord ++ tailWord_377309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377309).length < 2 ^ (prefixWord ++ tailWord_377309).sum := by decide
  have hdescent : baseEnd_377309 < baseStart_377309 := by decide
  rcases family_descends (prefixWord ++ tailWord_377309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377354 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_377354 : Nat := 118140960795 + 377354 * 2 ^ 59
def prefixEnd_377354 : Nat := 4983230072969 + 3 ^ 40 * 377354 * 2
def baseEnd_377354 : Nat := 86117323954143037528705

theorem tailTrace_377354 : CollatzResearch.WordTrace tailWord_377354 prefixEnd_377354 86117323954143037528705 := by
  unfold tailWord_377354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440807768729594944356779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9175487383278919851618077 3440807768729594944356779)
  ·
    refine ⟨5161211653094392416535169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3440807768729594944356779 5161211653094392416535169)
    ·
      refine ⟨3870908739820794312401377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5161211653094392416535169 3870908739820794312401377)
      ·
        refine ⟨2903181554865595734301033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3870908739820794312401377 2903181554865595734301033)
        ·
          refine ⟨2177386166149196800725775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903181554865595734301033 2177386166149196800725775)
          ·
            refine ⟨3266079249223795201088663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177386166149196800725775 3266079249223795201088663)
            ·
              refine ⟨4899118873835692801632995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266079249223795201088663 4899118873835692801632995)
              ·
                refine ⟨7348678310753539202449493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899118873835692801632995 7348678310753539202449493)
                ·
                  refine ⟨86117323954143037528705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7348678310753539202449493 86117323954143037528705)
                  ·
                    rfl

theorem cell21_377354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_377354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377354 prefixEnd_377354 := by exact prefixLift 377354
  have htrace : WordTrace (prefixWord ++ tailWord_377354) baseStart_377354 baseEnd_377354 := by
    simpa [prefixWord, tailWord_377354, baseEnd_377354] using wordTrace_append hprefix tailTrace_377354
  have hstable : (prefixWord ++ tailWord_377354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377354).length < 2 ^ (prefixWord ++ tailWord_377354).sum := by decide
  have hdescent : baseEnd_377354 < baseStart_377354 := by decide
  rcases family_descends (prefixWord ++ tailWord_377354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377399 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_377399 : Nat := 118140960795 + 377399 * 2 ^ 59
def prefixEnd_377399 : Nat := 4983230072969 + 3 ^ 40 * 377399 * 2
def baseEnd_377399 : Nat := 86127593567232959278613

theorem tailTrace_377399 : CollatzResearch.WordTrace tailWord_377399 prefixEnd_377399 86127593567232959278613 := by
  unfold tailWord_377399
  simp only [CollatzResearch.WordTrace]
  refine ⟨13764872359755352462815251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9176581573170234975210167 13764872359755352462815251)
  ·
    refine ⟨20647308539633028694222877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13764872359755352462815251 20647308539633028694222877)
    ·
      refine ⟨7742740702362385760333579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20647308539633028694222877 7742740702362385760333579)
      ·
        refine ⟨11614111053543578640500369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742740702362385760333579 11614111053543578640500369)
        ·
          refine ⟨8710583290157683980375277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11614111053543578640500369 8710583290157683980375277)
          ·
            refine ⟨3266468733809131492640729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8710583290157683980375277 3266468733809131492640729)
            ·
              refine ⟨2449851550356848619480547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266468733809131492640729 2449851550356848619480547)
              ·
                refine ⟨3674777325535272929220821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449851550356848619480547 3674777325535272929220821)
                ·
                  refine ⟨86127593567232959278613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3674777325535272929220821 86127593567232959278613)
                  ·
                    rfl

theorem cell21_377399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_377399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377399 prefixEnd_377399 := by exact prefixLift 377399
  have htrace : WordTrace (prefixWord ++ tailWord_377399) baseStart_377399 baseEnd_377399 := by
    simpa [prefixWord, tailWord_377399, baseEnd_377399] using wordTrace_append hprefix tailTrace_377399
  have hstable : (prefixWord ++ tailWord_377399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377399).length < 2 ^ (prefixWord ++ tailWord_377399).sum := by decide
  have hdescent : baseEnd_377399 < baseStart_377399 := by decide
  rcases family_descends (prefixWord ++ tailWord_377399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377554 : List Nat := [3, 2, 2, 2, 3, 1, 2, 6]
def baseStart_377554 : Nat := 118140960795 + 377554 * 2 ^ 59
def prefixEnd_377554 : Nat := 4983230072969 + 3 ^ 40 * 377554 * 2
def baseEnd_377554 : Nat := 28720988892995711398321

theorem tailTrace_377554 : CollatzResearch.WordTrace tailWord_377554 prefixEnd_377554 28720988892995711398321 := by
  unfold tailWord_377554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442631418548453483676929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9180350449462542623138477 3442631418548453483676929)
  ·
    refine ⟨2581973563911340112757697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3442631418548453483676929 2581973563911340112757697)
    ·
      refine ⟨1936480172933505084568273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2581973563911340112757697 1936480172933505084568273)
      ·
        refine ⟨1452360129700128813426205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936480172933505084568273 1452360129700128813426205)
        ·
          refine ⟨544635048637548305034827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1452360129700128813426205 544635048637548305034827)
          ·
            refine ⟨816952572956322457552241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544635048637548305034827 816952572956322457552241)
            ·
              refine ⟨612714429717241843164181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816952572956322457552241 612714429717241843164181)
              ·
                refine ⟨28720988892995711398321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 612714429717241843164181 28720988892995711398321)
                ·
                  rfl

theorem cell21_377554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_377554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377554 prefixEnd_377554 := by exact prefixLift 377554
  have htrace : WordTrace (prefixWord ++ tailWord_377554) baseStart_377554 baseEnd_377554 := by
    simpa [prefixWord, tailWord_377554, baseEnd_377554] using wordTrace_append hprefix tailTrace_377554
  have hstable : (prefixWord ++ tailWord_377554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377554).length < 2 ^ (prefixWord ++ tailWord_377554).sum := by decide
  have hdescent : baseEnd_377554 < baseStart_377554 := by decide
  rcases family_descends (prefixWord ++ tailWord_377554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377596 : List Nat := [2, 2, 2, 1, 3, 11]
def baseStart_377596 : Nat := 118140960795 + 377596 * 2 ^ 59
def prefixEnd_377596 : Nat := 4983230072969 + 3 ^ 40 * 377596 * 2
def baseEnd_377596 : Nat := 3191575987081644240551

theorem tailTrace_377596 : CollatzResearch.WordTrace tailWord_377596 prefixEnd_377596 3191575987081644240551 := by
  unfold tailWord_377596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886028770020827553868321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9181371693361103405157761 6886028770020827553868321)
  ·
    refine ⟨5164521577515620665401241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6886028770020827553868321 5164521577515620665401241)
    ·
      refine ⟨3873391183136715499050931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5164521577515620665401241 3873391183136715499050931)
      ·
        refine ⟨5810086774705073248576397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873391183136715499050931 5810086774705073248576397)
        ·
          refine ⟨2178782540514402468216149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5810086774705073248576397 2178782540514402468216149)
          ·
            refine ⟨3191575987081644240551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2178782540514402468216149 3191575987081644240551)
            ·
              rfl

theorem cell21_377596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 11].length) (baseStart_377596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377596 prefixEnd_377596 := by exact prefixLift 377596
  have htrace : WordTrace (prefixWord ++ tailWord_377596) baseStart_377596 baseEnd_377596 := by
    simpa [prefixWord, tailWord_377596, baseEnd_377596] using wordTrace_append hprefix tailTrace_377596
  have hstable : (prefixWord ++ tailWord_377596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377596).length < 2 ^ (prefixWord ++ tailWord_377596).sum := by decide
  have hdescent : baseEnd_377596 < baseStart_377596 := by decide
  rcases family_descends (prefixWord ++ tailWord_377596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377602 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_377602 : Nat := 118140960795 + 377602 * 2 ^ 59
def prefixEnd_377602 : Nat := 4983230072969 + 3 ^ 40 * 377602 * 2
def baseEnd_377602 : Nat := 86173920932949717394865

theorem tailTrace_377602 : CollatzResearch.WordTrace tailWord_377602 prefixEnd_377602 86173920932949717394865 := by
  unfold tailWord_377602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443069094504979533113765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9181517585346612088303373 3443069094504979533113765)
  ·
    refine ⟨645575455219683662458831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3443069094504979533113765 645575455219683662458831)
    ·
      refine ⟨968363182829525493688247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645575455219683662458831 968363182829525493688247)
      ·
        refine ⟨1452544774244288240532371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968363182829525493688247 1452544774244288240532371)
        ·
          refine ⟨2178817161366432360798557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452544774244288240532371 2178817161366432360798557)
          ·
            refine ⟨817056435512412135299459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2178817161366432360798557 817056435512412135299459)
            ·
              refine ⟨1225584653268618202949189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817056435512412135299459 1225584653268618202949189)
              ·
                refine ⟨229797122487865913052973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1225584653268618202949189 229797122487865913052973)
                ·
                  refine ⟨86173920932949717394865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229797122487865913052973 86173920932949717394865)
                  ·
                    rfl

theorem cell21_377602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_377602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377602 prefixEnd_377602 := by exact prefixLift 377602
  have htrace : WordTrace (prefixWord ++ tailWord_377602) baseStart_377602 baseEnd_377602 := by
    simpa [prefixWord, tailWord_377602, baseEnd_377602] using wordTrace_append hprefix tailTrace_377602
  have hstable : (prefixWord ++ tailWord_377602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377602).length < 2 ^ (prefixWord ++ tailWord_377602).sum := by decide
  have hdescent : baseEnd_377602 < baseStart_377602 := by decide
  rcases family_descends (prefixWord ++ tailWord_377602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377641 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_377641 : Nat := 118140960795 + 377641 * 2 ^ 59
def prefixEnd_377641 : Nat := 4983230072969 + 3 ^ 40 * 377641 * 2
def baseEnd_377641 : Nat := 86182821264294316244785

theorem tailTrace_377641 : CollatzResearch.WordTrace tailWord_377641 prefixEnd_377641 86182821264294316244785 := by
  unfold tailWord_377641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13773698824878627793124777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9182465883252418528749851 13773698824878627793124777)
  ·
    refine ⟨10330274118658970844843583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13773698824878627793124777 10330274118658970844843583)
    ·
      refine ⟨15495411177988456267265375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330274118658970844843583 15495411177988456267265375)
      ·
        refine ⟨23243116766982684400898063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15495411177988456267265375 23243116766982684400898063)
        ·
          refine ⟨34864675150474026601347095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23243116766982684400898063 34864675150474026601347095)
          ·
            refine ⟨52297012725711039902020643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34864675150474026601347095 52297012725711039902020643)
            ·
              refine ⟨78445519088566559853030965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52297012725711039902020643 78445519088566559853030965)
              ·
                refine ⟨7354267414553114986221653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78445519088566559853030965 7354267414553114986221653)
                ·
                  refine ⟨86182821264294316244785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7354267414553114986221653 86182821264294316244785)
                  ·
                    rfl

theorem cell21_377641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_377641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377641 prefixEnd_377641 := by exact prefixLift 377641
  have htrace : WordTrace (prefixWord ++ tailWord_377641) baseStart_377641 baseEnd_377641 := by
    simpa [prefixWord, tailWord_377641, baseEnd_377641] using wordTrace_append hprefix tailTrace_377641
  have hstable : (prefixWord ++ tailWord_377641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377641).length < 2 ^ (prefixWord ++ tailWord_377641).sum := by decide
  have hdescent : baseEnd_377641 < baseStart_377641 := by decide
  rcases family_descends (prefixWord ++ tailWord_377641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377661 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_377661 : Nat := 118140960795 + 377661 * 2 ^ 59
def prefixEnd_377661 : Nat := 4983230072969 + 3 ^ 40 * 377661 * 2
def baseEnd_377661 : Nat := 86187385536778725911411

theorem tailTrace_377661 : CollatzResearch.WordTrace tailWord_377661 prefixEnd_377661 86187385536778725911411 := by
  unfold tailWord_377661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774428284806171208852837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9182952189870780805901891 13774428284806171208852837)
  ·
    refine ⟨2582705303401157101659907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13774428284806171208852837 2582705303401157101659907)
    ·
      refine ⟨3874057955101735652489861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582705303401157101659907 3874057955101735652489861)
      ·
        refine ⟨726385866581575434841849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3874057955101735652489861 726385866581575434841849)
        ·
          refine ⟨544789399936181576131387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726385866581575434841849 544789399936181576131387)
          ·
            refine ⟨817184099904272364197081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544789399936181576131387 817184099904272364197081)
            ·
              refine ⟨612888074928204273147811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817184099904272364197081 612888074928204273147811)
              ·
                refine ⟨919332112392306409721717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612888074928204273147811 919332112392306409721717)
                ·
                  refine ⟨86187385536778725911411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 919332112392306409721717 86187385536778725911411)
                  ·
                    rfl

theorem cell21_377661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_377661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377661 prefixEnd_377661 := by exact prefixLift 377661
  have htrace : WordTrace (prefixWord ++ tailWord_377661) baseStart_377661 baseEnd_377661 := by
    simpa [prefixWord, tailWord_377661, baseEnd_377661] using wordTrace_append hprefix tailTrace_377661
  have hstable : (prefixWord ++ tailWord_377661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377661).length < 2 ^ (prefixWord ++ tailWord_377661).sum := by decide
  have hdescent : baseEnd_377661 < baseStart_377661 := by decide
  rcases family_descends (prefixWord ++ tailWord_377661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377672 : List Nat := [2, 1, 3, 1, 1, 3, 2, 8]
def baseStart_377672 : Nat := 118140960795 + 377672 * 2 ^ 59
def prefixEnd_377672 : Nat := 4983230072969 + 3 ^ 40 * 377672 * 2
def baseEnd_377672 : Nat := 28729965295548383742685

theorem tailTrace_377672 : CollatzResearch.WordTrace tailWord_377672 prefixEnd_377672 28729965295548383742685 := by
  unfold tailWord_377672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887414743883160043751635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9183219658510880058335513 6887414743883160043751635)
  ·
    refine ⟨10331122115824740065627453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887414743883160043751635 10331122115824740065627453)
    ·
      refine ⟨3874170793434277524610295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10331122115824740065627453 3874170793434277524610295)
      ·
        refine ⟨5811256190151416286915443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874170793434277524610295 5811256190151416286915443)
        ·
          refine ⟨8716884285227124430373165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811256190151416286915443 8716884285227124430373165)
          ·
            refine ⟨3268831606960171661389937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8716884285227124430373165 3268831606960171661389937)
            ·
              refine ⟨2451623705220128746042453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3268831606960171661389937 2451623705220128746042453)
              ·
                refine ⟨28729965295548383742685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2451623705220128746042453 28729965295548383742685)
                ·
                  rfl

theorem cell21_377672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_377672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377672 prefixEnd_377672 := by exact prefixLift 377672
  have htrace : WordTrace (prefixWord ++ tailWord_377672) baseStart_377672 baseEnd_377672 := by
    simpa [prefixWord, tailWord_377672, baseEnd_377672] using wordTrace_append hprefix tailTrace_377672
  have hstable : (prefixWord ++ tailWord_377672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377672).length < 2 ^ (prefixWord ++ tailWord_377672).sum := by decide
  have hdescent : baseEnd_377672 < baseStart_377672 := by decide
  rcases family_descends (prefixWord ++ tailWord_377672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377689 : List Nat := [1, 2, 1, 2, 2, 4, 4, 5]
def baseStart_377689 : Nat := 118140960795 + 377689 * 2 ^ 59
def prefixEnd_377689 : Nat := 4983230072969 + 3 ^ 40 * 377689 * 2
def baseEnd_377689 : Nat := 28731258506085633148229

theorem tailTrace_377689 : CollatzResearch.WordTrace tailWord_377689 prefixEnd_377689 28731258506085633148229 := by
  unfold tailWord_377689
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775449528704731990872121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9183633019136487993914747 13775449528704731990872121)
  ·
    refine ⟨10331587146528548993154091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13775449528704731990872121 10331587146528548993154091)
    ·
      refine ⟨15497380719792823489731137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331587146528548993154091 15497380719792823489731137)
      ·
        refine ⟨11623035539844617617298353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15497380719792823489731137 11623035539844617617298353)
        ·
          refine ⟨8717276654883463212973765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11623035539844617617298353 8717276654883463212973765)
          ·
            refine ⟨1634489372790649352432581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8717276654883463212973765 1634489372790649352432581)
            ·
              refine ⟨306466757398246753581109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1634489372790649352432581 306466757398246753581109)
              ·
                refine ⟨28731258506085633148229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306466757398246753581109 28731258506085633148229)
                ·
                  rfl

theorem cell21_377689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 5].length) (baseStart_377689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377689 prefixEnd_377689 := by exact prefixLift 377689
  have htrace : WordTrace (prefixWord ++ tailWord_377689) baseStart_377689 baseEnd_377689 := by
    simpa [prefixWord, tailWord_377689, baseEnd_377689] using wordTrace_append hprefix tailTrace_377689
  have hstable : (prefixWord ++ tailWord_377689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377689).length < 2 ^ (prefixWord ++ tailWord_377689).sum := by decide
  have hdescent : baseEnd_377689 < baseStart_377689 := by decide
  rcases family_descends (prefixWord ++ tailWord_377689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377726 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_377726 : Nat := 118140960795 + 377726 * 2 ^ 59
def prefixEnd_377726 : Nat := 4983230072969 + 3 ^ 40 * 377726 * 2
def baseEnd_377726 : Nat := 86202219422353057327945

theorem tailTrace_377726 : CollatzResearch.WordTrace tailWord_377726 prefixEnd_377726 86202219422353057327945 := by
  unfold tailWord_377726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722099878696335913746129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9184532686380458206646021 1722099878696335913746129)
  ·
    refine ⟨1291574909022251935309597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1722099878696335913746129 1291574909022251935309597)
    ·
      refine ⟨484340590883344475741099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1291574909022251935309597 484340590883344475741099)
      ·
        refine ⟨726510886325016713611649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484340590883344475741099 726510886325016713611649)
        ·
          refine ⟨544883164743762535208737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726510886325016713611649 544883164743762535208737)
          ·
            refine ⟨408662373557821901406553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544883164743762535208737 408662373557821901406553)
            ·
              refine ⟨306496780168366426054915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408662373557821901406553 306496780168366426054915)
              ·
                refine ⟨459745170252549639082373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306496780168366426054915 459745170252549639082373)
                ·
                  refine ⟨86202219422353057327945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459745170252549639082373 86202219422353057327945)
                  ·
                    rfl

theorem cell21_377726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_377726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377726 prefixEnd_377726 := by exact prefixLift 377726
  have htrace : WordTrace (prefixWord ++ tailWord_377726) baseStart_377726 baseEnd_377726 := by
    simpa [prefixWord, tailWord_377726, baseEnd_377726] using wordTrace_append hprefix tailTrace_377726
  have hstable : (prefixWord ++ tailWord_377726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377726).length < 2 ^ (prefixWord ++ tailWord_377726).sum := by decide
  have hdescent : baseEnd_377726 < baseStart_377726 := by decide
  rcases family_descends (prefixWord ++ tailWord_377726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377900 : List Nat := [2, 2, 1, 1, 1, 2, 6, 6]
def baseStart_377900 : Nat := 118140960795 + 377900 * 2 ^ 59
def prefixEnd_377900 : Nat := 4983230072969 + 3 ^ 40 * 377900 * 2
def baseEnd_377900 : Nat := 28747309530989140475863

theorem tailTrace_377900 : CollatzResearch.WordTrace tailWord_377900 prefixEnd_377900 28747309530989140475863 := by
  unfold tailWord_377900
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891572665470157513401577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9188763553960210017868769 6891572665470157513401577)
  ·
    refine ⟨5168679499102618135051183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6891572665470157513401577 5168679499102618135051183)
    ·
      refine ⟨7753019248653927202576775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5168679499102618135051183 7753019248653927202576775)
      ·
        refine ⟨11629528872980890803865163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753019248653927202576775 11629528872980890803865163)
        ·
          refine ⟨17444293309471336205797745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11629528872980890803865163 17444293309471336205797745)
          ·
            refine ⟨13083219982103502154348309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17444293309471336205797745 13083219982103502154348309)
            ·
              refine ⟨613275936661101663485077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13083219982103502154348309 613275936661101663485077)
              ·
                refine ⟨28747309530989140475863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 613275936661101663485077 28747309530989140475863)
                ·
                  rfl

theorem cell21_377900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_377900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_377900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_377900 prefixEnd_377900 := by exact prefixLift 377900
  have htrace : WordTrace (prefixWord ++ tailWord_377900) baseStart_377900 baseEnd_377900 := by
    simpa [prefixWord, tailWord_377900, baseEnd_377900] using wordTrace_append hprefix tailTrace_377900
  have hstable : (prefixWord ++ tailWord_377900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377900).length < 2 ^ (prefixWord ++ tailWord_377900).sum := by decide
  have hdescent : baseEnd_377900 < baseStart_377900 := by decide
  rcases family_descends (prefixWord ++ tailWord_377900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378007 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_378007 : Nat := 118140960795 + 378007 * 2 ^ 59
def prefixEnd_378007 : Nat := 4983230072969 + 3 ^ 40 * 378007 * 2
def baseEnd_378007 : Nat := 86266347450759013144037

theorem tailTrace_378007 : CollatzResearch.WordTrace tailWord_378007 prefixEnd_378007 86266347450759013144037 := by
  unfold tailWord_378007
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787047941552672300948275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9191365294368448200632183 13787047941552672300948275)
  ·
    refine ⟨20680571912329008451422413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13787047941552672300948275 20680571912329008451422413)
    ·
      refine ⟨7755214467123378169283405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20680571912329008451422413 7755214467123378169283405)
      ·
        refine ⟨2908205425171266813481277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7755214467123378169283405 2908205425171266813481277)
        ·
          refine ⟨1090577034439225055055479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2908205425171266813481277 1090577034439225055055479)
          ·
            refine ⟨1635865551658837582583219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090577034439225055055479 1635865551658837582583219)
            ·
              refine ⟨2453798327488256373874829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635865551658837582583219 2453798327488256373874829)
              ·
                refine ⟨920174372808096140203061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453798327488256373874829 920174372808096140203061)
                ·
                  refine ⟨86266347450759013144037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 920174372808096140203061 86266347450759013144037)
                  ·
                    rfl

theorem cell21_378007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_378007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378007 prefixEnd_378007 := by exact prefixLift 378007
  have htrace : WordTrace (prefixWord ++ tailWord_378007) baseStart_378007 baseEnd_378007 := by
    simpa [prefixWord, tailWord_378007, baseEnd_378007] using wordTrace_append hprefix tailTrace_378007
  have hstable : (prefixWord ++ tailWord_378007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378007).length < 2 ^ (prefixWord ++ tailWord_378007).sum := by decide
  have hdescent : baseEnd_378007 < baseStart_378007 := by decide
  rcases family_descends (prefixWord ++ tailWord_378007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378041 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 3]
def baseStart_378041 : Nat := 118140960795 + 378041 * 2 ^ 59
def prefixEnd_378041 : Nat := 4983230072969 + 3 ^ 40 * 378041 * 2
def baseEnd_378041 : Nat := 86274106713982509577301

theorem tailTrace_378041 : CollatzResearch.WordTrace tailWord_378041 prefixEnd_378041 86274106713982509577301 := by
  unfold tailWord_378041
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788288023429496107685977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9192192015619664071790651 13788288023429496107685977)
  ·
    refine ⟨10341216017572122080764483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13788288023429496107685977 10341216017572122080764483)
    ·
      refine ⟨15511824026358183121146725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10341216017572122080764483 15511824026358183121146725)
      ·
        refine ⟨2908467004942159335215011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15511824026358183121146725 2908467004942159335215011)
        ·
          refine ⟨4362700507413239002822517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908467004942159335215011 4362700507413239002822517)
          ·
            refine ⟨409003172569991156514611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4362700507413239002822517 409003172569991156514611)
            ·
              refine ⟨613504758854986734771917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409003172569991156514611 613504758854986734771917)
              ·
                refine ⟨230064284570620025539469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613504758854986734771917 230064284570620025539469)
                ·
                  refine ⟨86274106713982509577301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230064284570620025539469 86274106713982509577301)
                  ·
                    rfl

theorem cell21_378041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_378041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378041 prefixEnd_378041 := by exact prefixLift 378041
  have htrace : WordTrace (prefixWord ++ tailWord_378041) baseStart_378041 baseEnd_378041 := by
    simpa [prefixWord, tailWord_378041, baseEnd_378041] using wordTrace_append hprefix tailTrace_378041
  have hstable : (prefixWord ++ tailWord_378041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378041).length < 2 ^ (prefixWord ++ tailWord_378041).sum := by decide
  have hdescent : baseEnd_378041 < baseStart_378041 := by decide
  rcases family_descends (prefixWord ++ tailWord_378041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378069 : List Nat := [1, 3, 2, 4, 1, 2, 2, 6]
def baseStart_378069 : Nat := 118140960795 + 378069 * 2 ^ 59
def prefixEnd_378069 : Nat := 4983230072969 + 3 ^ 40 * 378069 * 2
def baseEnd_378069 : Nat := 28760165565153561036859

theorem tailTrace_378069 : CollatzResearch.WordTrace tailWord_378069 prefixEnd_378069 28760165565153561036859 := by
  unfold tailWord_378069
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789309267328056889705261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9192872844885371259803507 13789309267328056889705261)
  ·
    refine ⟨5170990975248021333639473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13789309267328056889705261 5170990975248021333639473)
    ·
      refine ⟨3878243231436016000229605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170990975248021333639473 3878243231436016000229605)
      ·
        refine ⟨727170605894253000043051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3878243231436016000229605 727170605894253000043051)
        ·
          refine ⟨1090755908841379500064577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727170605894253000043051 1090755908841379500064577)
          ·
            refine ⟨818066931631034625048433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090755908841379500064577 818066931631034625048433)
            ·
              refine ⟨613550198723275968786325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818066931631034625048433 613550198723275968786325)
              ·
                refine ⟨28760165565153561036859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 613550198723275968786325 28760165565153561036859)
                ·
                  rfl

theorem cell21_378069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_378069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378069 prefixEnd_378069 := by exact prefixLift 378069
  have htrace : WordTrace (prefixWord ++ tailWord_378069) baseStart_378069 baseEnd_378069 := by
    simpa [prefixWord, tailWord_378069, baseEnd_378069] using wordTrace_append hprefix tailTrace_378069
  have hstable : (prefixWord ++ tailWord_378069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378069).length < 2 ^ (prefixWord ++ tailWord_378069).sum := by decide
  have hdescent : baseEnd_378069 < baseStart_378069 := by decide
  rcases family_descends (prefixWord ++ tailWord_378069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378072 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_378072 : Nat := 118140960795 + 378072 * 2 ^ 59
def prefixEnd_378072 : Nat := 4983230072969 + 3 ^ 40 * 378072 * 2
def baseEnd_378072 : Nat := 86281181336333344560571

theorem tailTrace_378072 : CollatzResearch.WordTrace tailWord_378072 prefixEnd_378072 86281181336333344560571 := by
  unfold tailWord_378072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6894709343158594201032235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9192945790878125601376313 6894709343158594201032235)
  ·
    refine ⟨10342064014737891301548353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6894709343158594201032235 10342064014737891301548353)
    ·
      refine ⟨7756548011053418476161265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10342064014737891301548353 7756548011053418476161265)
      ·
        refine ⟨5817411008290063857120949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756548011053418476161265 5817411008290063857120949)
        ·
          refine ⟨545382282027193486605089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5817411008290063857120949 545382282027193486605089)
          ·
            refine ⟨409036711520395114953817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545382282027193486605089 409036711520395114953817)
            ·
              refine ⟨306777533640296336215363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409036711520395114953817 306777533640296336215363)
              ·
                refine ⟨460166300460444504323045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306777533640296336215363 460166300460444504323045)
                ·
                  refine ⟨86281181336333344560571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460166300460444504323045 86281181336333344560571)
                  ·
                    rfl

theorem cell21_378072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_378072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378072 prefixEnd_378072 := by exact prefixLift 378072
  have htrace : WordTrace (prefixWord ++ tailWord_378072) baseStart_378072 baseEnd_378072 := by
    simpa [prefixWord, tailWord_378072, baseEnd_378072] using wordTrace_append hprefix tailTrace_378072
  have hstable : (prefixWord ++ tailWord_378072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378072).length < 2 ^ (prefixWord ++ tailWord_378072).sum := by decide
  have hdescent : baseEnd_378072 < baseStart_378072 := by decide
  rcases family_descends (prefixWord ++ tailWord_378072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378111 : List Nat := [1, 1, 2, 2, 1, 14]
def baseStart_378111 : Nat := 118140960795 + 378111 * 2 ^ 59
def prefixEnd_378111 : Nat := 4983230072969 + 3 ^ 40 * 378111 * 2
def baseEnd_378111 : Nat := 3195928950654738644833

theorem tailTrace_378111 : CollatzResearch.WordTrace tailWord_378111 prefixEnd_378111 3195928950654738644833 := by
  unfold tailWord_378111
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790841133175898062734187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9193894088783932041822791 13790841133175898062734187)
  ·
    refine ⟨20686261699763847094101281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13790841133175898062734187 20686261699763847094101281)
    ·
      refine ⟨15514696274822885320575961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20686261699763847094101281 15514696274822885320575961)
      ·
        refine ⟨11636022206117163990431971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15514696274822885320575961 11636022206117163990431971)
        ·
          refine ⟨17454033309175745985647957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11636022206117163990431971 17454033309175745985647957)
          ·
            refine ⟨3195928950654738644833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 17454033309175745985647957 3195928950654738644833)
            ·
              rfl

theorem cell21_378111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 14].length) (baseStart_378111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378111 prefixEnd_378111 := by exact prefixLift 378111
  have htrace : WordTrace (prefixWord ++ tailWord_378111) baseStart_378111 baseEnd_378111 := by
    simpa [prefixWord, tailWord_378111, baseEnd_378111] using wordTrace_append hprefix tailTrace_378111
  have hstable : (prefixWord ++ tailWord_378111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378111).length < 2 ^ (prefixWord ++ tailWord_378111).sum := by decide
  have hdescent : baseEnd_378111 < baseStart_378111 := by decide
  rcases family_descends (prefixWord ++ tailWord_378111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378182 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_378182 : Nat := 118140960795 + 378182 * 2 ^ 59
def prefixEnd_378182 : Nat := 4983230072969 + 3 ^ 40 * 378182 * 2
def baseEnd_378182 : Nat := 86306284834997597727013

theorem tailTrace_378182 : CollatzResearch.WordTrace tailWord_378182 prefixEnd_378182 86306284834997597727013 := by
  unfold tailWord_378182
  simp only [CollatzResearch.WordTrace]
  refine ⟨431044709872458662142775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9195620477279118125712533 431044709872458662142775)
  ·
    refine ⟨646567064808687993214163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431044709872458662142775 646567064808687993214163)
    ·
      refine ⟨969850597213031989821245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646567064808687993214163 969850597213031989821245)
      ·
        refine ⟨363693973954886996182967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 969850597213031989821245 363693973954886996182967)
        ·
          refine ⟨545540960932330494274451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363693973954886996182967 545540960932330494274451)
          ·
            refine ⟨818311441398495741411677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545540960932330494274451 818311441398495741411677)
            ·
              refine ⟨306866790524435903029379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818311441398495741411677 306866790524435903029379)
              ·
                refine ⟨460300185786653854544069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306866790524435903029379 460300185786653854544069)
                ·
                  refine ⟨86306284834997597727013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460300185786653854544069 86306284834997597727013)
                  ·
                    rfl

theorem cell21_378182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_378182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378182 prefixEnd_378182 := by exact prefixLift 378182
  have htrace : WordTrace (prefixWord ++ tailWord_378182) baseStart_378182 baseEnd_378182 := by
    simpa [prefixWord, tailWord_378182, baseEnd_378182] using wordTrace_append hprefix tailTrace_378182
  have hstable : (prefixWord ++ tailWord_378182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378182).length < 2 ^ (prefixWord ++ tailWord_378182).sum := by decide
  have hdescent : baseEnd_378182 < baseStart_378182 := by decide
  rcases family_descends (prefixWord ++ tailWord_378182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378241 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 4]
def baseStart_378241 : Nat := 118140960795 + 378241 * 2 ^ 59
def prefixEnd_378241 : Nat := 4983230072969 + 3 ^ 40 * 378241 * 2
def baseEnd_378241 : Nat := 86319749438826606243559

theorem tailTrace_378241 : CollatzResearch.WordTrace tailWord_378241 prefixEnd_378241 86319749438826606243559 := by
  unfold tailWord_378241
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795582622704930264966577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9197055081803286843311051 13795582622704930264966577)
  ·
    refine ⟨10346686967028697698724933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13795582622704930264966577 10346686967028697698724933)
    ·
      refine ⟨1940003806317880818510925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10346686967028697698724933 1940003806317880818510925)
      ·
        refine ⟨727501427369205306941597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1940003806317880818510925 727501427369205306941597)
        ·
          refine ⟨272813035263451990103099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727501427369205306941597 272813035263451990103099)
          ·
            refine ⟨409219552895177985154649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272813035263451990103099 409219552895177985154649)
            ·
              refine ⟨306914664671383488865987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409219552895177985154649 306914664671383488865987)
              ·
                refine ⟨460371997007075233298981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306914664671383488865987 460371997007075233298981)
                ·
                  refine ⟨86319749438826606243559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460371997007075233298981 86319749438826606243559)
                  ·
                    rfl

theorem cell21_378241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_378241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378241 prefixEnd_378241 := by exact prefixLift 378241
  have htrace : WordTrace (prefixWord ++ tailWord_378241) baseStart_378241 baseEnd_378241 := by
    simpa [prefixWord, tailWord_378241, baseEnd_378241] using wordTrace_append hprefix tailTrace_378241
  have hstable : (prefixWord ++ tailWord_378241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378241).length < 2 ^ (prefixWord ++ tailWord_378241).sum := by decide
  have hdescent : baseEnd_378241 < baseStart_378241 := by decide
  rcases family_descends (prefixWord ++ tailWord_378241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378280 : List Nat := [2, 1, 6, 1, 11]
def baseStart_378280 : Nat := 118140960795 + 378280 * 2 ^ 59
def prefixEnd_378280 : Nat := 4983230072969 + 3 ^ 40 * 378280 * 2
def baseEnd_378280 : Nat := 1065785799631743272759

theorem tailTrace_378280 : CollatzResearch.WordTrace tailWord_378280 prefixEnd_378280 1065785799631743272759 := by
  unfold tailWord_378280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898502534781819962818147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9198003379709093283757529 6898502534781819962818147)
  ·
    refine ⟨10347753802172729944227221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6898502534781819962818147 10347753802172729944227221)
    ·
      refine ⟨485050959476846716135651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10347753802172729944227221 485050959476846716135651)
      ·
        refine ⟨727576439215270074203477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485050959476846716135651 727576439215270074203477)
        ·
          refine ⟨1065785799631743272759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 727576439215270074203477 1065785799631743272759)
          ·
            rfl

theorem cell21_378280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 11].length) (baseStart_378280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378280 prefixEnd_378280 := by exact prefixLift 378280
  have htrace : WordTrace (prefixWord ++ tailWord_378280) baseStart_378280 baseEnd_378280 := by
    simpa [prefixWord, tailWord_378280, baseEnd_378280] using wordTrace_append hprefix tailTrace_378280
  have hstable : (prefixWord ++ tailWord_378280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378280).length < 2 ^ (prefixWord ++ tailWord_378280).sum := by decide
  have hdescent : baseEnd_378280 < baseStart_378280 := by decide
  rcases family_descends (prefixWord ++ tailWord_378280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378297 : List Nat := [1, 2, 1, 4, 4, 2, 1, 6]
def baseStart_378297 : Nat := 118140960795 + 378297 * 2 ^ 59
def prefixEnd_378297 : Nat := 4983230072969 + 3 ^ 40 * 378297 * 2
def baseEnd_378297 : Nat := 28777509800594317770037

theorem tailTrace_378297 : CollatzResearch.WordTrace tailWord_378297 prefixEnd_378297 28777509800594317770037 := by
  unfold tailWord_378297
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797625110502051829005145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9198416740334701219336763 13797625110502051829005145)
  ·
    refine ⟨10348218832876538871753859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13797625110502051829005145 10348218832876538871753859)
    ·
      refine ⟨15522328249314808307630789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10348218832876538871753859 15522328249314808307630789)
      ·
        refine ⟨2910436546746526557680773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15522328249314808307630789 2910436546746526557680773)
        ·
          refine ⟨545706852514973729565145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2910436546746526557680773 545706852514973729565145)
          ·
            refine ⟨409280139386230297173859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545706852514973729565145 409280139386230297173859)
            ·
              refine ⟨613920209079345445760789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409280139386230297173859 613920209079345445760789)
              ·
                refine ⟨28777509800594317770037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 613920209079345445760789 28777509800594317770037)
                ·
                  rfl

theorem cell21_378297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 6].length) (baseStart_378297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378297 prefixEnd_378297 := by exact prefixLift 378297
  have htrace : WordTrace (prefixWord ++ tailWord_378297) baseStart_378297 baseEnd_378297 := by
    simpa [prefixWord, tailWord_378297, baseEnd_378297] using wordTrace_append hprefix tailTrace_378297
  have hstable : (prefixWord ++ tailWord_378297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378297).length < 2 ^ (prefixWord ++ tailWord_378297).sum := by decide
  have hdescent : baseEnd_378297 < baseStart_378297 := by decide
  rcases family_descends (prefixWord ++ tailWord_378297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378325 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_378325 : Nat := 118140960795 + 378325 * 2 ^ 59
def prefixEnd_378325 : Nat := 4983230072969 + 3 ^ 40 * 378325 * 2
def baseEnd_378325 : Nat := 86338919383261126843387

theorem tailTrace_378325 : CollatzResearch.WordTrace tailWord_378325 prefixEnd_378325 86338919383261126843387 := by
  unfold tailWord_378325
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798646354400612611024429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9199097569600408407349619 13798646354400612611024429)
  ·
    refine ⟨5174492382900229729134161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13798646354400612611024429 5174492382900229729134161)
    ·
      refine ⟨3880869287175172296850621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5174492382900229729134161 3880869287175172296850621)
      ·
        refine ⟨1455325982690689611318983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3880869287175172296850621 1455325982690689611318983)
        ·
          refine ⟨2182988974036034416978475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455325982690689611318983 2182988974036034416978475)
          ·
            refine ⟨3274483461054051625467713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182988974036034416978475 3274483461054051625467713)
            ·
              refine ⟨2455862595790538719100785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274483461054051625467713 2455862595790538719100785)
              ·
                refine ⟨1841896946842904039325589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455862595790538719100785 1841896946842904039325589)
                ·
                  refine ⟨86338919383261126843387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1841896946842904039325589 86338919383261126843387)
                  ·
                    rfl

theorem cell21_378325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_378325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378325 prefixEnd_378325 := by exact prefixLift 378325
  have htrace : WordTrace (prefixWord ++ tailWord_378325) baseStart_378325 baseEnd_378325 := by
    simpa [prefixWord, tailWord_378325, baseEnd_378325] using wordTrace_append hprefix tailTrace_378325
  have hstable : (prefixWord ++ tailWord_378325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378325).length < 2 ^ (prefixWord ++ tailWord_378325).sum := by decide
  have hdescent : baseEnd_378325 < baseStart_378325 := by decide
  rcases family_descends (prefixWord ++ tailWord_378325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378401 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_378401 : Nat := 118140960795 + 378401 * 2 ^ 59
def prefixEnd_378401 : Nat := 4983230072969 + 3 ^ 40 * 378401 * 2
def baseEnd_378401 : Nat := 86356263618701883576565

theorem tailTrace_378401 : CollatzResearch.WordTrace tailWord_378401 prefixEnd_378401 86356263618701883576565 := by
  unfold tailWord_378401
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801418302125277590791057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9200945534750185060527371 13801418302125277590791057)
  ·
    refine ⟨10351063726593958193093293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13801418302125277590791057 10351063726593958193093293)
    ·
      refine ⟨3881648897472734322409985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10351063726593958193093293 3881648897472734322409985)
      ·
        refine ⟨2911236673104550741807489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3881648897472734322409985 2911236673104550741807489)
        ·
          refine ⟨2183427504828413056355617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911236673104550741807489 2183427504828413056355617)
          ·
            refine ⟨1637570628621309792266713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183427504828413056355617 1637570628621309792266713)
            ·
              refine ⟨1228177971465982344200035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637570628621309792266713 1228177971465982344200035)
              ·
                refine ⟨1842266957198973516300053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228177971465982344200035 1842266957198973516300053)
                ·
                  refine ⟨86356263618701883576565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1842266957198973516300053 86356263618701883576565)
                  ·
                    rfl

theorem cell21_378401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_378401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378401 prefixEnd_378401 := by exact prefixLift 378401
  have htrace : WordTrace (prefixWord ++ tailWord_378401) baseStart_378401 baseEnd_378401 := by
    simpa [prefixWord, tailWord_378401, baseEnd_378401] using wordTrace_append hprefix tailTrace_378401
  have hstable : (prefixWord ++ tailWord_378401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378401).length < 2 ^ (prefixWord ++ tailWord_378401).sum := by decide
  have hdescent : baseEnd_378401 < baseStart_378401 := by decide
  rcases family_descends (prefixWord ++ tailWord_378401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378556 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_378556 : Nat := 118140960795 + 378556 * 2 ^ 59
def prefixEnd_378556 : Nat := 4983230072969 + 3 ^ 40 * 378556 * 2
def baseEnd_378556 : Nat := 86391636730456058492915

theorem tailTrace_378556 : CollatzResearch.WordTrace tailWord_378556 prefixEnd_378556 86391636730456058492915 := by
  unfold tailWord_378556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903535808281869531341761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9204714411042492708455681 6903535808281869531341761)
  ·
    refine ⟨5177651856211402148506321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6903535808281869531341761 5177651856211402148506321)
    ·
      refine ⟨3883238892158551611379741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5177651856211402148506321 3883238892158551611379741)
      ·
        refine ⟨1456214584559456854267403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3883238892158551611379741 1456214584559456854267403)
        ·
          refine ⟨2184321876839185281401105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456214584559456854267403 2184321876839185281401105)
          ·
            refine ⟨1638241407629388961050829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184321876839185281401105 1638241407629388961050829)
            ·
              refine ⟨614340527861020860394061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638241407629388961050829 614340527861020860394061)
              ·
                refine ⟨230377697947882822647773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 614340527861020860394061 230377697947882822647773)
                ·
                  refine ⟨86391636730456058492915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230377697947882822647773 86391636730456058492915)
                  ·
                    rfl

theorem cell21_378556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_378556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378556 prefixEnd_378556 := by exact prefixLift 378556
  have htrace : WordTrace (prefixWord ++ tailWord_378556) baseStart_378556 baseEnd_378556 := by
    simpa [prefixWord, tailWord_378556, baseEnd_378556] using wordTrace_append hprefix tailTrace_378556
  have hstable : (prefixWord ++ tailWord_378556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378556).length < 2 ^ (prefixWord ++ tailWord_378556).sum := by decide
  have hdescent : baseEnd_378556 < baseStart_378556 := by decide
  rcases family_descends (prefixWord ++ tailWord_378556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378573 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 5]
def baseStart_378573 : Nat := 118140960795 + 378573 * 2 ^ 59
def prefixEnd_378573 : Nat := 4983230072969 + 3 ^ 40 * 378573 * 2
def baseEnd_378573 : Nat := 86395516362067806709547

theorem tailTrace_378573 : CollatzResearch.WordTrace tailWord_378573 prefixEnd_378573 86395516362067806709547 := by
  unfold tailWord_378573
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807691657502150966052373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9205127771668100644034915 13807691657502150966052373)
  ·
    refine ⟨647235546445413326533705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13807691657502150966052373 647235546445413326533705)
    ·
      refine ⟨485426659834059994900279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 647235546445413326533705 485426659834059994900279)
      ·
        refine ⟨728139989751089992350419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485426659834059994900279 728139989751089992350419)
        ·
          refine ⟨1092209984626634988525629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728139989751089992350419 1092209984626634988525629)
          ·
            refine ⟨409578744234988120697111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1092209984626634988525629 409578744234988120697111)
            ·
              refine ⟨614368116352482181045667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409578744234988120697111 614368116352482181045667)
              ·
                refine ⟨921552174528723271568501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614368116352482181045667 921552174528723271568501)
                ·
                  refine ⟨86395516362067806709547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 921552174528723271568501 86395516362067806709547)
                  ·
                    rfl

theorem cell21_378573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_378573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378573 prefixEnd_378573 := by exact prefixLift 378573
  have htrace : WordTrace (prefixWord ++ tailWord_378573) baseStart_378573 baseEnd_378573 := by
    simpa [prefixWord, tailWord_378573, baseEnd_378573] using wordTrace_append hprefix tailTrace_378573
  have hstable : (prefixWord ++ tailWord_378573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378573).length < 2 ^ (prefixWord ++ tailWord_378573).sum := by decide
  have hdescent : baseEnd_378573 < baseStart_378573 := by decide
  rcases family_descends (prefixWord ++ tailWord_378573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378691 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 3]
def baseStart_378691 : Nat := 118140960795 + 378691 * 2 ^ 59
def prefixEnd_378691 : Nat := 4983230072969 + 3 ^ 40 * 378691 * 2
def baseEnd_378691 : Nat := 86422445569725823742639

theorem tailTrace_378691 : CollatzResearch.WordTrace tailWord_378691 prefixEnd_378691 86422445569725823742639 := by
  unfold tailWord_378691
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811995471074657118847927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9207996980716438079231951 13811995471074657118847927)
  ·
    refine ⟨20717993206611985678271891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13811995471074657118847927 20717993206611985678271891)
    ·
      refine ⟨31076989809917978517407837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717993206611985678271891 31076989809917978517407837)
      ·
        refine ⟨11653871178719241944027939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31076989809917978517407837 11653871178719241944027939)
        ·
          refine ⟨17480806768078862916041909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11653871178719241944027939 17480806768078862916041909)
          ·
            refine ⟨1638825634507393398378929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17480806768078862916041909 1638825634507393398378929)
            ·
              refine ⟨1229119225880545048784197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638825634507393398378929 1229119225880545048784197)
              ·
                refine ⟨230459854852602196647037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1229119225880545048784197 230459854852602196647037)
                ·
                  refine ⟨86422445569725823742639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230459854852602196647037 86422445569725823742639)
                  ·
                    rfl

theorem cell21_378691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3].length) (baseStart_378691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378691 prefixEnd_378691 := by exact prefixLift 378691
  have htrace : WordTrace (prefixWord ++ tailWord_378691) baseStart_378691 baseEnd_378691 := by
    simpa [prefixWord, tailWord_378691, baseEnd_378691] using wordTrace_append hprefix tailTrace_378691
  have hstable : (prefixWord ++ tailWord_378691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378691).length < 2 ^ (prefixWord ++ tailWord_378691).sum := by decide
  have hdescent : baseEnd_378691 < baseStart_378691 := by decide
  rcases family_descends (prefixWord ++ tailWord_378691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378719 : List Nat := [1, 1, 2, 3, 1, 5, 1, 7]
def baseStart_378719 : Nat := 118140960795 + 378719 * 2 ^ 59
def prefixEnd_378719 : Nat := 4983230072969 + 3 ^ 40 * 378719 * 2
def baseEnd_378719 : Nat := 28809611850401332425305

theorem tailTrace_378719 : CollatzResearch.WordTrace tailWord_378719 prefixEnd_378719 28809611850401332425305 := by
  unfold tailWord_378719
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813016714973217900867211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9208677809982145267244807 13813016714973217900867211)
  ·
    refine ⟨20719525072459826851300817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13813016714973217900867211 20719525072459826851300817)
    ·
      refine ⟨15539643804344870138475613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20719525072459826851300817 15539643804344870138475613)
      ·
        refine ⟨5827366426629326301928355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15539643804344870138475613 5827366426629326301928355)
        ·
          refine ⟨8741049639943989452892533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827366426629326301928355 8741049639943989452892533)
          ·
            refine ⟨819473403744749011208675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8741049639943989452892533 819473403744749011208675)
            ·
              refine ⟨1229210105617123516813013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819473403744749011208675 1229210105617123516813013)
              ·
                refine ⟨28809611850401332425305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1229210105617123516813013 28809611850401332425305)
                ·
                  rfl

theorem cell21_378719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_378719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378719 prefixEnd_378719 := by exact prefixLift 378719
  have htrace : WordTrace (prefixWord ++ tailWord_378719) baseStart_378719 baseEnd_378719 := by
    simpa [prefixWord, tailWord_378719, baseEnd_378719] using wordTrace_append hprefix tailTrace_378719
  have hstable : (prefixWord ++ tailWord_378719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378719).length < 2 ^ (prefixWord ++ tailWord_378719).sum := by decide
  have hdescent : baseEnd_378719 < baseStart_378719 := by decide
  rcases family_descends (prefixWord ++ tailWord_378719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378742 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_378742 : Nat := 118140960795 + 378742 * 2 ^ 59
def prefixEnd_378742 : Nat := 4983230072969 + 3 ^ 40 * 378742 * 2
def baseEnd_378742 : Nat := 86434084464561068392535

theorem tailTrace_378742 : CollatzResearch.WordTrace tailWord_378742 prefixEnd_378742 86434084464561068392535 := by
  unfold tailWord_378742
  simp only [CollatzResearch.WordTrace]
  refine ⟨863365974618118301809655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9209237062593261885969653 863365974618118301809655)
  ·
    refine ⟨1295048961927177452714483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863365974618118301809655 1295048961927177452714483)
    ·
      refine ⟨1942573442890766179071725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295048961927177452714483 1942573442890766179071725)
      ·
        refine ⟨728465041084037317151897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1942573442890766179071725 728465041084037317151897)
        ·
          refine ⟨546348780813027987863923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728465041084037317151897 546348780813027987863923)
          ·
            refine ⟨819523171219541981795885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546348780813027987863923 819523171219541981795885)
            ·
              refine ⟨307321189207328243173457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819523171219541981795885 307321189207328243173457)
              ·
                refine ⟨230490891905496182380093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307321189207328243173457 230490891905496182380093)
                ·
                  refine ⟨86434084464561068392535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230490891905496182380093 86434084464561068392535)
                  ·
                    rfl

theorem cell21_378742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_378742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378742 prefixEnd_378742 := by exact prefixLift 378742
  have htrace : WordTrace (prefixWord ++ tailWord_378742) baseStart_378742 baseEnd_378742 := by
    simpa [prefixWord, tailWord_378742, baseEnd_378742] using wordTrace_append hprefix tailTrace_378742
  have hstable : (prefixWord ++ tailWord_378742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378742).length < 2 ^ (prefixWord ++ tailWord_378742).sum := by decide
  have hdescent : baseEnd_378742 < baseStart_378742 := by decide
  rcases family_descends (prefixWord ++ tailWord_378742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378753 : List Nat := [1, 2, 4, 4, 1, 1, 2, 6]
def baseStart_378753 : Nat := 118140960795 + 378753 * 2 ^ 59
def prefixEnd_378753 : Nat := 4983230072969 + 3 ^ 40 * 378753 * 2
def baseEnd_378753 : Nat := 28812198271475831236393

theorem tailTrace_378753 : CollatzResearch.WordTrace tailWord_378753 prefixEnd_378753 28812198271475831236393 := by
  unfold tailWord_378753
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814256796850041707604913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9209504531233361138403275 13814256796850041707604913)
  ·
    refine ⟨10360692597637531280703685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13814256796850041707604913 10360692597637531280703685)
    ·
      refine ⟨1942629862057037115131941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10360692597637531280703685 1942629862057037115131941)
      ·
        refine ⟨364243099135694459087239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1942629862057037115131941 364243099135694459087239)
        ·
          refine ⟨546364648703541688630859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364243099135694459087239 546364648703541688630859)
          ·
            refine ⟨819546973055312532946289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546364648703541688630859 819546973055312532946289)
            ·
              refine ⟨614660229791484399709717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819546973055312532946289 614660229791484399709717)
              ·
                refine ⟨28812198271475831236393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 614660229791484399709717 28812198271475831236393)
                ·
                  rfl

theorem cell21_378753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 6].length) (baseStart_378753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378753 prefixEnd_378753 := by exact prefixLift 378753
  have htrace : WordTrace (prefixWord ++ tailWord_378753) baseStart_378753 baseEnd_378753 := by
    simpa [prefixWord, tailWord_378753, baseEnd_378753] using wordTrace_append hprefix tailTrace_378753
  have hstable : (prefixWord ++ tailWord_378753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378753).length < 2 ^ (prefixWord ++ tailWord_378753).sum := by decide
  have hdescent : baseEnd_378753 < baseStart_378753 := by decide
  rcases family_descends (prefixWord ++ tailWord_378753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378801 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 3]
def baseStart_378801 : Nat := 118140960795 + 378801 * 2 ^ 59
def prefixEnd_378801 : Nat := 4983230072969 + 3 ^ 40 * 378801 * 2
def baseEnd_378801 : Nat := 86447549068390076909081

theorem tailTrace_378801 : CollatzResearch.WordTrace tailWord_378801 prefixEnd_378801 86447549068390076909081 := by
  unfold tailWord_378801
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816007500676145905352257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9210671667117430603568171 13816007500676145905352257)
  ·
    refine ⟨10362005625507109429014193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13816007500676145905352257 10362005625507109429014193)
    ·
      refine ⟨7771504219130332071760645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10362005625507109429014193 7771504219130332071760645)
      ·
        refine ⟨1457157041086937263455121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7771504219130332071760645 1457157041086937263455121)
        ·
          refine ⟨1092867780815202947591341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1457157041086937263455121 1092867780815202947591341)
          ·
            refine ⟨409825417805701105346753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1092867780815202947591341 409825417805701105346753)
            ·
              refine ⟨307369063354275829010065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409825417805701105346753 307369063354275829010065)
              ·
                refine ⟨230526797515706871757549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307369063354275829010065 230526797515706871757549)
                ·
                  refine ⟨86447549068390076909081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230526797515706871757549 86447549068390076909081)
                  ·
                    rfl

theorem cell21_378801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_378801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378801 prefixEnd_378801 := by exact prefixLift 378801
  have htrace : WordTrace (prefixWord ++ tailWord_378801) baseStart_378801 baseEnd_378801 := by
    simpa [prefixWord, tailWord_378801, baseEnd_378801] using wordTrace_append hprefix tailTrace_378801
  have hstable : (prefixWord ++ tailWord_378801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378801).length < 2 ^ (prefixWord ++ tailWord_378801).sum := by decide
  have hdescent : baseEnd_378801 < baseStart_378801 := by decide
  rcases family_descends (prefixWord ++ tailWord_378801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378840 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_378840 : Nat := 118140960795 + 378840 * 2 ^ 59
def prefixEnd_378840 : Nat := 4983230072969 + 3 ^ 40 * 378840 * 2
def baseEnd_378840 : Nat := 86456449399734675759001

theorem tailTrace_378840 : CollatzResearch.WordTrace tailWord_378840 prefixEnd_378840 86456449399734675759001 := by
  unfold tailWord_378840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908714973767427783010987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9211619965023237044014649 6908714973767427783010987)
  ·
    refine ⟨10363072460651141674516481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908714973767427783010987 10363072460651141674516481)
    ·
      refine ⟨7772304345488356255887361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10363072460651141674516481 7772304345488356255887361)
      ·
        refine ⟨5829228259116267191915521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7772304345488356255887361 5829228259116267191915521)
        ·
          refine ⟨4371921194337200393936641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5829228259116267191915521 4371921194337200393936641)
          ·
            refine ⟨3278940895752900295452481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4371921194337200393936641 3278940895752900295452481)
            ·
              refine ⟨2459205671814675221589361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278940895752900295452481 2459205671814675221589361)
              ·
                refine ⟨1844404253861006416192021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459205671814675221589361 1844404253861006416192021)
                ·
                  refine ⟨86456449399734675759001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1844404253861006416192021 86456449399734675759001)
                  ·
                    rfl

theorem cell21_378840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_378840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_378840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_378840 prefixEnd_378840 := by exact prefixLift 378840
  have htrace : WordTrace (prefixWord ++ tailWord_378840) baseStart_378840 baseEnd_378840 := by
    simpa [prefixWord, tailWord_378840, baseEnd_378840] using wordTrace_append hprefix tailTrace_378840
  have hstable : (prefixWord ++ tailWord_378840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378840).length < 2 ^ (prefixWord ++ tailWord_378840).sum := by decide
  have hdescent : baseEnd_378840 < baseStart_378840 := by decide
  rcases family_descends (prefixWord ++ tailWord_378840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379057 : List Nat := [1, 2, 2, 5, 2, 2, 2, 5]
def baseStart_379057 : Nat := 118140960795 + 379057 * 2 ^ 59
def prefixEnd_379057 : Nat := 4983230072969 + 3 ^ 40 * 379057 * 2
def baseEnd_379057 : Nat := 28835323918730173547297

theorem tailTrace_379057 : CollatzResearch.WordTrace tailWord_379057 prefixEnd_379057 28835323918730173547297 := by
  unfold tailWord_379057
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825344587748701626671425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9216896391832467751114283 13825344587748701626671425)
  ·
    refine ⟨10369008440811526220003569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13825344587748701626671425 10369008440811526220003569)
    ·
      refine ⟨7776756330608644665002677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10369008440811526220003569 7776756330608644665002677)
      ·
        refine ⟨729070905994560437344001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7776756330608644665002677 729070905994560437344001)
        ·
          refine ⟨546803179495920328008001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729070905994560437344001 546803179495920328008001)
          ·
            refine ⟨410102384621940246006001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546803179495920328008001 410102384621940246006001)
            ·
              refine ⟨307576788466455184504501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410102384621940246006001 307576788466455184504501)
              ·
                refine ⟨28835323918730173547297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307576788466455184504501 28835323918730173547297)
                ·
                  rfl

theorem cell21_379057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 5].length) (baseStart_379057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379057 prefixEnd_379057 := by exact prefixLift 379057
  have htrace : WordTrace (prefixWord ++ tailWord_379057) baseStart_379057 baseEnd_379057 := by
    simpa [prefixWord, tailWord_379057, baseEnd_379057] using wordTrace_append hprefix tailTrace_379057
  have hstable : (prefixWord ++ tailWord_379057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379057).length < 2 ^ (prefixWord ++ tailWord_379057).sum := by decide
  have hdescent : baseEnd_379057 < baseStart_379057 := by decide
  rcases family_descends (prefixWord ++ tailWord_379057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379181 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 3]
def baseStart_379181 : Nat := 118140960795 + 379181 * 2 ^ 59
def prefixEnd_379181 : Nat := 4983230072969 + 3 ^ 40 * 379181 * 2
def baseEnd_379181 : Nat := 86534270245593860574971

theorem tailTrace_379181 : CollatzResearch.WordTrace tailWord_379181 prefixEnd_379181 86534270245593860574971 := by
  unfold tailWord_379181
  simp only [CollatzResearch.WordTrace]
  refine ⟨13829867239299470804185397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9219911492866313869456931 13829867239299470804185397)
  ·
    refine ⟨1296550053684325387892381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13829867239299470804185397 1296550053684325387892381)
    ·
      refine ⟨486206270131622020459643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1296550053684325387892381 486206270131622020459643)
      ·
        refine ⟨729309405197433030689465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486206270131622020459643 729309405197433030689465)
        ·
          refine ⟨546982053898074773017099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729309405197433030689465 546982053898074773017099)
          ·
            refine ⟨820473080847112159525649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546982053898074773017099 820473080847112159525649)
            ·
              refine ⟨615354810635334119644237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820473080847112159525649 615354810635334119644237)
              ·
                refine ⟨230758053988250294866589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615354810635334119644237 230758053988250294866589)
                ·
                  refine ⟨86534270245593860574971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230758053988250294866589 86534270245593860574971)
                  ·
                    rfl

theorem cell21_379181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_379181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379181 prefixEnd_379181 := by exact prefixLift 379181
  have htrace : WordTrace (prefixWord ++ tailWord_379181) baseStart_379181 baseEnd_379181 := by
    simpa [prefixWord, tailWord_379181, baseEnd_379181] using wordTrace_append hprefix tailTrace_379181
  have hstable : (prefixWord ++ tailWord_379181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379181).length < 2 ^ (prefixWord ++ tailWord_379181).sum := by decide
  have hdescent : baseEnd_379181 < baseStart_379181 := by decide
  rcases family_descends (prefixWord ++ tailWord_379181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379189 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_379189 : Nat := 118140960795 + 379189 * 2 ^ 59
def prefixEnd_379189 : Nat := 4983230072969 + 3 ^ 40 * 379189 * 2
def baseEnd_379189 : Nat := 86536095954587624441621

theorem tailTrace_379189 : CollatzResearch.WordTrace tailWord_379189 prefixEnd_379189 86536095954587624441621 := by
  unfold tailWord_379189
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830159023270488170476621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9220106015513658780317747 13830159023270488170476621)
  ·
    refine ⟨5186309633726433063928733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13830159023270488170476621 5186309633726433063928733)
    ·
      refine ⟨1944866112647412398973275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5186309633726433063928733 1944866112647412398973275)
      ·
        refine ⟨2917299168971118598459913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944866112647412398973275 2917299168971118598459913)
        ·
          refine ⟨2187974376728338948844935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917299168971118598459913 2187974376728338948844935)
          ·
            refine ⟨3281961565092508423267403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187974376728338948844935 3281961565092508423267403)
            ·
              refine ⟨4922942347638762634901105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281961565092508423267403 4922942347638762634901105)
              ·
                refine ⟨3692206760729071976175829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922942347638762634901105 3692206760729071976175829)
                ·
                  refine ⟨86536095954587624441621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3692206760729071976175829 86536095954587624441621)
                  ·
                    rfl

theorem cell21_379189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_379189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379189 prefixEnd_379189 := by exact prefixLift 379189
  have htrace : WordTrace (prefixWord ++ tailWord_379189) baseStart_379189 baseEnd_379189 := by
    simpa [prefixWord, tailWord_379189, baseEnd_379189] using wordTrace_append hprefix tailTrace_379189
  have hstable : (prefixWord ++ tailWord_379189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379189).length < 2 ^ (prefixWord ++ tailWord_379189).sum := by decide
  have hdescent : baseEnd_379189 < baseStart_379189 := by decide
  rcases family_descends (prefixWord ++ tailWord_379189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379240 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_379240 : Nat := 118140960795 + 379240 * 2 ^ 59
def prefixEnd_379240 : Nat := 4983230072969 + 3 ^ 40 * 379240 * 2
def baseEnd_379240 : Nat := 86547734849422869091517

theorem tailTrace_379240 : CollatzResearch.WordTrace tailWord_379240 prefixEnd_379240 86547734849422869091517 := by
  unfold tailWord_379240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916009573042861940291587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9221346097390482587055449 6916009573042861940291587)
  ·
    refine ⟨10374014359564292910437381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6916009573042861940291587 10374014359564292910437381)
    ·
      refine ⟨1945127692418304920707009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10374014359564292910437381 1945127692418304920707009)
      ·
        refine ⟨1458845769313728690530257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1945127692418304920707009 1458845769313728690530257)
        ·
          refine ⟨1094134326985296517897693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458845769313728690530257 1094134326985296517897693)
          ·
            refine ⟨410300372619486194211635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1094134326985296517897693 410300372619486194211635)
            ·
              refine ⟨615450558929229291317453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410300372619486194211635 615450558929229291317453)
              ·
                refine ⟨230793959598460984244045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615450558929229291317453 230793959598460984244045)
                ·
                  refine ⟨86547734849422869091517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230793959598460984244045 86547734849422869091517)
                  ·
                    rfl

theorem cell21_379240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_379240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379240 prefixEnd_379240 := by exact prefixLift 379240
  have htrace : WordTrace (prefixWord ++ tailWord_379240) baseStart_379240 baseEnd_379240 := by
    simpa [prefixWord, tailWord_379240, baseEnd_379240] using wordTrace_append hprefix tailTrace_379240
  have hstable : (prefixWord ++ tailWord_379240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379240).length < 2 ^ (prefixWord ++ tailWord_379240).sum := by decide
  have hdescent : baseEnd_379240 < baseStart_379240 := by decide
  rcases family_descends (prefixWord ++ tailWord_379240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379313 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_379313 : Nat := 118140960795 + 379313 * 2 ^ 59
def prefixEnd_379313 : Nat := 4983230072969 + 3 ^ 40 * 379313 * 2
def baseEnd_379313 : Nat := 86564394443990964374701

theorem tailTrace_379313 : CollatzResearch.WordTrace tailWord_379313 prefixEnd_379313 86564394443990964374701 := by
  unfold tailWord_379313
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834681674821257347990593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9223121116547504898660395 13834681674821257347990593)
  ·
    refine ⟨10376011256115943010992945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13834681674821257347990593 10376011256115943010992945)
    ·
      refine ⟨7782008442086957258244709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10376011256115943010992945 7782008442086957258244709)
      ·
        refine ⟨1459126582891304485920883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7782008442086957258244709 1459126582891304485920883)
        ·
          refine ⟨2188689874336956728881325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459126582891304485920883 2188689874336956728881325)
          ·
            refine ⟨820758702876358773330497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2188689874336956728881325 820758702876358773330497)
            ·
              refine ⟨615569027157269079997873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820758702876358773330497 615569027157269079997873)
              ·
                refine ⟨461676770367951809998405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615569027157269079997873 461676770367951809998405)
                ·
                  refine ⟨86564394443990964374701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461676770367951809998405 86564394443990964374701)
                  ·
                    rfl

theorem cell21_379313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_379313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379313 prefixEnd_379313 := by exact prefixLift 379313
  have htrace : WordTrace (prefixWord ++ tailWord_379313) baseStart_379313 baseEnd_379313 := by
    simpa [prefixWord, tailWord_379313, baseEnd_379313] using wordTrace_append hprefix tailTrace_379313
  have hstable : (prefixWord ++ tailWord_379313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379313).length < 2 ^ (prefixWord ++ tailWord_379313).sum := by decide
  have hdescent : baseEnd_379313 < baseStart_379313 := by decide
  rcases family_descends (prefixWord ++ tailWord_379313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379389 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 4]
def baseStart_379389 : Nat := 118140960795 + 379389 * 2 ^ 59
def prefixEnd_379389 : Nat := 4983230072969 + 3 ^ 40 * 379389 * 2
def baseEnd_379389 : Nat := 86581738679431721107879

theorem tailTrace_379389 : CollatzResearch.WordTrace tailWord_379389 prefixEnd_379389 86581738679431721107879 := by
  unfold tailWord_379389
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837453622545922327757221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9224969081697281551838147 13837453622545922327757221)
  ·
    refine ⟨2594522554227360436454479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13837453622545922327757221 2594522554227360436454479)
    ·
      refine ⟨3891783831341040654681719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594522554227360436454479 3891783831341040654681719)
      ·
        refine ⟨5837675747011560982022579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891783831341040654681719 5837675747011560982022579)
        ·
          refine ⟨8756513620517341473033869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5837675747011560982022579 8756513620517341473033869)
          ·
            refine ⟨3283692607694003052387701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8756513620517341473033869 3283692607694003052387701)
            ·
              refine ⟨307846181971312786161347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3283692607694003052387701 307846181971312786161347)
              ·
                refine ⟨461769272956969179242021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307846181971312786161347 461769272956969179242021)
                ·
                  refine ⟨86581738679431721107879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461769272956969179242021 86581738679431721107879)
                  ·
                    rfl

theorem cell21_379389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_379389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379389 prefixEnd_379389 := by exact prefixLift 379389
  have htrace : WordTrace (prefixWord ++ tailWord_379389) baseStart_379389 baseEnd_379389 := by
    simpa [prefixWord, tailWord_379389, baseEnd_379389] using wordTrace_append hprefix tailTrace_379389
  have hstable : (prefixWord ++ tailWord_379389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379389).length < 2 ^ (prefixWord ++ tailWord_379389).sum := by decide
  have hdescent : baseEnd_379389 < baseStart_379389 := by decide
  rcases family_descends (prefixWord ++ tailWord_379389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379403 : List Nat := [1, 1, 1, 1, 7, 1, 4, 5]
def baseStart_379403 : Nat := 118140960795 + 379403 * 2 ^ 59
def prefixEnd_379403 : Nat := 4983230072969 + 3 ^ 40 * 379403 * 2
def baseEnd_379403 : Nat := 28861644556723602624839

theorem tailTrace_379403 : CollatzResearch.WordTrace tailWord_379403 prefixEnd_379403 28861644556723602624839 := by
  unfold tailWord_379403
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837964244495202718766863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9225309496330135145844575 13837964244495202718766863)
  ·
    refine ⟨20756946366742804078150295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13837964244495202718766863 20756946366742804078150295)
    ·
      refine ⟨31135419550114206117225443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20756946366742804078150295 31135419550114206117225443)
      ·
        refine ⟨46703129325171309175838165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31135419550114206117225443 46703129325171309175838165)
        ·
          refine ⟨1094604593558702558808707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 46703129325171309175838165 1094604593558702558808707)
          ·
            refine ⟨1641906890338053838213061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094604593558702558808707 1641906890338053838213061)
            ·
              refine ⟨307857541938385094664949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1641906890338053838213061 307857541938385094664949)
              ·
                refine ⟨28861644556723602624839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307857541938385094664949 28861644556723602624839)
                ·
                  rfl

theorem cell21_379403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 5].length) (baseStart_379403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379403 prefixEnd_379403 := by exact prefixLift 379403
  have htrace : WordTrace (prefixWord ++ tailWord_379403) baseStart_379403 baseEnd_379403 := by
    simpa [prefixWord, tailWord_379403, baseEnd_379403] using wordTrace_append hprefix tailTrace_379403
  have hstable : (prefixWord ++ tailWord_379403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379403).length < 2 ^ (prefixWord ++ tailWord_379403).sum := by decide
  have hdescent : baseEnd_379403 < baseStart_379403 := by decide
  rcases family_descends (prefixWord ++ tailWord_379403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379434 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_379434 : Nat := 118140960795 + 379434 * 2 ^ 59
def prefixEnd_379434 : Nat := 4983230072969 + 3 ^ 40 * 379434 * 2
def baseEnd_379434 : Nat := 86592008292521642857787

theorem tailTrace_379434 : CollatzResearch.WordTrace tailWord_379434 prefixEnd_379434 86592008292521642857787 := by
  unfold tailWord_379434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459773726845723753286339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9226063271588596675430237 3459773726845723753286339)
  ·
    refine ⟨5189660590268585629929509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459773726845723753286339 5189660590268585629929509)
    ·
      refine ⟨973061360675359805611783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5189660590268585629929509 973061360675359805611783)
      ·
        refine ⟨1459592041013039708417675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973061360675359805611783 1459592041013039708417675)
        ·
          refine ⟨2189388061519559562626513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459592041013039708417675 2189388061519559562626513)
          ·
            refine ⟨1642041046139669671969885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2189388061519559562626513 1642041046139669671969885)
            ·
              refine ⟨615765392302376126988707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1642041046139669671969885 615765392302376126988707)
              ·
                refine ⟨923648088453564190483061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615765392302376126988707 923648088453564190483061)
                ·
                  refine ⟨86592008292521642857787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923648088453564190483061 86592008292521642857787)
                  ·
                    rfl

theorem cell21_379434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_379434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379434 prefixEnd_379434 := by exact prefixLift 379434
  have htrace : WordTrace (prefixWord ++ tailWord_379434) baseStart_379434 baseEnd_379434 := by
    simpa [prefixWord, tailWord_379434, baseEnd_379434] using wordTrace_append hprefix tailTrace_379434
  have hstable : (prefixWord ++ tailWord_379434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379434).length < 2 ^ (prefixWord ++ tailWord_379434).sum := by decide
  have hdescent : baseEnd_379434 < baseStart_379434 := by decide
  rcases family_descends (prefixWord ++ tailWord_379434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379448 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_379448 : Nat := 118140960795 + 379448 * 2 ^ 59
def prefixEnd_379448 : Nat := 4983230072969 + 3 ^ 40 * 379448 * 2
def baseEnd_379448 : Nat := 86595203283260729624425

theorem tailTrace_379448 : CollatzResearch.WordTrace tailWord_379448 prefixEnd_379448 86595203283260729624425 := by
  unfold tailWord_379448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919802764666087702077499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9226403686221450269436665 6919802764666087702077499)
  ·
    refine ⟨10379704146999131553116249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919802764666087702077499 10379704146999131553116249)
    ·
      refine ⟨7784778110249348664837187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10379704146999131553116249 7784778110249348664837187)
      ·
        refine ⟨11677167165374022997255781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784778110249348664837187 11677167165374022997255781)
        ·
          refine ⟨2189468843507629311985459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11677167165374022997255781 2189468843507629311985459)
          ·
            refine ⟨3284203265261443967978189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189468843507629311985459 3284203265261443967978189)
            ·
              refine ⟨1231576224473041487991821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3284203265261443967978189 1231576224473041487991821)
              ·
                refine ⟨461841084177390557996933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231576224473041487991821 461841084177390557996933)
                ·
                  refine ⟨86595203283260729624425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461841084177390557996933 86595203283260729624425)
                  ·
                    rfl

theorem cell21_379448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_379448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379448 prefixEnd_379448 := by exact prefixLift 379448
  have htrace : WordTrace (prefixWord ++ tailWord_379448) baseStart_379448 baseEnd_379448 := by
    simpa [prefixWord, tailWord_379448, baseEnd_379448] using wordTrace_append hprefix tailTrace_379448
  have hstable : (prefixWord ++ tailWord_379448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379448).length < 2 ^ (prefixWord ++ tailWord_379448).sum := by decide
  have hdescent : baseEnd_379448 < baseStart_379448 := by decide
  rcases family_descends (prefixWord ++ tailWord_379448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379496 : List Nat := [2, 1, 4, 3, 2, 2, 1, 6]
def baseStart_379496 : Nat := 118140960795 + 379496 * 2 ^ 59
def prefixEnd_379496 : Nat := 4983230072969 + 3 ^ 40 * 379496 * 2
def baseEnd_379496 : Nat := 28868719179074437608109

theorem tailTrace_379496 : CollatzResearch.WordTrace tailWord_379496 prefixEnd_379496 28868719179074437608109 := by
  unfold tailWord_379496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920678116579139800951171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9227570822105519734601561 6920678116579139800951171)
  ·
    refine ⟨10381017174868709701426757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6920678116579139800951171 10381017174868709701426757)
    ·
      refine ⟨1946440720287883069017517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10381017174868709701426757 1946440720287883069017517)
      ·
        refine ⟨729915270107956150881569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1946440720287883069017517 729915270107956150881569)
        ·
          refine ⟨547436452580967113161177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729915270107956150881569 547436452580967113161177)
          ·
            refine ⟨410577339435725334870883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547436452580967113161177 410577339435725334870883)
            ·
              refine ⟨615866009153588002306325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410577339435725334870883 615866009153588002306325)
              ·
                refine ⟨28868719179074437608109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 615866009153588002306325 28868719179074437608109)
                ·
                  rfl

theorem cell21_379496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_379496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379496 prefixEnd_379496 := by exact prefixLift 379496
  have htrace : WordTrace (prefixWord ++ tailWord_379496) baseStart_379496 baseEnd_379496 := by
    simpa [prefixWord, tailWord_379496, baseEnd_379496] using wordTrace_append hprefix tailTrace_379496
  have hstable : (prefixWord ++ tailWord_379496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379496).length < 2 ^ (prefixWord ++ tailWord_379496).sum := by decide
  have hdescent : baseEnd_379496 < baseStart_379496 := by decide
  rcases family_descends (prefixWord ++ tailWord_379496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379583 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_379583 : Nat := 118140960795 + 379583 * 2 ^ 59
def prefixEnd_379583 : Nat := 4983230072969 + 3 ^ 40 * 379583 * 2
def baseEnd_379583 : Nat := 86626012122530494874149

theorem tailTrace_379583 : CollatzResearch.WordTrace tailWord_379583 prefixEnd_379583 86626012122530494874149 := by
  unfold tailWord_379583
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844529383843093460319403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9229686255895395640212935 13844529383843093460319403)
  ·
    refine ⟨20766794075764640190479105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13844529383843093460319403 20766794075764640190479105)
    ·
      refine ⟨15575095556823480142859329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20766794075764640190479105 15575095556823480142859329)
      ·
        refine ⟨11681321667617610107144497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15575095556823480142859329 11681321667617610107144497)
        ·
          refine ⟨8760991250713207580358373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11681321667617610107144497 8760991250713207580358373)
          ·
            refine ⟨1642685859508726421317195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8760991250713207580358373 1642685859508726421317195)
            ·
              refine ⟨2464028789263089631975793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642685859508726421317195 2464028789263089631975793)
              ·
                refine ⟨1848021591947317223981845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464028789263089631975793 1848021591947317223981845)
                ·
                  refine ⟨86626012122530494874149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1848021591947317223981845 86626012122530494874149)
                  ·
                    rfl

theorem cell21_379583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_379583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379583 prefixEnd_379583 := by exact prefixLift 379583
  have htrace : WordTrace (prefixWord ++ tailWord_379583) baseStart_379583 baseEnd_379583 := by
    simpa [prefixWord, tailWord_379583, baseEnd_379583] using wordTrace_append hprefix tailTrace_379583
  have hstable : (prefixWord ++ tailWord_379583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379583).length < 2 ^ (prefixWord ++ tailWord_379583).sum := by decide
  have hdescent : baseEnd_379583 < baseStart_379583 := by decide
  rcases family_descends (prefixWord ++ tailWord_379583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379617 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 4]
def baseStart_379617 : Nat := 118140960795 + 379617 * 2 ^ 59
def prefixEnd_379617 : Nat := 4983230072969 + 3 ^ 40 * 379617 * 2
def baseEnd_379617 : Nat := 86633771385753991307413

theorem tailTrace_379617 : CollatzResearch.WordTrace tailWord_379617 prefixEnd_379617 86633771385753991307413 := by
  unfold tailWord_379617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845769465719917267057105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9230512977146611511371403 13845769465719917267057105)
  ·
    refine ⟨10384327099289937950292829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13845769465719917267057105 10384327099289937950292829)
    ·
      refine ⟨3894122662233726731359811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10384327099289937950292829 3894122662233726731359811)
      ·
        refine ⟨5841183993350590097039717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894122662233726731359811 5841183993350590097039717)
        ·
          refine ⟨1095221998753235643194947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5841183993350590097039717 1095221998753235643194947)
          ·
            refine ⟨1642832998129853464792421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095221998753235643194947 1642832998129853464792421)
            ·
              refine ⟨308031187149347524648579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1642832998129853464792421 308031187149347524648579)
              ·
                refine ⟨462046780724021286972869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308031187149347524648579 462046780724021286972869)
                ·
                  refine ⟨86633771385753991307413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462046780724021286972869 86633771385753991307413)
                  ·
                    rfl

theorem cell21_379617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_379617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379617 prefixEnd_379617 := by exact prefixLift 379617
  have htrace : WordTrace (prefixWord ++ tailWord_379617) baseStart_379617 baseEnd_379617 := by
    simpa [prefixWord, tailWord_379617, baseEnd_379617] using wordTrace_append hprefix tailTrace_379617
  have hstable : (prefixWord ++ tailWord_379617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379617).length < 2 ^ (prefixWord ++ tailWord_379617).sum := by decide
  have hdescent : baseEnd_379617 < baseStart_379617 := by decide
  rcases family_descends (prefixWord ++ tailWord_379617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379628 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_379628 : Nat := 118140960795 + 379628 * 2 ^ 59
def prefixEnd_379628 : Nat := 4983230072969 + 3 ^ 40 * 379628 * 2
def baseEnd_379628 : Nat := 86636281735620416624057

theorem tailTrace_379628 : CollatzResearch.WordTrace tailWord_379628 prefixEnd_379628 86636281735620416624057 := by
  unfold tailWord_379628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923085334340033072853769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9230780445786710763805025 6923085334340033072853769)
  ·
    refine ⟨5192314000755024804640327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6923085334340033072853769 5192314000755024804640327)
    ·
      refine ⟨7788471001132537206960491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192314000755024804640327 7788471001132537206960491)
      ·
        refine ⟨11682706501698805810440737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788471001132537206960491 11682706501698805810440737)
        ·
          refine ⟨8762029876274104357830553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682706501698805810440737 8762029876274104357830553)
          ·
            refine ⟨6571522407205578268372915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8762029876274104357830553 6571522407205578268372915)
            ·
              refine ⟨9857283610808367402559373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571522407205578268372915 9857283610808367402559373)
              ·
                refine ⟨3696481354053137775959765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9857283610808367402559373 3696481354053137775959765)
                ·
                  refine ⟨86636281735620416624057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3696481354053137775959765 86636281735620416624057)
                  ·
                    rfl

theorem cell21_379628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_379628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379628 prefixEnd_379628 := by exact prefixLift 379628
  have htrace : WordTrace (prefixWord ++ tailWord_379628) baseStart_379628 baseEnd_379628 := by
    simpa [prefixWord, tailWord_379628, baseEnd_379628] using wordTrace_append hprefix tailTrace_379628
  have hstable : (prefixWord ++ tailWord_379628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379628).length < 2 ^ (prefixWord ++ tailWord_379628).sum := by decide
  have hdescent : baseEnd_379628 < baseStart_379628 := by decide
  rcases family_descends (prefixWord ++ tailWord_379628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379673 : List Nat := [1, 2, 1, 2, 1, 1, 1, 12]
def baseStart_379673 : Nat := 118140960795 + 379673 * 2 ^ 59
def prefixEnd_379673 : Nat := 4983230072969 + 3 ^ 40 * 379673 * 2
def baseEnd_379673 : Nat := 28882183782903446124655

theorem tailTrace_379673 : CollatzResearch.WordTrace tailWord_379673 prefixEnd_379673 28882183782903446124655 := by
  unfold tailWord_379673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13847811953517038831095673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9231874635678025887397115 13847811953517038831095673)
  ·
    refine ⟨10385858965137779123321755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13847811953517038831095673 10385858965137779123321755)
    ·
      refine ⟨15578788447706668684982633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10385858965137779123321755 15578788447706668684982633)
      ·
        refine ⟨11684091335780001513736975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15578788447706668684982633 11684091335780001513736975)
        ·
          refine ⟨17526137003670002270605463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11684091335780001513736975 17526137003670002270605463)
          ·
            refine ⟨26289205505505003405908195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17526137003670002270605463 26289205505505003405908195)
            ·
              refine ⟨39433808258257505108862293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26289205505505003405908195 39433808258257505108862293)
              ·
                refine ⟨28882183782903446124655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 39433808258257505108862293 28882183782903446124655)
                ·
                  rfl

theorem cell21_379673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_379673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379673 prefixEnd_379673 := by exact prefixLift 379673
  have htrace : WordTrace (prefixWord ++ tailWord_379673) baseStart_379673 baseEnd_379673 := by
    simpa [prefixWord, tailWord_379673, baseEnd_379673] using wordTrace_append hprefix tailTrace_379673
  have hstable : (prefixWord ++ tailWord_379673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379673).length < 2 ^ (prefixWord ++ tailWord_379673).sum := by decide
  have hdescent : baseEnd_379673 < baseStart_379673 := by decide
  rcases family_descends (prefixWord ++ tailWord_379673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379676 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_379676 : Nat := 118140960795 + 379676 * 2 ^ 59
def prefixEnd_379676 : Nat := 4983230072969 + 3 ^ 40 * 379676 * 2
def baseEnd_379676 : Nat := 86647235989582999823959

theorem tailTrace_379676 : CollatzResearch.WordTrace tailWord_379676 prefixEnd_379676 86647235989582999823959 := by
  unfold tailWord_379676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923960686253085171727441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9231947581670780228969921 6923960686253085171727441)
  ·
    refine ⟨5192970514689813878795581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6923960686253085171727441 5192970514689813878795581)
    ·
      refine ⟨1947363943008680204548343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5192970514689813878795581 1947363943008680204548343)
      ·
        refine ⟨2921045914513020306822515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947363943008680204548343 2921045914513020306822515)
        ·
          refine ⟨4381568871769530460233773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2921045914513020306822515 4381568871769530460233773)
          ·
            refine ⟨1643088326913573922587665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4381568871769530460233773 1643088326913573922587665)
            ·
              refine ⟨1232316245185180441940749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643088326913573922587665 1232316245185180441940749)
              ·
                refine ⟨462118591944442665727781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1232316245185180441940749 462118591944442665727781)
                ·
                  refine ⟨86647235989582999823959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462118591944442665727781 86647235989582999823959)
                  ·
                    rfl

theorem cell21_379676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_379676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379676 prefixEnd_379676 := by exact prefixLift 379676
  have htrace : WordTrace (prefixWord ++ tailWord_379676) baseStart_379676 baseEnd_379676 := by
    simpa [prefixWord, tailWord_379676, baseEnd_379676] using wordTrace_append hprefix tailTrace_379676
  have hstable : (prefixWord ++ tailWord_379676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379676).length < 2 ^ (prefixWord ++ tailWord_379676).sum := by decide
  have hdescent : baseEnd_379676 < baseStart_379676 := by decide
  rcases family_descends (prefixWord ++ tailWord_379676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379704 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_379704 : Nat := 118140960795 + 379704 * 2 ^ 59
def prefixEnd_379704 : Nat := 4983230072969 + 3 ^ 40 * 379704 * 2
def baseEnd_379704 : Nat := 86653625971061173357235

theorem tailTrace_379704 : CollatzResearch.WordTrace tailWord_379704 prefixEnd_379704 86653625971061173357235 := by
  unfold tailWord_379704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6924471308202365562737083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9232628410936487416982777 6924471308202365562737083)
  ·
    refine ⟨10386706962303548344105625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6924471308202365562737083 10386706962303548344105625)
    ·
      refine ⟨7790030221727661258079219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10386706962303548344105625 7790030221727661258079219)
      ·
        refine ⟨11685045332591491887118829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7790030221727661258079219 11685045332591491887118829)
        ·
          refine ⟨4381891999721809457669561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11685045332591491887118829 4381891999721809457669561)
          ·
            refine ⟨3286418999791357093252171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4381891999721809457669561 3286418999791357093252171)
            ·
              refine ⟨4929628499687035639878257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286418999791357093252171 4929628499687035639878257)
              ·
                refine ⟨3697221374765276729908693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4929628499687035639878257 3697221374765276729908693)
                ·
                  refine ⟨86653625971061173357235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3697221374765276729908693 86653625971061173357235)
                  ·
                    rfl

theorem cell21_379704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_379704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379704 prefixEnd_379704 := by exact prefixLift 379704
  have htrace : WordTrace (prefixWord ++ tailWord_379704) baseStart_379704 baseEnd_379704 := by
    simpa [prefixWord, tailWord_379704, baseEnd_379704] using wordTrace_append hprefix tailTrace_379704
  have hstable : (prefixWord ++ tailWord_379704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379704).length < 2 ^ (prefixWord ++ tailWord_379704).sum := by decide
  have hdescent : baseEnd_379704 < baseStart_379704 := by decide
  rcases family_descends (prefixWord ++ tailWord_379704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379710 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_379710 : Nat := 118140960795 + 379710 * 2 ^ 59
def prefixEnd_379710 : Nat := 4983230072969 + 3 ^ 40 * 379710 * 2
def baseEnd_379710 : Nat := 86654995252806496257223

theorem tailTrace_379710 : CollatzResearch.WordTrace tailWord_379710 prefixEnd_379710 86654995252806496257223 := by
  unfold tailWord_379710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731145181797874268774073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9232774302921996100128389 1731145181797874268774073)
  ·
    refine ⟨1298358886348405701580555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1731145181797874268774073 1298358886348405701580555)
    ·
      refine ⟨1947538329522608552370833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298358886348405701580555 1947538329522608552370833)
      ·
        refine ⟨1460653747141956414278125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1947538329522608552370833 1460653747141956414278125)
        ·
          refine ⟨547745155178233655354297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1460653747141956414278125 547745155178233655354297)
          ·
            refine ⟨410808866383675241515723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547745155178233655354297 410808866383675241515723)
            ·
              refine ⟨616213299575512862273585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410808866383675241515723 616213299575512862273585)
              ·
                refine ⟨462159974681634646705189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616213299575512862273585 462159974681634646705189)
                ·
                  refine ⟨86654995252806496257223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462159974681634646705189 86654995252806496257223)
                  ·
                    rfl

theorem cell21_379710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_379710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379710 prefixEnd_379710 := by exact prefixLift 379710
  have htrace : WordTrace (prefixWord ++ tailWord_379710) baseStart_379710 baseEnd_379710 := by
    simpa [prefixWord, tailWord_379710, baseEnd_379710] using wordTrace_append hprefix tailTrace_379710
  have hstable : (prefixWord ++ tailWord_379710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379710).length < 2 ^ (prefixWord ++ tailWord_379710).sum := by decide
  have hdescent : baseEnd_379710 < baseStart_379710 := by decide
  rcases family_descends (prefixWord ++ tailWord_379710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379721 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_379721 : Nat := 118140960795 + 379721 * 2 ^ 59
def prefixEnd_379721 : Nat := 4983230072969 + 3 ^ 40 * 379721 * 2
def baseEnd_379721 : Nat := 86657505602672921573867

theorem tailTrace_379721 : CollatzResearch.WordTrace tailWord_379721 prefixEnd_379721 86657505602672921573867 := by
  unfold tailWord_379721
  simp only [CollatzResearch.WordTrace]
  refine ⟨13849562657343143028843017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9233041771562095352562011 13849562657343143028843017)
  ·
    refine ⟨10387171993007357271632263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13849562657343143028843017 10387171993007357271632263)
    ·
      refine ⟨15580757989511035907448395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10387171993007357271632263 15580757989511035907448395)
      ·
        refine ⟨23371136984266553861172593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15580757989511035907448395 23371136984266553861172593)
        ·
          refine ⟨17528352738199915395879445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23371136984266553861172593 17528352738199915395879445)
          ·
            refine ⟨821641534603121034181849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17528352738199915395879445 821641534603121034181849)
            ·
              refine ⟨616231150952340775636387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821641534603121034181849 616231150952340775636387)
              ·
                refine ⟨924346726428511163454581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616231150952340775636387 924346726428511163454581)
                ·
                  refine ⟨86657505602672921573867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 924346726428511163454581 86657505602672921573867)
                  ·
                    rfl

theorem cell21_379721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_379721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379721 prefixEnd_379721 := by exact prefixLift 379721
  have htrace : WordTrace (prefixWord ++ tailWord_379721) baseStart_379721 baseEnd_379721 := by
    simpa [prefixWord, tailWord_379721, baseEnd_379721] using wordTrace_append hprefix tailTrace_379721
  have hstable : (prefixWord ++ tailWord_379721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379721).length < 2 ^ (prefixWord ++ tailWord_379721).sum := by decide
  have hdescent : baseEnd_379721 < baseStart_379721 := by decide
  rcases family_descends (prefixWord ++ tailWord_379721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379786 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_379786 : Nat := 118140960795 + 379786 * 2 ^ 59
def prefixEnd_379786 : Nat := 4983230072969 + 3 ^ 40 * 379786 * 2
def baseEnd_379786 : Nat := 86672339488247252990401

theorem tailTrace_379786 : CollatzResearch.WordTrace tailWord_379786 prefixEnd_379786 86672339488247252990401 := by
  unfold tailWord_379786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462983350526914782489803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9234622268071772753306141 3462983350526914782489803)
  ·
    refine ⟨5194475025790372173734705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3462983350526914782489803 5194475025790372173734705)
    ·
      refine ⟨3895856269342779130301029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5194475025790372173734705 3895856269342779130301029)
      ·
        refine ⟨730473050501771086931443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3895856269342779130301029 730473050501771086931443)
        ·
          refine ⟨1095709575752656630397165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730473050501771086931443 1095709575752656630397165)
          ·
            refine ⟨410891090907246236398937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1095709575752656630397165 410891090907246236398937)
            ·
              refine ⟨308168318180434677299203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410891090907246236398937 308168318180434677299203)
              ·
                refine ⟨462252477270652015948805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308168318180434677299203 462252477270652015948805)
                ·
                  refine ⟨86672339488247252990401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462252477270652015948805 86672339488247252990401)
                  ·
                    rfl

theorem cell21_379786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_379786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379786 prefixEnd_379786 := by exact prefixLift 379786
  have htrace : WordTrace (prefixWord ++ tailWord_379786) baseStart_379786 baseEnd_379786 := by
    simpa [prefixWord, tailWord_379786, baseEnd_379786] using wordTrace_append hprefix tailTrace_379786
  have hstable : (prefixWord ++ tailWord_379786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379786).length < 2 ^ (prefixWord ++ tailWord_379786).sum := by decide
  have hdescent : baseEnd_379786 < baseStart_379786 := by decide
  rcases family_descends (prefixWord ++ tailWord_379786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379825 : List Nat := [1, 2, 2, 4, 12]
def baseStart_379825 : Nat := 118140960795 + 379825 * 2 ^ 59
def prefixEnd_379825 : Nat := 4983230072969 + 3 ^ 40 * 379825 * 2
def baseEnd_379825 : Nat := 1070138763204837677041

theorem tailTrace_379825 : CollatzResearch.WordTrace tailWord_379825 prefixEnd_379825 1070138763204837677041 := by
  unfold tailWord_379825
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853355848966368790628929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9235570565977579193752619 13853355848966368790628929)
  ·
    refine ⟨10390016886724776592971697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13853355848966368790628929 10390016886724776592971697)
    ·
      refine ⟨7792512665043582444728773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10390016886724776592971697 7792512665043582444728773)
      ·
        refine ⟨1461096124695671708386645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7792512665043582444728773 1461096124695671708386645)
        ·
          refine ⟨1070138763204837677041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1461096124695671708386645 1070138763204837677041)
          ·
            rfl

theorem cell21_379825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 12].length) (baseStart_379825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379825 prefixEnd_379825 := by exact prefixLift 379825
  have htrace : WordTrace (prefixWord ++ tailWord_379825) baseStart_379825 baseEnd_379825 := by
    simpa [prefixWord, tailWord_379825, baseEnd_379825] using wordTrace_append hprefix tailTrace_379825
  have hstable : (prefixWord ++ tailWord_379825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379825).length < 2 ^ (prefixWord ++ tailWord_379825).sum := by decide
  have hdescent : baseEnd_379825 < baseStart_379825 := by decide
  rcases family_descends (prefixWord ++ tailWord_379825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379887 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_379887 : Nat := 118140960795 + 379887 * 2 ^ 59
def prefixEnd_379887 : Nat := 4983230072969 + 3 ^ 40 * 379887 * 2
def baseEnd_379887 : Nat := 86695389064293521806861

theorem tailTrace_379887 : CollatzResearch.WordTrace tailWord_379887 prefixEnd_379887 86695389064293521806861 := by
  unfold tailWord_379887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855617174741753379385915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9237078116494502252923943 13855617174741753379385915)
  ·
    refine ⟨20783425762112630069078873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855617174741753379385915 20783425762112630069078873)
    ·
      refine ⟨15587569321584472551809155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20783425762112630069078873 15587569321584472551809155)
      ·
        refine ⟨23381353982376708827713733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15587569321584472551809155 23381353982376708827713733)
        ·
          refine ⟨4384003871695632905196325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23381353982376708827713733 4384003871695632905196325)
          ·
            refine ⟨822000725942931169724311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4384003871695632905196325 822000725942931169724311)
            ·
              refine ⟨1233001088914396754586467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822000725942931169724311 1233001088914396754586467)
              ·
                refine ⟨1849501633371595131879701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233001088914396754586467 1849501633371595131879701)
                ·
                  refine ⟨86695389064293521806861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1849501633371595131879701 86695389064293521806861)
                  ·
                    rfl

theorem cell21_379887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_379887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379887 prefixEnd_379887 := by exact prefixLift 379887
  have htrace : WordTrace (prefixWord ++ tailWord_379887) baseStart_379887 baseEnd_379887 := by
    simpa [prefixWord, tailWord_379887, baseEnd_379887] using wordTrace_append hprefix tailTrace_379887
  have hstable : (prefixWord ++ tailWord_379887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379887).length < 2 ^ (prefixWord ++ tailWord_379887).sum := by decide
  have hdescent : baseEnd_379887 < baseStart_379887 := by decide
  rcases family_descends (prefixWord ++ tailWord_379887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379901 : List Nat := [1, 4, 1, 1, 1, 2, 1, 10]
def baseStart_379901 : Nat := 118140960795 + 379901 * 2 ^ 59
def prefixEnd_379901 : Nat := 4983230072969 + 3 ^ 40 * 379901 * 2
def baseEnd_379901 : Nat := 28899528018344202857833

theorem tailTrace_379901 : CollatzResearch.WordTrace tailWord_379901 prefixEnd_379901 28899528018344202857833 := by
  unfold tailWord_379901
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856127796691033770395557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9237418531127355846930371 13856127796691033770395557)
  ·
    refine ⟨2598023961879568831949167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13856127796691033770395557 2598023961879568831949167)
    ·
      refine ⟨3897035942819353247923751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598023961879568831949167 3897035942819353247923751)
      ·
        refine ⟨5845553914229029871885627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897035942819353247923751 5845553914229029871885627)
        ·
          refine ⟨8768330871343544807828441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845553914229029871885627 8768330871343544807828441)
          ·
            refine ⟨6576248153507658605871331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8768330871343544807828441 6576248153507658605871331)
            ·
              refine ⟨9864372230261487908806997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6576248153507658605871331 9864372230261487908806997)
              ·
                refine ⟨28899528018344202857833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9864372230261487908806997 28899528018344202857833)
                ·
                  rfl

theorem cell21_379901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_379901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379901 prefixEnd_379901 := by exact prefixLift 379901
  have htrace : WordTrace (prefixWord ++ tailWord_379901) baseStart_379901 baseEnd_379901 := by
    simpa [prefixWord, tailWord_379901, baseEnd_379901] using wordTrace_append hprefix tailTrace_379901
  have hstable : (prefixWord ++ tailWord_379901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379901).length < 2 ^ (prefixWord ++ tailWord_379901).sum := by decide
  have hdescent : baseEnd_379901 < baseStart_379901 := by decide
  rcases family_descends (prefixWord ++ tailWord_379901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379918 : List Nat := [4, 1, 1, 2, 2, 3, 1, 7]
def baseStart_379918 : Nat := 118140960795 + 379918 * 2 ^ 59
def prefixEnd_379918 : Nat := 4983230072969 + 3 ^ 40 * 379918 * 2
def baseEnd_379918 : Nat := 28900821228881452263377

theorem tailTrace_379918 : CollatzResearch.WordTrace tailWord_379918 prefixEnd_379918 28900821228881452263377 := by
  unfold tailWord_379918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732093479703680709220551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9237831891752963782509605 1732093479703680709220551)
  ·
    refine ⟨2598140219555521063830827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1732093479703680709220551 2598140219555521063830827)
    ·
      refine ⟨3897210329333281595746241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598140219555521063830827 3897210329333281595746241)
      ·
        refine ⟨2922907746999961196809681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897210329333281595746241 2922907746999961196809681)
        ·
          refine ⟨2192180810249970897607261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922907746999961196809681 2192180810249970897607261)
          ·
            refine ⟨822067803843739086602723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2192180810249970897607261 822067803843739086602723)
            ·
              refine ⟨1233101705765608629904085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822067803843739086602723 1233101705765608629904085)
              ·
                refine ⟨28900821228881452263377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1233101705765608629904085 28900821228881452263377)
                ·
                  rfl

theorem cell21_379918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_379918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_379918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_379918 prefixEnd_379918 := by exact prefixLift 379918
  have htrace : WordTrace (prefixWord ++ tailWord_379918) baseStart_379918 baseEnd_379918 := by
    simpa [prefixWord, tailWord_379918, baseEnd_379918] using wordTrace_append hprefix tailTrace_379918
  have hstable : (prefixWord ++ tailWord_379918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379918).length < 2 ^ (prefixWord ++ tailWord_379918).sum := by decide
  have hdescent : baseEnd_379918 < baseStart_379918 := by decide
  rcases family_descends (prefixWord ++ tailWord_379918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380025 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_380025 : Nat := 118140960795 + 380025 * 2 ^ 59
def prefixEnd_380025 : Nat := 4983230072969 + 3 ^ 40 * 380025 * 2
def baseEnd_380025 : Nat := 86726882544435948506579

theorem tailTrace_380025 : CollatzResearch.WordTrace tailWord_380025 prefixEnd_380025 86726882544435948506579 := by
  unfold tailWord_380025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860650448241802947909529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9240433632161201965273019 13860650448241802947909529)
  ·
    refine ⟨10395487836181352210932147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13860650448241802947909529 10395487836181352210932147)
    ·
      refine ⟨15593231754272028316398221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10395487836181352210932147 15593231754272028316398221)
      ·
        refine ⟨5847461907852010618649333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15593231754272028316398221 5847461907852010618649333)
        ·
          refine ⟨548199553861125995498375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5847461907852010618649333 548199553861125995498375)
          ·
            refine ⟨822299330791688993247563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548199553861125995498375 822299330791688993247563)
            ·
              refine ⟨1233448996187533489871345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822299330791688993247563 1233448996187533489871345)
              ·
                refine ⟨925086747140650117403509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233448996187533489871345 925086747140650117403509)
                ·
                  refine ⟨86726882544435948506579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 925086747140650117403509 86726882544435948506579)
                  ·
                    rfl

theorem cell21_380025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_380025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380025 prefixEnd_380025 := by exact prefixLift 380025
  have htrace : WordTrace (prefixWord ++ tailWord_380025) baseStart_380025 baseEnd_380025 := by
    simpa [prefixWord, tailWord_380025, baseEnd_380025] using wordTrace_append hprefix tailTrace_380025
  have hstable : (prefixWord ++ tailWord_380025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380025).length < 2 ^ (prefixWord ++ tailWord_380025).sum := by decide
  have hdescent : baseEnd_380025 < baseStart_380025 := by decide
  rcases family_descends (prefixWord ++ tailWord_380025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380042 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_380042 : Nat := 118140960795 + 380042 * 2 ^ 59
def prefixEnd_380042 : Nat := 4983230072969 + 3 ^ 40 * 380042 * 2
def baseEnd_380042 : Nat := 86730762176047696723211

theorem tailTrace_380042 : CollatzResearch.WordTrace tailWord_380042 prefixEnd_380042 86730762176047696723211 := by
  unfold tailWord_380042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465317622295053712819595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9240846992786809900852253 3465317622295053712819595)
  ·
    refine ⟨5197976433442580569229393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3465317622295053712819595 5197976433442580569229393)
    ·
      refine ⟨3898482325081935426922045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5197976433442580569229393 3898482325081935426922045)
      ·
        refine ⟨1461930871905725785095767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3898482325081935426922045 1461930871905725785095767)
        ·
          refine ⟨2192896307858588677643651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461930871905725785095767 2192896307858588677643651)
          ·
            refine ⟨3289344461787883016465477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192896307858588677643651 3289344461787883016465477)
            ·
              refine ⟨616752086585228065587277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3289344461787883016465477 616752086585228065587277)
              ·
                refine ⟨231282032469460524595229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616752086585228065587277 231282032469460524595229)
                ·
                  refine ⟨86730762176047696723211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231282032469460524595229 86730762176047696723211)
                  ·
                    rfl

theorem cell21_380042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_380042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380042 prefixEnd_380042 := by exact prefixLift 380042
  have htrace : WordTrace (prefixWord ++ tailWord_380042) baseStart_380042 baseEnd_380042 := by
    simpa [prefixWord, tailWord_380042, baseEnd_380042] using wordTrace_append hprefix tailTrace_380042
  have hstable : (prefixWord ++ tailWord_380042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380042).length < 2 ^ (prefixWord ++ tailWord_380042).sum := by decide
  have hdescent : baseEnd_380042 < baseStart_380042 := by decide
  rcases family_descends (prefixWord ++ tailWord_380042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380056 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_380056 : Nat := 118140960795 + 380056 * 2 ^ 59
def prefixEnd_380056 : Nat := 4983230072969 + 3 ^ 40 * 380056 * 2
def baseEnd_380056 : Nat := 86733957166786783489849

theorem tailTrace_380056 : CollatzResearch.WordTrace tailWord_380056 prefixEnd_380056 86733957166786783489849 := by
  unfold tailWord_380056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930890555564747621144011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9241187407419663494858681 6930890555564747621144011)
  ·
    refine ⟨10396335833347121431716017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6930890555564747621144011 10396335833347121431716017)
    ·
      refine ⟨7797251875010341073787013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10396335833347121431716017 7797251875010341073787013)
      ·
        refine ⟨1461984726564438951335065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7797251875010341073787013 1461984726564438951335065)
        ·
          refine ⟨1096488544923329213501299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461984726564438951335065 1096488544923329213501299)
          ·
            refine ⟨1644732817384993820251949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096488544923329213501299 1644732817384993820251949)
            ·
              refine ⟨616774806519372682594481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1644732817384993820251949 616774806519372682594481)
              ·
                refine ⟨462581104889529511945861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616774806519372682594481 462581104889529511945861)
                ·
                  refine ⟨86733957166786783489849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462581104889529511945861 86733957166786783489849)
                  ·
                    rfl

theorem cell21_380056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_380056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380056 prefixEnd_380056 := by exact prefixLift 380056
  have htrace : WordTrace (prefixWord ++ tailWord_380056) baseStart_380056 baseEnd_380056 := by
    simpa [prefixWord, tailWord_380056, baseEnd_380056] using wordTrace_append hprefix tailTrace_380056
  have hstable : (prefixWord ++ tailWord_380056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380056).length < 2 ^ (prefixWord ++ tailWord_380056).sum := by decide
  have hdescent : baseEnd_380056 < baseStart_380056 := by decide
  rcases family_descends (prefixWord ++ tailWord_380056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380129 : List Nat := [1, 2, 3, 1, 3, 2, 1, 8]
def baseStart_380129 : Nat := 118140960795 + 380129 * 2 ^ 59
def prefixEnd_380129 : Nat := 4983230072969 + 3 ^ 40 * 380129 * 2
def baseEnd_380129 : Nat := 28916872253784959591011

theorem tailTrace_380129 : CollatzResearch.WordTrace tailWord_380129 prefixEnd_380129 28916872253784959591011 := by
  unfold tailWord_380129
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864443639865028709695441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9242962426576685806463627 13864443639865028709695441)
  ·
    refine ⟨10398332729898771532271581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13864443639865028709695441 10398332729898771532271581)
    ·
      refine ⟨3899374773712039324601843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10398332729898771532271581 3899374773712039324601843)
      ·
        refine ⟨5849062160568058986902765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899374773712039324601843 5849062160568058986902765)
        ·
          refine ⟨2193398310213022120088537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5849062160568058986902765 2193398310213022120088537)
          ·
            refine ⟨1645048732659766590066403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193398310213022120088537 1645048732659766590066403)
            ·
              refine ⟨2467573098989649885099605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645048732659766590066403 2467573098989649885099605)
              ·
                refine ⟨28916872253784959591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2467573098989649885099605 28916872253784959591011)
                ·
                  rfl

theorem cell21_380129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_380129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380129 prefixEnd_380129 := by exact prefixLift 380129
  have htrace : WordTrace (prefixWord ++ tailWord_380129) baseStart_380129 baseEnd_380129 := by
    simpa [prefixWord, tailWord_380129, baseEnd_380129] using wordTrace_append hprefix tailTrace_380129
  have hstable : (prefixWord ++ tailWord_380129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380129).length < 2 ^ (prefixWord ++ tailWord_380129).sum := by decide
  have hdescent : baseEnd_380129 < baseStart_380129 := by decide
  rcases family_descends (prefixWord ++ tailWord_380129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380132 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_380132 : Nat := 118140960795 + 380132 * 2 ^ 59
def prefixEnd_380132 : Nat := 4983230072969 + 3 ^ 40 * 380132 * 2
def baseEnd_380132 : Nat := 86751301402227540223027

theorem tailTrace_380132 : CollatzResearch.WordTrace tailWord_380132 prefixEnd_380132 86751301402227540223027 := by
  unfold tailWord_380132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932276529427080111027325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9243035372569440148036433 6932276529427080111027325)
  ·
    refine ⟨2599603698535155041635247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6932276529427080111027325 2599603698535155041635247)
    ·
      refine ⟨3899405547802732562452871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599603698535155041635247 3899405547802732562452871)
      ·
        refine ⟨5849108321704098843679307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899405547802732562452871 5849108321704098843679307)
        ·
          refine ⟨8773662482556148265518961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849108321704098843679307 8773662482556148265518961)
          ·
            refine ⟨6580246861917111199139221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8773662482556148265518961 6580246861917111199139221)
            ·
              refine ⟨308449071652364587459651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6580246861917111199139221 308449071652364587459651)
              ·
                refine ⟨462673607478546881189477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308449071652364587459651 462673607478546881189477)
                ·
                  refine ⟨86751301402227540223027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462673607478546881189477 86751301402227540223027)
                  ·
                    rfl

theorem cell21_380132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_380132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380132 prefixEnd_380132 := by exact prefixLift 380132
  have htrace : WordTrace (prefixWord ++ tailWord_380132) baseStart_380132 baseEnd_380132 := by
    simpa [prefixWord, tailWord_380132, baseEnd_380132] using wordTrace_append hprefix tailTrace_380132
  have hstable : (prefixWord ++ tailWord_380132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380132).length < 2 ^ (prefixWord ++ tailWord_380132).sum := by decide
  have hdescent : baseEnd_380132 < baseStart_380132 := by decide
  rcases family_descends (prefixWord ++ tailWord_380132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380177 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 3]
def baseStart_380177 : Nat := 118140960795 + 380177 * 2 ^ 59
def prefixEnd_380177 : Nat := 4983230072969 + 3 ^ 40 * 380177 * 2
def baseEnd_380177 : Nat := 86761571015317461972935

theorem tailTrace_380177 : CollatzResearch.WordTrace tailWord_380177 prefixEnd_380177 86761571015317461972935 := by
  unfold tailWord_380177
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866194343691132907442785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9244129562460755271628523 13866194343691132907442785)
  ·
    refine ⟨10399645757768349680582089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13866194343691132907442785 10399645757768349680582089)
    ·
      refine ⟨7799734318326262260436567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10399645757768349680582089 7799734318326262260436567)
      ·
        refine ⟨11699601477489393390654851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7799734318326262260436567 11699601477489393390654851)
        ·
          refine ⟨17549402216234090085982277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11699601477489393390654851 17549402216234090085982277)
          ·
            refine ⟨3290512915543891891121677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17549402216234090085982277 3290512915543891891121677)
            ·
              refine ⟨1233942343328959459170629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3290512915543891891121677 1233942343328959459170629)
              ·
                refine ⟨231364189374179898594493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1233942343328959459170629 231364189374179898594493)
                ·
                  refine ⟨86761571015317461972935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231364189374179898594493 86761571015317461972935)
                  ·
                    rfl

theorem cell21_380177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_380177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380177 prefixEnd_380177 := by exact prefixLift 380177
  have htrace : WordTrace (prefixWord ++ tailWord_380177) baseStart_380177 baseEnd_380177 := by
    simpa [prefixWord, tailWord_380177, baseEnd_380177] using wordTrace_append hprefix tailTrace_380177
  have hstable : (prefixWord ++ tailWord_380177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380177).length < 2 ^ (prefixWord ++ tailWord_380177).sum := by decide
  have hdescent : baseEnd_380177 < baseStart_380177 := by decide
  rcases family_descends (prefixWord ++ tailWord_380177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380225 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 4]
def baseStart_380225 : Nat := 118140960795 + 380225 * 2 ^ 59
def prefixEnd_380225 : Nat := 4983230072969 + 3 ^ 40 * 380225 * 2
def baseEnd_380225 : Nat := 86772525269280045172837

theorem tailTrace_380225 : CollatzResearch.WordTrace tailWord_380225 prefixEnd_380225 86772525269280045172837 := by
  unfold tailWord_380225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867945047517237105190129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9245296698344824736793419 13867945047517237105190129)
  ·
    refine ⟨10400958785637927828892597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13867945047517237105190129 10400958785637927828892597)
    ·
      refine ⟨975089886153555733958681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10400958785637927828892597 975089886153555733958681)
      ·
        refine ⟨731317414615166800469011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975089886153555733958681 731317414615166800469011)
        ·
          refine ⟨1096976121922750200703517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731317414615166800469011 1096976121922750200703517)
          ·
            refine ⟨411366045721031325263819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1096976121922750200703517 411366045721031325263819)
            ·
              refine ⟨617049068581546987895729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411366045721031325263819 617049068581546987895729)
              ·
                refine ⟨462786801436160240921797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617049068581546987895729 462786801436160240921797)
                ·
                  refine ⟨86772525269280045172837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462786801436160240921797 86772525269280045172837)
                  ·
                    rfl

theorem cell21_380225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_380225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380225 prefixEnd_380225 := by exact prefixLift 380225
  have htrace : WordTrace (prefixWord ++ tailWord_380225) baseStart_380225 baseEnd_380225 := by
    simpa [prefixWord, tailWord_380225, baseEnd_380225] using wordTrace_append hprefix tailTrace_380225
  have hstable : (prefixWord ++ tailWord_380225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380225).length < 2 ^ (prefixWord ++ tailWord_380225).sum := by decide
  have hdescent : baseEnd_380225 < baseStart_380225 := by decide
  rcases family_descends (prefixWord ++ tailWord_380225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380236 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_380236 : Nat := 118140960795 + 380236 * 2 ^ 59
def prefixEnd_380236 : Nat := 4983230072969 + 3 ^ 40 * 380236 * 2
def baseEnd_380236 : Nat := 86775035619146470489481

theorem tailTrace_380236 : CollatzResearch.WordTrace tailWord_380236 prefixEnd_380236 86775035619146470489481 := by
  unfold tailWord_380236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934173125238692991920281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9245564166984923989227041 6934173125238692991920281)
  ·
    refine ⟨5200629843929019743940211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6934173125238692991920281 5200629843929019743940211)
    ·
      refine ⟨7800944765893529615910317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200629843929019743940211 7800944765893529615910317)
      ·
        refine ⟨2925354287210073605966369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7800944765893529615910317 2925354287210073605966369)
        ·
          refine ⟨2194015715407555204474777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925354287210073605966369 2194015715407555204474777)
          ·
            refine ⟨1645511786555666403356083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194015715407555204474777 1645511786555666403356083)
            ·
              refine ⟨2468267679833499605034125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645511786555666403356083 2468267679833499605034125)
              ·
                refine ⟨925600379937562351887797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2468267679833499605034125 925600379937562351887797)
                ·
                  refine ⟨86775035619146470489481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 925600379937562351887797 86775035619146470489481)
                  ·
                    rfl

theorem cell21_380236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_380236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380236 prefixEnd_380236 := by exact prefixLift 380236
  have htrace : WordTrace (prefixWord ++ tailWord_380236) baseStart_380236 baseEnd_380236 := by
    simpa [prefixWord, tailWord_380236, baseEnd_380236] using wordTrace_append hprefix tailTrace_380236
  have hstable : (prefixWord ++ tailWord_380236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380236).length < 2 ^ (prefixWord ++ tailWord_380236).sum := by decide
  have hdescent : baseEnd_380236 < baseStart_380236 := by decide
  rcases family_descends (prefixWord ++ tailWord_380236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380343 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_380343 : Nat := 118140960795 + 380343 * 2 ^ 59
def prefixEnd_380343 : Nat := 4983230072969 + 3 ^ 40 * 380343 * 2
def baseEnd_380343 : Nat := 86799454476938062205929

theorem tailTrace_380343 : CollatzResearch.WordTrace tailWord_380343 prefixEnd_380343 86799454476938062205929 := by
  unfold tailWord_380343
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872248861089743257985683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9248165907393162171990455 13872248861089743257985683)
  ·
    refine ⟨20808373291634614886978525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13872248861089743257985683 20808373291634614886978525)
    ·
      refine ⟨7803139984362980582616947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20808373291634614886978525 7803139984362980582616947)
      ·
        refine ⟨11704709976544470873925421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7803139984362980582616947 11704709976544470873925421)
        ·
          refine ⟨4389266241204176577722033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11704709976544470873925421 4389266241204176577722033)
          ·
            refine ⟨3291949680903132433291525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389266241204176577722033 3291949680903132433291525)
            ·
              refine ⟨617240565169337331242161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3291949680903132433291525 617240565169337331242161)
              ·
                refine ⟨462930423877002998431621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617240565169337331242161 462930423877002998431621)
                ·
                  refine ⟨86799454476938062205929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462930423877002998431621 86799454476938062205929)
                  ·
                    rfl

theorem cell21_380343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_380343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380343 prefixEnd_380343 := by exact prefixLift 380343
  have htrace : WordTrace (prefixWord ++ tailWord_380343) baseStart_380343 baseEnd_380343 := by
    simpa [prefixWord, tailWord_380343, baseEnd_380343] using wordTrace_append hprefix tailTrace_380343
  have hstable : (prefixWord ++ tailWord_380343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380343).length < 2 ^ (prefixWord ++ tailWord_380343).sum := by decide
  have hdescent : baseEnd_380343 < baseStart_380343 := by decide
  rcases family_descends (prefixWord ++ tailWord_380343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380405 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_380405 : Nat := 118140960795 + 380405 * 2 ^ 59
def prefixEnd_380405 : Nat := 4983230072969 + 3 ^ 40 * 380405 * 2
def baseEnd_380405 : Nat := 86813603721639732172469

theorem tailTrace_380405 : CollatzResearch.WordTrace tailWord_380405 prefixEnd_380405 86813603721639732172469 := by
  unfold tailWord_380405
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874510186865127846742669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9249673457910085231161779 13874510186865127846742669)
  ·
    refine ⟨5202941320074422942528501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13874510186865127846742669 5202941320074422942528501)
    ·
      refine ⟨487775748756977150862047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5202941320074422942528501 487775748756977150862047)
      ·
        refine ⟨731663623135465726293071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487775748756977150862047 731663623135465726293071)
        ·
          refine ⟨1097495434703198589439607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731663623135465726293071 1097495434703198589439607)
          ·
            refine ⟨1646243152054797884159411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097495434703198589439607 1646243152054797884159411)
            ·
              refine ⟨2469364728082196826239117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646243152054797884159411 2469364728082196826239117)
              ·
                refine ⟨926011773030823809839669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2469364728082196826239117 926011773030823809839669)
                ·
                  refine ⟨86813603721639732172469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926011773030823809839669 86813603721639732172469)
                  ·
                    rfl

theorem cell21_380405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_380405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380405 prefixEnd_380405 := by exact prefixLift 380405
  have htrace : WordTrace (prefixWord ++ tailWord_380405) baseStart_380405 baseEnd_380405 := by
    simpa [prefixWord, tailWord_380405, baseEnd_380405] using wordTrace_append hprefix tailTrace_380405
  have hstable : (prefixWord ++ tailWord_380405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380405).length < 2 ^ (prefixWord ++ tailWord_380405).sum := by decide
  have hdescent : baseEnd_380405 < baseStart_380405 := by decide
  rcases family_descends (prefixWord ++ tailWord_380405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380447 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_380447 : Nat := 118140960795 + 380447 * 2 ^ 59
def prefixEnd_380447 : Nat := 4983230072969 + 3 ^ 40 * 380447 * 2
def baseEnd_380447 : Nat := 86823188693856992472383

theorem tailTrace_380447 : CollatzResearch.WordTrace tailWord_380447 prefixEnd_380447 86823188693856992472383 := by
  unfold tailWord_380447
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876042052712969019771595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9250694701808646013181063 13876042052712969019771595)
  ·
    refine ⟨20814063079069453529657393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876042052712969019771595 20814063079069453529657393)
    ·
      refine ⟨15610547309302090147243045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20814063079069453529657393 15610547309302090147243045)
      ·
        refine ⟨2926977620494141902608071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15610547309302090147243045 2926977620494141902608071)
        ·
          refine ⟨4390466430741212853912107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926977620494141902608071 4390466430741212853912107)
          ·
            refine ⟨6585699646111819280868161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390466430741212853912107 6585699646111819280868161)
            ·
              refine ⟨4939274734583864460651121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585699646111819280868161 4939274734583864460651121)
              ·
                refine ⟨3704456050937898345488341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4939274734583864460651121 3704456050937898345488341)
                ·
                  refine ⟨86823188693856992472383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3704456050937898345488341 86823188693856992472383)
                  ·
                    rfl

theorem cell21_380447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_380447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380447 prefixEnd_380447 := by exact prefixLift 380447
  have htrace : WordTrace (prefixWord ++ tailWord_380447) baseStart_380447 baseEnd_380447 := by
    simpa [prefixWord, tailWord_380447, baseEnd_380447] using wordTrace_append hprefix tailTrace_380447
  have hstable : (prefixWord ++ tailWord_380447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380447).length < 2 ^ (prefixWord ++ tailWord_380447).sum := by decide
  have hdescent : baseEnd_380447 < baseStart_380447 := by decide
  rcases family_descends (prefixWord ++ tailWord_380447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380470 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_380470 : Nat := 118140960795 + 380470 * 2 ^ 59
def prefixEnd_380470 : Nat := 4983230072969 + 3 ^ 40 * 380470 * 2
def baseEnd_380470 : Nat := 86828437607214063589003

theorem tailTrace_380470 : CollatzResearch.WordTrace tailWord_380470 prefixEnd_380470 86828437607214063589003 := by
  unfold tailWord_380470
  simp only [CollatzResearch.WordTrace]
  refine ⟨867305058226852746741179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9251253954419762631905909 867305058226852746741179)
  ·
    refine ⟨1300957587340279120111769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867305058226852746741179 1300957587340279120111769)
    ·
      refine ⟨975718190505209340083827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1300957587340279120111769 975718190505209340083827)
      ·
        refine ⟨1463577285757814010125741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975718190505209340083827 1463577285757814010125741)
        ·
          refine ⟨548841482159180253797153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1463577285757814010125741 548841482159180253797153)
          ·
            refine ⟨411631111619385190347865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548841482159180253797153 411631111619385190347865)
            ·
              refine ⟨308723333714538892760899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411631111619385190347865 308723333714538892760899)
              ·
                refine ⟨463085000571808339141349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308723333714538892760899 463085000571808339141349)
                ·
                  refine ⟨86828437607214063589003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463085000571808339141349 86828437607214063589003)
                  ·
                    rfl

theorem cell21_380470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_380470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380470 prefixEnd_380470 := by exact prefixLift 380470
  have htrace : WordTrace (prefixWord ++ tailWord_380470) baseStart_380470 baseEnd_380470 := by
    simpa [prefixWord, tailWord_380470, baseEnd_380470] using wordTrace_append hprefix tailTrace_380470
  have hstable : (prefixWord ++ tailWord_380470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380470).length < 2 ^ (prefixWord ++ tailWord_380470).sum := by decide
  have hdescent : baseEnd_380470 < baseStart_380470 := by decide
  rcases family_descends (prefixWord ++ tailWord_380470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380574 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_380574 : Nat := 118140960795 + 380574 * 2 ^ 59
def prefixEnd_380574 : Nat := 4983230072969 + 3 ^ 40 * 380574 * 2
def baseEnd_380574 : Nat := 86852171824132993855457

theorem tailTrace_380574 : CollatzResearch.WordTrace tailWord_380574 prefixEnd_380574 86852171824132993855457 := by
  unfold tailWord_380574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735084265406608713705597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9253782748835246473096517 1735084265406608713705597)
  ·
    refine ⟨650656599527478267639599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1735084265406608713705597 650656599527478267639599)
    ·
      refine ⟨975984899291217401459399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650656599527478267639599 975984899291217401459399)
      ·
        refine ⟨1463977348936826102189099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975984899291217401459399 1463977348936826102189099)
        ·
          refine ⟨2195966023405239153283649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463977348936826102189099 2195966023405239153283649)
          ·
            refine ⟨1646974517553929364962737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195966023405239153283649 1646974517553929364962737)
            ·
              refine ⟨1235230888165447023722053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646974517553929364962737 1235230888165447023722053)
              ·
                refine ⟨231605791531021316947885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1235230888165447023722053 231605791531021316947885)
                ·
                  refine ⟨86852171824132993855457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231605791531021316947885 86852171824132993855457)
                  ·
                    rfl

theorem cell21_380574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_380574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380574 prefixEnd_380574 := by exact prefixLift 380574
  have htrace : WordTrace (prefixWord ++ tailWord_380574) baseStart_380574 baseEnd_380574 := by
    simpa [prefixWord, tailWord_380574, baseEnd_380574] using wordTrace_append hprefix tailTrace_380574
  have hstable : (prefixWord ++ tailWord_380574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380574).length < 2 ^ (prefixWord ++ tailWord_380574).sum := by decide
  have hdescent : baseEnd_380574 < baseStart_380574 := by decide
  rcases family_descends (prefixWord ++ tailWord_380574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380602 : List Nat := [3, 1, 1, 1, 2, 6, 2, 5]
def baseStart_380602 : Nat := 118140960795 + 380602 * 2 ^ 59
def prefixEnd_380602 : Nat := 4983230072969 + 3 ^ 40 * 380602 * 2
def baseEnd_380602 : Nat := 28952853935203722462911

theorem tailTrace_380602 : CollatzResearch.WordTrace tailWord_380602 prefixEnd_380602 28952853935203722462911 := by
  unfold tailWord_380602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470423841787857622916015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9254463578100953661109373 3470423841787857622916015)
  ·
    refine ⟨5205635762681786434374023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3470423841787857622916015 5205635762681786434374023)
    ·
      refine ⟨7808453644022679651561035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205635762681786434374023 7808453644022679651561035)
      ·
        refine ⟨11712680466034019477341553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7808453644022679651561035 11712680466034019477341553)
        ·
          refine ⟨8784510349525514608006165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11712680466034019477341553 8784510349525514608006165)
          ·
            refine ⟨411773922634008497250289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8784510349525514608006165 411773922634008497250289)
            ·
              refine ⟨308830441975506372937717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411773922634008497250289 308830441975506372937717)
              ·
                refine ⟨28952853935203722462911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308830441975506372937717 28952853935203722462911)
                ·
                  rfl

theorem cell21_380602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_380602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380602 prefixEnd_380602 := by exact prefixLift 380602
  have htrace : WordTrace (prefixWord ++ tailWord_380602) baseStart_380602 baseEnd_380602 := by
    simpa [prefixWord, tailWord_380602, baseEnd_380602] using wordTrace_append hprefix tailTrace_380602
  have hstable : (prefixWord ++ tailWord_380602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380602).length < 2 ^ (prefixWord ++ tailWord_380602).sum := by decide
  have hdescent : baseEnd_380602 < baseStart_380602 := by decide
  rcases family_descends (prefixWord ++ tailWord_380602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380726 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_380726 : Nat := 118140960795 + 380726 * 2 ^ 59
def prefixEnd_380726 : Nat := 4983230072969 + 3 ^ 40 * 380726 * 2
def baseEnd_380726 : Nat := 86886860295014507321813

theorem tailTrace_380726 : CollatzResearch.WordTrace tailWord_380726 prefixEnd_380726 86886860295014507321813 := by
  unfold tailWord_380726
  simp only [CollatzResearch.WordTrace]
  refine ⟨867888626168887479323627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9257478679134799779452021 867888626168887479323627)
  ·
    refine ⟨1301832939253331218985441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867888626168887479323627 1301832939253331218985441)
    ·
      refine ⟨976374704439998414239081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1301832939253331218985441 976374704439998414239081)
      ·
        refine ⟨732281028329998810679311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 976374704439998414239081 732281028329998810679311)
        ·
          refine ⟨1098421542494998216018967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732281028329998810679311 1098421542494998216018967)
          ·
            refine ⟨1647632313742497324028451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098421542494998216018967 1647632313742497324028451)
            ·
              refine ⟨2471448470613745986042677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647632313742497324028451 2471448470613745986042677)
              ·
                refine ⟨231698294120038686191501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2471448470613745986042677 231698294120038686191501)
                ·
                  refine ⟨86886860295014507321813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231698294120038686191501 86886860295014507321813)
                  ·
                    rfl

theorem cell21_380726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_380726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380726 prefixEnd_380726 := by exact prefixLift 380726
  have htrace : WordTrace (prefixWord ++ tailWord_380726) baseStart_380726 baseEnd_380726 := by
    simpa [prefixWord, tailWord_380726, baseEnd_380726] using wordTrace_append hprefix tailTrace_380726
  have hstable : (prefixWord ++ tailWord_380726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380726).length < 2 ^ (prefixWord ++ tailWord_380726).sum := by decide
  have hdescent : baseEnd_380726 < baseStart_380726 := by decide
  rcases family_descends (prefixWord ++ tailWord_380726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380771 : List Nat := [1, 1, 1, 5, 5, 1, 2, 5]
def baseStart_380771 : Nat := 118140960795 + 380771 * 2 ^ 59
def prefixEnd_380771 : Nat := 4983230072969 + 3 ^ 40 * 380771 * 2
def baseEnd_380771 : Nat := 28965709969368143023907

theorem tailTrace_380771 : CollatzResearch.WordTrace tailWord_380771 prefixEnd_380771 28965709969368143023907 := by
  unfold tailWord_380771
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887859303539172354566167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9258572869026114903044111 13887859303539172354566167)
  ·
    refine ⟨20831788955308758531849251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13887859303539172354566167 20831788955308758531849251)
    ·
      refine ⟨31247683432963137797773877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20831788955308758531849251 31247683432963137797773877)
      ·
        refine ⟨2929470321840294168541301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31247683432963137797773877 2929470321840294168541301)
        ·
          refine ⟨274637842672527578300747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2929470321840294168541301 274637842672527578300747)
          ·
            refine ⟨411956764008791367451121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274637842672527578300747 411956764008791367451121)
            ·
              refine ⟨308967573006593525588341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411956764008791367451121 308967573006593525588341)
              ·
                refine ⟨28965709969368143023907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308967573006593525588341 28965709969368143023907)
                ·
                  rfl

theorem cell21_380771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 5].length) (baseStart_380771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380771 prefixEnd_380771 := by exact prefixLift 380771
  have htrace : WordTrace (prefixWord ++ tailWord_380771) baseStart_380771 baseEnd_380771 := by
    simpa [prefixWord, tailWord_380771, baseEnd_380771] using wordTrace_append hprefix tailTrace_380771
  have hstable : (prefixWord ++ tailWord_380771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380771).length < 2 ^ (prefixWord ++ tailWord_380771).sum := by decide
  have hdescent : baseEnd_380771 < baseStart_380771 := by decide
  rcases family_descends (prefixWord ++ tailWord_380771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380841 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_380841 : Nat := 118140960795 + 380841 * 2 ^ 59
def prefixEnd_380841 : Nat := 4983230072969 + 3 ^ 40 * 380841 * 2
def baseEnd_380841 : Nat := 86913104861799862904911

theorem tailTrace_380841 : CollatzResearch.WordTrace tailWord_380841 prefixEnd_380841 86913104861799862904911 := by
  unfold tailWord_380841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13890412413285574309614377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9260274942190382873076251 13890412413285574309614377)
  ·
    refine ⟨10417809309964180732210783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13890412413285574309614377 10417809309964180732210783)
    ·
      refine ⟨15626713964946271098316175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417809309964180732210783 15626713964946271098316175)
      ·
        refine ⟨23440070947419406647474263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15626713964946271098316175 23440070947419406647474263)
        ·
          refine ⟨35160106421129109971211395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23440070947419406647474263 35160106421129109971211395)
          ·
            refine ⟨52740159631693664956817093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35160106421129109971211395 52740159631693664956817093)
            ·
              refine ⟨9888779930942562179403205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52740159631693664956817093 9888779930942562179403205)
              ·
                refine ⟨1854146237051730408638101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9888779930942562179403205 1854146237051730408638101)
                ·
                  refine ⟨86913104861799862904911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1854146237051730408638101 86913104861799862904911)
                  ·
                    rfl

theorem cell21_380841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_380841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380841 prefixEnd_380841 := by exact prefixLift 380841
  have htrace : WordTrace (prefixWord ++ tailWord_380841) baseStart_380841 baseEnd_380841 := by
    simpa [prefixWord, tailWord_380841, baseEnd_380841] using wordTrace_append hprefix tailTrace_380841
  have hstable : (prefixWord ++ tailWord_380841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380841).length < 2 ^ (prefixWord ++ tailWord_380841).sum := by decide
  have hdescent : baseEnd_380841 < baseStart_380841 := by decide
  rcases family_descends (prefixWord ++ tailWord_380841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380861 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 3]
def baseStart_380861 : Nat := 118140960795 + 380861 * 2 ^ 59
def prefixEnd_380861 : Nat := 4983230072969 + 3 ^ 40 * 380861 * 2
def baseEnd_380861 : Nat := 86917669134284272571537

theorem tailTrace_380861 : CollatzResearch.WordTrace tailWord_380861 prefixEnd_380861 86917669134284272571537 := by
  unfold tailWord_380861
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891141873213117725342437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9260761248808745150228291 13891141873213117725342437)
  ·
    refine ⟨2604589101227459573501707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13891141873213117725342437 2604589101227459573501707)
    ·
      refine ⟨3906883651841189360252561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604589101227459573501707 3906883651841189360252561)
      ·
        refine ⟨2930162738880892020189421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3906883651841189360252561 2930162738880892020189421)
        ·
          refine ⟨1098811027080334507571033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2930162738880892020189421 1098811027080334507571033)
          ·
            refine ⟨824108270310250880678275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098811027080334507571033 824108270310250880678275)
            ·
              refine ⟨1236162405465376321017413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824108270310250880678275 1236162405465376321017413)
              ·
                refine ⟨231780451024758060190765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1236162405465376321017413 231780451024758060190765)
                ·
                  refine ⟨86917669134284272571537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231780451024758060190765 86917669134284272571537)
                  ·
                    rfl

theorem cell21_380861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_380861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380861 prefixEnd_380861 := by exact prefixLift 380861
  have htrace : WordTrace (prefixWord ++ tailWord_380861) baseStart_380861 baseEnd_380861 := by
    simpa [prefixWord, tailWord_380861, baseEnd_380861] using wordTrace_append hprefix tailTrace_380861
  have hstable : (prefixWord ++ tailWord_380861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380861).length < 2 ^ (prefixWord ++ tailWord_380861).sum := by decide
  have hdescent : baseEnd_380861 < baseStart_380861 := by decide
  rcases family_descends (prefixWord ++ tailWord_380861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380909 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 4]
def baseStart_380909 : Nat := 118140960795 + 380909 * 2 ^ 59
def prefixEnd_380909 : Nat := 4983230072969 + 3 ^ 40 * 380909 * 2
def baseEnd_380909 : Nat := 86928623388246855771439

theorem tailTrace_380909 : CollatzResearch.WordTrace tailWord_380909 prefixEnd_380909 86928623388246855771439 := by
  unfold tailWord_380909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892892577039221923089781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9261928384692814615393187 13892892577039221923089781)
  ·
    refine ⟨1302458679097427055289667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13892892577039221923089781 1302458679097427055289667)
    ·
      refine ⟨1953688018646140582934501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302458679097427055289667 1953688018646140582934501)
      ·
        refine ⟨366316503496151359300219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1953688018646140582934501 366316503496151359300219)
        ·
          refine ⟨549474755244227038950329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366316503496151359300219 549474755244227038950329)
          ·
            refine ⟨412106066433170279212747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549474755244227038950329 412106066433170279212747)
            ·
              refine ⟨618159099649755418819121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412106066433170279212747 618159099649755418819121)
              ·
                refine ⟨463619324737316564114341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618159099649755418819121 463619324737316564114341)
                ·
                  refine ⟨86928623388246855771439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463619324737316564114341 86928623388246855771439)
                  ·
                    rfl

theorem cell21_380909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_380909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380909 prefixEnd_380909 := by exact prefixLift 380909
  have htrace : WordTrace (prefixWord ++ tailWord_380909) baseStart_380909 baseEnd_380909 := by
    simpa [prefixWord, tailWord_380909, baseEnd_380909] using wordTrace_append hprefix tailTrace_380909
  have hstable : (prefixWord ++ tailWord_380909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380909).length < 2 ^ (prefixWord ++ tailWord_380909).sum := by decide
  have hdescent : baseEnd_380909 < baseStart_380909 := by decide
  rcases family_descends (prefixWord ++ tailWord_380909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380920 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_380920 : Nat := 118140960795 + 380920 * 2 ^ 59
def prefixEnd_380920 : Nat := 4983230072969 + 3 ^ 40 * 380920 * 2
def baseEnd_380920 : Nat := 86931133738113281088083

theorem tailTrace_380920 : CollatzResearch.WordTrace tailWord_380920 prefixEnd_380920 86931133738113281088083 := by
  unfold tailWord_380920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946646889999685400870107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9262195853332913867826809 6946646889999685400870107)
  ·
    refine ⟨10419970334999528101305161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6946646889999685400870107 10419970334999528101305161)
    ·
      refine ⟨7814977751249646075978871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10419970334999528101305161 7814977751249646075978871)
      ·
        refine ⟨11722466626874469113968307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7814977751249646075978871 11722466626874469113968307)
        ·
          refine ⟨17583699940311703670952461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722466626874469113968307 17583699940311703670952461)
          ·
            refine ⟨6593887477616888876607173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17583699940311703670952461 6593887477616888876607173)
            ·
              refine ⟨1236353902053166664363845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6593887477616888876607173 1236353902053166664363845)
              ·
                refine ⟨231816356634968749568221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1236353902053166664363845 231816356634968749568221)
                ·
                  refine ⟨86931133738113281088083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231816356634968749568221 86931133738113281088083)
                  ·
                    rfl

theorem cell21_380920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_380920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380920 prefixEnd_380920 := by exact prefixLift 380920
  have htrace : WordTrace (prefixWord ++ tailWord_380920) baseStart_380920 baseEnd_380920 := by
    simpa [prefixWord, tailWord_380920, baseEnd_380920] using wordTrace_append hprefix tailTrace_380920
  have hstable : (prefixWord ++ tailWord_380920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380920).length < 2 ^ (prefixWord ++ tailWord_380920).sum := by decide
  have hdescent : baseEnd_380920 < baseStart_380920 := by decide
  rcases family_descends (prefixWord ++ tailWord_380920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380979 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_380979 : Nat := 118140960795 + 380979 * 2 ^ 59
def prefixEnd_380979 : Nat := 4983230072969 + 3 ^ 40 * 380979 * 2
def baseEnd_380979 : Nat := 86944598341942289604629

theorem tailTrace_380979 : CollatzResearch.WordTrace tailWord_380979 prefixEnd_380979 86944598341942289604629 := by
  unfold tailWord_380979
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895445686785623878137991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9263630457857082585425327 13895445686785623878137991)
  ·
    refine ⟨20843168530178435817206987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13895445686785623878137991 20843168530178435817206987)
    ·
      refine ⟨31264752795267653725810481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20843168530178435817206987 31264752795267653725810481)
      ·
        refine ⟨23448564596450740294357861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31264752795267653725810481 23448564596450740294357861)
        ·
          refine ⟨4396605861834513805192099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23448564596450740294357861 4396605861834513805192099)
          ·
            refine ⟨6594908792751770707788149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396605861834513805192099 6594908792751770707788149)
            ·
              refine ⟨618272699320478503855139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6594908792751770707788149 618272699320478503855139)
              ·
                refine ⟨927409048980717755782709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618272699320478503855139 927409048980717755782709)
                ·
                  refine ⟨86944598341942289604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927409048980717755782709 86944598341942289604629)
                  ·
                    rfl

theorem cell21_380979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_380979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380979 prefixEnd_380979 := by exact prefixLift 380979
  have htrace : WordTrace (prefixWord ++ tailWord_380979) baseStart_380979 baseEnd_380979 := by
    simpa [prefixWord, tailWord_380979, baseEnd_380979] using wordTrace_append hprefix tailTrace_380979
  have hstable : (prefixWord ++ tailWord_380979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380979).length < 2 ^ (prefixWord ++ tailWord_380979).sum := by decide
  have hdescent : baseEnd_380979 < baseStart_380979 := by decide
  rcases family_descends (prefixWord ++ tailWord_380979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380985 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 4]
def baseStart_380985 : Nat := 118140960795 + 380985 * 2 ^ 59
def prefixEnd_380985 : Nat := 4983230072969 + 3 ^ 40 * 380985 * 2
def baseEnd_380985 : Nat := 86945967623687612504617

theorem tailTrace_380985 : CollatzResearch.WordTrace tailWord_380985 prefixEnd_380985 86945967623687612504617 := by
  unfold tailWord_380985
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895664524763886902856409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9263776349842591268570939 13895664524763886902856409)
  ·
    refine ⟨10421748393572915177142307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13895664524763886902856409 10421748393572915177142307)
    ·
      refine ⟨15632622590359372765713461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421748393572915177142307 15632622590359372765713461)
      ·
        refine ⟨1465558367846191196785637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15632622590359372765713461 1465558367846191196785637)
        ·
          refine ⟨274792193971160849397307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1465558367846191196785637 274792193971160849397307)
          ·
            refine ⟨412188290956741274095961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274792193971160849397307 412188290956741274095961)
            ·
              refine ⟨309141218217555955571971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412188290956741274095961 309141218217555955571971)
              ·
                refine ⟨463711827326333933357957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309141218217555955571971 463711827326333933357957)
                ·
                  refine ⟨86945967623687612504617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463711827326333933357957 86945967623687612504617)
                  ·
                    rfl

theorem cell21_380985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_380985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_380985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_380985 prefixEnd_380985 := by exact prefixLift 380985
  have htrace : WordTrace (prefixWord ++ tailWord_380985) baseStart_380985 baseEnd_380985 := by
    simpa [prefixWord, tailWord_380985, baseEnd_380985] using wordTrace_append hprefix tailTrace_380985
  have hstable : (prefixWord ++ tailWord_380985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380985).length < 2 ^ (prefixWord ++ tailWord_380985).sum := by decide
  have hdescent : baseEnd_380985 < baseStart_380985 := by decide
  rcases family_descends (prefixWord ++ tailWord_380985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381072 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_381072 : Nat := 118140960795 + 381072 * 2 ^ 59
def prefixEnd_381072 : Nat := 4983230072969 + 3 ^ 40 * 381072 * 2
def baseEnd_381072 : Nat := 86965822208994794554439

theorem tailTrace_381072 : CollatzResearch.WordTrace tailWord_381072 prefixEnd_381072 86965822208994794554439 := by
  unfold tailWord_381072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949418837724350380636735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9265891783632467174182313 6949418837724350380636735)
  ·
    refine ⟨10424128256586525570955103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949418837724350380636735 10424128256586525570955103)
    ·
      refine ⟨15636192384879788356432655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10424128256586525570955103 15636192384879788356432655)
      ·
        refine ⟨23454288577319682534648983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15636192384879788356432655 23454288577319682534648983)
        ·
          refine ⟨35181432865979523801973475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23454288577319682534648983 35181432865979523801973475)
          ·
            refine ⟨52772149298969285702960213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35181432865979523801973475 52772149298969285702960213)
            ·
              refine ⟨618423624597296316831565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 52772149298969285702960213 618423624597296316831565)
              ·
                refine ⟨231908859223986118811837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618423624597296316831565 231908859223986118811837)
                ·
                  refine ⟨86965822208994794554439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231908859223986118811837 86965822208994794554439)
                  ·
                    rfl

theorem cell21_381072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_381072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381072 prefixEnd_381072 := by exact prefixLift 381072
  have htrace : WordTrace (prefixWord ++ tailWord_381072) baseStart_381072 baseEnd_381072 := by
    simpa [prefixWord, tailWord_381072, baseEnd_381072] using wordTrace_append hprefix tailTrace_381072
  have hstable : (prefixWord ++ tailWord_381072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381072).length < 2 ^ (prefixWord ++ tailWord_381072).sum := by decide
  have hdescent : baseEnd_381072 < baseStart_381072 := by decide
  rcases family_descends (prefixWord ++ tailWord_381072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381078 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_381078 : Nat := 118140960795 + 381078 * 2 ^ 59
def prefixEnd_381078 : Nat := 4983230072969 + 3 ^ 40 * 381078 * 2
def baseEnd_381078 : Nat := 86967191490740117454427

theorem tailTrace_381078 : CollatzResearch.WordTrace tailWord_381078 prefixEnd_381078 86967191490740117454427 := by
  unfold tailWord_381078
  simp only [CollatzResearch.WordTrace]
  refine ⟨868691032089185236624493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9266037675617975857327925 868691032089185236624493)
  ·
    refine ⟨325759137033444463734185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 868691032089185236624493 325759137033444463734185)
    ·
      refine ⟨244319352775083347800639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325759137033444463734185 244319352775083347800639)
      ·
        refine ⟨366479029162625021700959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244319352775083347800639 366479029162625021700959)
        ·
          refine ⟨549718543743937532551439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366479029162625021700959 549718543743937532551439)
          ·
            refine ⟨824577815615906298827159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549718543743937532551439 824577815615906298827159)
            ·
              refine ⟨1236866723423859448240739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824577815615906298827159 1236866723423859448240739)
              ·
                refine ⟨1855300085135789172361109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236866723423859448240739 1855300085135789172361109)
                ·
                  refine ⟨86967191490740117454427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1855300085135789172361109 86967191490740117454427)
                  ·
                    rfl

theorem cell21_381078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_381078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381078 prefixEnd_381078 := by exact prefixLift 381078
  have htrace : WordTrace (prefixWord ++ tailWord_381078) baseStart_381078 baseEnd_381078 := by
    simpa [prefixWord, tailWord_381078, baseEnd_381078] using wordTrace_append hprefix tailTrace_381078
  have hstable : (prefixWord ++ tailWord_381078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381078).length < 2 ^ (prefixWord ++ tailWord_381078).sum := by decide
  have hdescent : baseEnd_381078 < baseStart_381078 := by decide
  rcases family_descends (prefixWord ++ tailWord_381078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381145 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_381145 : Nat := 118140960795 + 381145 * 2 ^ 59
def prefixEnd_381145 : Nat := 4983230072969 + 3 ^ 40 * 381145 * 2
def baseEnd_381145 : Nat := 86982481803562889837623

theorem tailTrace_381145 : CollatzResearch.WordTrace tailWord_381145 prefixEnd_381145 86982481803562889837623 := by
  unfold tailWord_381145
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901500204184234228680889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9267666802789489485787259 13901500204184234228680889)
  ·
    refine ⟨10426125153138175671510667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13901500204184234228680889 10426125153138175671510667)
    ·
      refine ⟨15639187729707263507266001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10426125153138175671510667 15639187729707263507266001)
      ·
        refine ⟨11729390797280447630449501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15639187729707263507266001 11729390797280447630449501)
        ·
          refine ⟨4398521548980167861418563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11729390797280447630449501 4398521548980167861418563)
          ·
            refine ⟨6597782323470251792127845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398521548980167861418563 6597782323470251792127845)
            ·
              refine ⟨1237084185650672211023971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6597782323470251792127845 1237084185650672211023971)
              ·
                refine ⟨1855626278476008316535957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237084185650672211023971 1855626278476008316535957)
                ·
                  refine ⟨86982481803562889837623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1855626278476008316535957 86982481803562889837623)
                  ·
                    rfl

theorem cell21_381145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_381145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381145 prefixEnd_381145 := by exact prefixLift 381145
  have htrace : WordTrace (prefixWord ++ tailWord_381145) baseStart_381145 baseEnd_381145 := by
    simpa [prefixWord, tailWord_381145, baseEnd_381145] using wordTrace_append hprefix tailTrace_381145
  have hstable : (prefixWord ++ tailWord_381145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381145).length < 2 ^ (prefixWord ++ tailWord_381145).sum := by decide
  have hdescent : baseEnd_381145 < baseStart_381145 := by decide
  rcases family_descends (prefixWord ++ tailWord_381145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381162 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_381162 : Nat := 118140960795 + 381162 * 2 ^ 59
def prefixEnd_381162 : Nat := 4983230072969 + 3 ^ 40 * 381162 * 2
def baseEnd_381162 : Nat := 86986361435174638054255

theorem tailTrace_381162 : CollatzResearch.WordTrace tailWord_381162 prefixEnd_381162 86986361435174638054255 := by
  unfold tailWord_381162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475530061280661533012435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9268080163415097421366493 3475530061280661533012435)
  ·
    refine ⟨5213295091920992299518653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3475530061280661533012435 5213295091920992299518653)
    ·
      refine ⟨1954985659470372112319495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5213295091920992299518653 1954985659470372112319495)
      ·
        refine ⟨2932478489205558168479243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954985659470372112319495 2932478489205558168479243)
        ·
          refine ⟨4398717733808337252718865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932478489205558168479243 4398717733808337252718865)
          ·
            refine ⟨3299038300356252939539149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398717733808337252718865 3299038300356252939539149)
            ·
              refine ⟨1237139362633594852327181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3299038300356252939539149 1237139362633594852327181)
              ·
                refine ⟨463927260987598069622693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1237139362633594852327181 463927260987598069622693)
                ·
                  refine ⟨86986361435174638054255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463927260987598069622693 86986361435174638054255)
                  ·
                    rfl

theorem cell21_381162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_381162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381162 prefixEnd_381162 := by exact prefixLift 381162
  have htrace : WordTrace (prefixWord ++ tailWord_381162) baseStart_381162 baseEnd_381162 := by
    simpa [prefixWord, tailWord_381162, baseEnd_381162] using wordTrace_append hprefix tailTrace_381162
  have hstable : (prefixWord ++ tailWord_381162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381162).length < 2 ^ (prefixWord ++ tailWord_381162).sum := by decide
  have hdescent : baseEnd_381162 < baseStart_381162 := by decide
  rcases family_descends (prefixWord ++ tailWord_381162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381210 : List Nat := [3, 1, 1, 3, 5, 1, 1, 6]
def baseStart_381210 : Nat := 118140960795 + 381210 * 2 ^ 59
def prefixEnd_381210 : Nat := 4983230072969 + 3 ^ 40 * 381210 * 2
def baseEnd_381210 : Nat := 28999105229712407084719

theorem tailTrace_381210 : CollatzResearch.WordTrace tailWord_381210 prefixEnd_381210 28999105229712407084719 := by
  unfold tailWord_381210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475967737237187582449271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9269247299299166886531389 3475967737237187582449271)
  ·
    refine ⟨5213951605855781373673907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3475967737237187582449271 5213951605855781373673907)
    ·
      refine ⟨7820927408783672060510861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213951605855781373673907 7820927408783672060510861)
      ·
        refine ⟨2932847778293877022691573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7820927408783672060510861 2932847778293877022691573)
        ·
          refine ⟨274954479215050970877335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2932847778293877022691573 274954479215050970877335)
          ·
            refine ⟨412431718822576456316003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274954479215050970877335 412431718822576456316003)
            ·
              refine ⟨618647578233864684474005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412431718822576456316003 618647578233864684474005)
              ·
                refine ⟨28999105229712407084719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 618647578233864684474005 28999105229712407084719)
                ·
                  rfl

theorem cell21_381210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_381210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381210 prefixEnd_381210 := by exact prefixLift 381210
  have htrace : WordTrace (prefixWord ++ tailWord_381210) baseStart_381210 baseEnd_381210 := by
    simpa [prefixWord, tailWord_381210, baseEnd_381210] using wordTrace_append hprefix tailTrace_381210
  have hstable : (prefixWord ++ tailWord_381210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381210).length < 2 ^ (prefixWord ++ tailWord_381210).sum := by decide
  have hdescent : baseEnd_381210 < baseStart_381210 := by decide
  rcases family_descends (prefixWord ++ tailWord_381210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381224 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_381224 : Nat := 118140960795 + 381224 * 2 ^ 59
def prefixEnd_381224 : Nat := 4983230072969 + 3 ^ 40 * 381224 * 2
def baseEnd_381224 : Nat := 87000510679876308020795

theorem tailTrace_381224 : CollatzResearch.WordTrace tailWord_381224 prefixEnd_381224 87000510679876308020795 := by
  unfold tailWord_381224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952190785449015360403363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9269587713932020480537817 6952190785449015360403363)
  ·
    refine ⟨10428286178173523040605045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6952190785449015360403363 10428286178173523040605045)
    ·
      refine ⟨977651829203767785056723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10428286178173523040605045 977651829203767785056723)
      ·
        refine ⟨1466477743805651677585085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977651829203767785056723 1466477743805651677585085)
        ·
          refine ⟨549929153927119379094407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1466477743805651677585085 549929153927119379094407)
          ·
            refine ⟨824893730890679068641611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549929153927119379094407 824893730890679068641611)
            ·
              refine ⟨1237340596336018602962417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824893730890679068641611 1237340596336018602962417)
              ·
                refine ⟨928005447252013952221813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237340596336018602962417 928005447252013952221813)
                ·
                  refine ⟨87000510679876308020795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928005447252013952221813 87000510679876308020795)
                  ·
                    rfl

theorem cell21_381224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_381224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381224 prefixEnd_381224 := by exact prefixLift 381224
  have htrace : WordTrace (prefixWord ++ tailWord_381224) baseStart_381224 baseEnd_381224 := by
    simpa [prefixWord, tailWord_381224, baseEnd_381224] using wordTrace_append hprefix tailTrace_381224
  have hstable : (prefixWord ++ tailWord_381224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381224).length < 2 ^ (prefixWord ++ tailWord_381224).sum := by decide
  have hdescent : baseEnd_381224 < baseStart_381224 := by decide
  rcases family_descends (prefixWord ++ tailWord_381224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381241 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 3]
def baseStart_381241 : Nat := 118140960795 + 381241 * 2 ^ 59
def prefixEnd_381241 : Nat := 4983230072969 + 3 ^ 40 * 381241 * 2
def baseEnd_381241 : Nat := 87004390311488056237427

theorem tailTrace_381241 : CollatzResearch.WordTrace tailWord_381241 prefixEnd_381241 87004390311488056237427 := by
  unfold tailWord_381241
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905001611836442624175577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9270001074557628416117051 13905001611836442624175577)
  ·
    refine ⟨10428751208877331968131683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13905001611836442624175577 10428751208877331968131683)
    ·
      refine ⟨15643126813315997952197525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10428751208877331968131683 15643126813315997952197525)
      ·
        refine ⟨733271569374187404009259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15643126813315997952197525 733271569374187404009259)
        ·
          refine ⟨1099907354061281106013889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733271569374187404009259 1099907354061281106013889)
          ·
            refine ⟨824930515545960829510417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099907354061281106013889 824930515545960829510417)
            ·
              refine ⟨618697886659470622132813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824930515545960829510417 618697886659470622132813)
              ·
                refine ⟨232011707497301483299805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618697886659470622132813 232011707497301483299805)
                ·
                  refine ⟨87004390311488056237427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232011707497301483299805 87004390311488056237427)
                  ·
                    rfl

theorem cell21_381241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_381241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381241 prefixEnd_381241 := by exact prefixLift 381241
  have htrace : WordTrace (prefixWord ++ tailWord_381241) baseStart_381241 baseEnd_381241 := by
    simpa [prefixWord, tailWord_381241, baseEnd_381241] using wordTrace_append hprefix tailTrace_381241
  have hstable : (prefixWord ++ tailWord_381241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381241).length < 2 ^ (prefixWord ++ tailWord_381241).sum := by decide
  have hdescent : baseEnd_381241 < baseStart_381241 := by decide
  rcases family_descends (prefixWord ++ tailWord_381241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381278 : List Nat := [4, 4, 2, 1, 2, 1, 2, 5]
def baseStart_381278 : Nat := 118140960795 + 381278 * 2 ^ 59
def prefixEnd_381278 : Nat := 4983230072969 + 3 ^ 40 * 381278 * 2
def baseEnd_381278 : Nat := 29004278071861404706895

theorem tailTrace_381278 : CollatzResearch.WordTrace tailWord_381278 prefixEnd_381278 29004278071861404706895 := by
  unfold tailWord_381278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738293889087799742909061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9270900741801598628848325 1738293889087799742909061)
  ·
    refine ⟨325930104203962451795449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1738293889087799742909061 325930104203962451795449)
    ·
      refine ⟨244447578152971838846587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325930104203962451795449 244447578152971838846587)
      ·
        refine ⟨366671367229457758269881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244447578152971838846587 366671367229457758269881)
        ·
          refine ⟨275003525422093318702411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366671367229457758269881 275003525422093318702411)
          ·
            refine ⟨412505288133139978053617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275003525422093318702411 412505288133139978053617)
            ·
              refine ⟨309378966099854983540213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412505288133139978053617 309378966099854983540213)
              ·
                refine ⟨29004278071861404706895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 309378966099854983540213 29004278071861404706895)
                ·
                  rfl

theorem cell21_381278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_381278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381278 prefixEnd_381278 := by exact prefixLift 381278
  have htrace : WordTrace (prefixWord ++ tailWord_381278) baseStart_381278 baseEnd_381278 := by
    simpa [prefixWord, tailWord_381278, baseEnd_381278] using wordTrace_append hprefix tailTrace_381278
  have hstable : (prefixWord ++ tailWord_381278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381278).length < 2 ^ (prefixWord ++ tailWord_381278).sum := by decide
  have hdescent : baseEnd_381278 < baseStart_381278 := by decide
  rcases family_descends (prefixWord ++ tailWord_381278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381469 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 3]
def baseStart_381469 : Nat := 118140960795 + 381469 * 2 ^ 59
def prefixEnd_381469 : Nat := 4983230072969 + 3 ^ 40 * 381469 * 2
def baseEnd_381469 : Nat := 87056423017810326436961

theorem tailTrace_381469 : CollatzResearch.WordTrace tailWord_381469 prefixEnd_381469 87056423017810326436961 := by
  unfold tailWord_381469
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913317455010437563475461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9275544970006958375650307 13913317455010437563475461)
  ·
    refine ⟨2608747022814457043151649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13913317455010437563475461 2608747022814457043151649)
    ·
      refine ⟨1956560267110842782363737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2608747022814457043151649 1956560267110842782363737)
      ·
        refine ⟨1467420200333132086772803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1956560267110842782363737 1467420200333132086772803)
        ·
          refine ⟨2201130300499698130159205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467420200333132086772803 2201130300499698130159205)
          ·
            refine ⟨412711931343693399404851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2201130300499698130159205 412711931343693399404851)
            ·
              refine ⟨619067897015540099107277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412711931343693399404851 619067897015540099107277)
              ·
                refine ⟨232150461380827537165229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619067897015540099107277 232150461380827537165229)
                ·
                  refine ⟨87056423017810326436961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232150461380827537165229 87056423017810326436961)
                  ·
                    rfl

theorem cell21_381469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_381469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381469 prefixEnd_381469 := by exact prefixLift 381469
  have htrace : WordTrace (prefixWord ++ tailWord_381469) baseStart_381469 baseEnd_381469 := by
    simpa [prefixWord, tailWord_381469, baseEnd_381469] using wordTrace_append hprefix tailTrace_381469
  have hstable : (prefixWord ++ tailWord_381469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381469).length < 2 ^ (prefixWord ++ tailWord_381469).sum := by decide
  have hdescent : baseEnd_381469 < baseStart_381469 := by decide
  rcases family_descends (prefixWord ++ tailWord_381469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381480 : List Nat := [2, 1, 5, 2, 1, 1, 9]
def baseStart_381480 : Nat := 118140960795 + 381480 * 2 ^ 59
def prefixEnd_381480 : Nat := 4983230072969 + 3 ^ 40 * 381480 * 2
def baseEnd_381480 : Nat := 9673214818630750194845

theorem tailTrace_381480 : CollatzResearch.WordTrace tailWord_381480 prefixEnd_381480 9673214818630750194845 := by
  unfold tailWord_381480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956859328985293221062947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9275812438647057628083929 6956859328985293221062947)
  ·
    refine ⟨10435288993477939831594421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6956859328985293221062947 10435288993477939831594421)
    ·
      refine ⟨978308343138556859211977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10435288993477939831594421 978308343138556859211977)
      ·
        refine ⟨733731257353917644408983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978308343138556859211977 733731257353917644408983)
        ·
          refine ⟨1100596886030876466613475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733731257353917644408983 1100596886030876466613475)
          ·
            refine ⟨1650895329046314699920213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100596886030876466613475 1650895329046314699920213)
            ·
              refine ⟨9673214818630750194845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1650895329046314699920213 9673214818630750194845)
              ·
                rfl

theorem cell21_381480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 9].length) (baseStart_381480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381480 prefixEnd_381480 := by exact prefixLift 381480
  have htrace : WordTrace (prefixWord ++ tailWord_381480) baseStart_381480 baseEnd_381480 := by
    simpa [prefixWord, tailWord_381480, baseEnd_381480] using wordTrace_append hprefix tailTrace_381480
  have hstable : (prefixWord ++ tailWord_381480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381480).length < 2 ^ (prefixWord ++ tailWord_381480).sum := by decide
  have hdescent : baseEnd_381480 < baseStart_381480 := by decide
  rcases family_descends (prefixWord ++ tailWord_381480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381486 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_381486 : Nat := 118140960795 + 381486 * 2 ^ 59
def prefixEnd_381486 : Nat := 4983230072969 + 3 ^ 40 * 381486 * 2
def baseEnd_381486 : Nat := 87060302649422074653593

theorem tailTrace_381486 : CollatzResearch.WordTrace tailWord_381486 prefixEnd_381486 87060302649422074653593 := by
  unfold tailWord_381486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739242186993606183355539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9275958330632566311229541 1739242186993606183355539)
  ·
    refine ⟨2608863280490409275033309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739242186993606183355539 2608863280490409275033309)
    ·
      refine ⟨978323730183903478137491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2608863280490409275033309 978323730183903478137491)
      ·
        refine ⟨1467485595275855217206237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978323730183903478137491 1467485595275855217206237)
        ·
          refine ⟨550307098228445706452339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1467485595275855217206237 550307098228445706452339)
          ·
            refine ⟨825460647342668559678509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550307098228445706452339 825460647342668559678509)
            ·
              refine ⟨309547742753500709879441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825460647342668559678509 309547742753500709879441)
              ·
                refine ⟨232160807065125532409581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309547742753500709879441 232160807065125532409581)
                ·
                  refine ⟨87060302649422074653593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232160807065125532409581 87060302649422074653593)
                  ·
                    rfl

theorem cell21_381486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_381486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381486 prefixEnd_381486 := by exact prefixLift 381486
  have htrace : WordTrace (prefixWord ++ tailWord_381486) baseStart_381486 baseEnd_381486 := by
    simpa [prefixWord, tailWord_381486, baseEnd_381486] using wordTrace_append hprefix tailTrace_381486
  have hstable : (prefixWord ++ tailWord_381486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381486).length < 2 ^ (prefixWord ++ tailWord_381486).sum := by decide
  have hdescent : baseEnd_381486 < baseStart_381486 := by decide
  rcases family_descends (prefixWord ++ tailWord_381486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381632 : List Nat := [2, 1, 1, 2, 4, 2, 4, 5]
def baseStart_381632 : Nat := 118140960795 + 381632 * 2 ^ 59
def prefixEnd_381632 : Nat := 4983230072969 + 3 ^ 40 * 381632 * 2
def baseEnd_381632 : Nat := 29031207279519421739987

theorem tailTrace_381632 : CollatzResearch.WordTrace tailWord_381632 prefixEnd_381632 29031207279519421739987 := by
  unfold tailWord_381632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959631276709958200829575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9279508368946610934439433 6959631276709958200829575)
  ·
    refine ⟨10439446915064937301244363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6959631276709958200829575 10439446915064937301244363)
    ·
      refine ⟨15659170372597405951866545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439446915064937301244363 15659170372597405951866545)
      ·
        refine ⟨11744377779448054463899909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15659170372597405951866545 11744377779448054463899909)
        ·
          refine ⟨2202070833646510211981233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11744377779448054463899909 2202070833646510211981233)
          ·
            refine ⟨1651553125234882658985925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202070833646510211981233 1651553125234882658985925)
            ·
              refine ⟨309666210981540498559861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1651553125234882658985925 309666210981540498559861)
              ·
                refine ⟨29031207279519421739987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 309666210981540498559861 29031207279519421739987)
                ·
                  rfl

theorem cell21_381632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_381632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381632 prefixEnd_381632 := by exact prefixLift 381632
  have htrace : WordTrace (prefixWord ++ tailWord_381632) baseStart_381632 baseEnd_381632 := by
    simpa [prefixWord, tailWord_381632, baseEnd_381632] using wordTrace_append hprefix tailTrace_381632
  have hstable : (prefixWord ++ tailWord_381632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381632).length < 2 ^ (prefixWord ++ tailWord_381632).sum := by decide
  have hdescent : baseEnd_381632 < baseStart_381632 := by decide
  rcases family_descends (prefixWord ++ tailWord_381632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381663 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 5]
def baseStart_381663 : Nat := 118140960795 + 381663 * 2 ^ 59
def prefixEnd_381663 : Nat := 4983230072969 + 3 ^ 40 * 381663 * 2
def baseEnd_381663 : Nat := 87100696460909100203231

theorem tailTrace_381663 : CollatzResearch.WordTrace tailWord_381663 prefixEnd_381663 87100696460909100203231 := by
  unfold tailWord_381663
  simp only [CollatzResearch.WordTrace]
  refine ⟨13920393216307608696037643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9280262144205072464025095 13920393216307608696037643)
  ·
    refine ⟨20880589824461413044056465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13920393216307608696037643 20880589824461413044056465)
    ·
      refine ⟨15660442368346059783042349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20880589824461413044056465 15660442368346059783042349)
      ·
        refine ⟨5872665888129772418640881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15660442368346059783042349 5872665888129772418640881)
        ·
          refine ⟨4404499416097329313980661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5872665888129772418640881 4404499416097329313980661)
          ·
            refine ⟨412921820259124623185687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4404499416097329313980661 412921820259124623185687)
            ·
              refine ⟨619382730388686934778531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412921820259124623185687 619382730388686934778531)
              ·
                refine ⟨929074095583030402167797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619382730388686934778531 929074095583030402167797)
                ·
                  refine ⟨87100696460909100203231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929074095583030402167797 87100696460909100203231)
                  ·
                    rfl

theorem cell21_381663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_381663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381663 prefixEnd_381663 := by exact prefixLift 381663
  have htrace : WordTrace (prefixWord ++ tailWord_381663) baseStart_381663 baseEnd_381663 := by
    simpa [prefixWord, tailWord_381663, baseEnd_381663] using wordTrace_append hprefix tailTrace_381663
  have hstable : (prefixWord ++ tailWord_381663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381663).length < 2 ^ (prefixWord ++ tailWord_381663).sum := by decide
  have hdescent : baseEnd_381663 < baseStart_381663 := by decide
  rcases family_descends (prefixWord ++ tailWord_381663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381722 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_381722 : Nat := 118140960795 + 381722 * 2 ^ 59
def prefixEnd_381722 : Nat := 4983230072969 + 3 ^ 40 * 381722 * 2
def baseEnd_381722 : Nat := 87114161064738108719777

theorem tailTrace_381722 : CollatzResearch.WordTrace tailWord_381722 prefixEnd_381722 87114161064738108719777 := by
  unfold tailWord_381722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480636280773465443108855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9281696748729241181623613 3480636280773465443108855)
  ·
    refine ⟨5220954421160198164663283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3480636280773465443108855 5220954421160198164663283)
    ·
      refine ⟨7831431631740297246994925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5220954421160198164663283 7831431631740297246994925)
      ·
        refine ⟨2936786861902611467623097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7831431631740297246994925 2936786861902611467623097)
        ·
          refine ⟨2202590146426958600717323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936786861902611467623097 2202590146426958600717323)
          ·
            refine ⟨3303885219640437901075985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202590146426958600717323 3303885219640437901075985)
            ·
              refine ⟨2477913914730328425806989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303885219640437901075985 2477913914730328425806989)
              ·
                refine ⟨929217718023873159677621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2477913914730328425806989 929217718023873159677621)
                ·
                  refine ⟨87114161064738108719777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929217718023873159677621 87114161064738108719777)
                  ·
                    rfl

theorem cell21_381722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_381722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381722 prefixEnd_381722 := by exact prefixLift 381722
  have htrace : WordTrace (prefixWord ++ tailWord_381722) baseStart_381722 baseEnd_381722 := by
    simpa [prefixWord, tailWord_381722, baseEnd_381722] using wordTrace_append hprefix tailTrace_381722
  have hstable : (prefixWord ++ tailWord_381722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381722).length < 2 ^ (prefixWord ++ tailWord_381722).sum := by decide
  have hdescent : baseEnd_381722 < baseStart_381722 := by decide
  rcases family_descends (prefixWord ++ tailWord_381722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381925 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 3]
def baseStart_381925 : Nat := 118140960795 + 381925 * 2 ^ 59
def prefixEnd_381925 : Nat := 4983230072969 + 3 ^ 40 * 381925 * 2
def baseEnd_381925 : Nat := 87160488430454866836029

theorem tailTrace_381925 : CollatzResearch.WordTrace tailWord_381925 prefixEnd_381925 87160488430454866836029 := by
  unfold tailWord_381925
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929949141358427442075229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9286632760905618294716819 13929949141358427442075229)
  ·
    refine ⟨5223730928009410290778211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13929949141358427442075229 5223730928009410290778211)
    ·
      refine ⟨7835596392014115436167317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5223730928009410290778211 7835596392014115436167317)
      ·
        refine ⟨367293580875661661070343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7835596392014115436167317 367293580875661661070343)
        ·
          refine ⟨550940371313492491605515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367293580875661661070343 550940371313492491605515)
          ·
            refine ⟨826410556970238737408273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550940371313492491605515 826410556970238737408273)
            ·
              refine ⟨619807917727679053056205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826410556970238737408273 619807917727679053056205)
              ·
                refine ⟨232427969147879644896077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619807917727679053056205 232427969147879644896077)
                ·
                  refine ⟨87160488430454866836029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232427969147879644896077 87160488430454866836029)
                  ·
                    rfl

theorem cell21_381925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_381925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381925 prefixEnd_381925 := by exact prefixLift 381925
  have htrace : WordTrace (prefixWord ++ tailWord_381925) baseStart_381925 baseEnd_381925 := by
    simpa [prefixWord, tailWord_381925, baseEnd_381925] using wordTrace_append hprefix tailTrace_381925
  have hstable : (prefixWord ++ tailWord_381925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381925).length < 2 ^ (prefixWord ++ tailWord_381925).sum := by decide
  have hdescent : baseEnd_381925 < baseStart_381925 := by decide
  rcases family_descends (prefixWord ++ tailWord_381925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381970 : List Nat := [3, 2, 5, 1, 1, 1, 1, 7]
def baseStart_381970 : Nat := 118140960795 + 381970 * 2 ^ 59
def prefixEnd_381970 : Nat := 4983230072969 + 3 ^ 40 * 381970 * 2
def baseEnd_381970 : Nat := 29056919347848262861979

theorem tailTrace_381970 : CollatzResearch.WordTrace tailWord_381970 prefixEnd_381970 29056919347848262861979 := by
  unfold tailWord_381970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482897606548850031865841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9287726950796933418308909 3482897606548850031865841)
  ·
    refine ⟨2612173204911637523899381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3482897606548850031865841 2612173204911637523899381)
    ·
      refine ⟨244891237960466017865567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2612173204911637523899381 244891237960466017865567)
      ·
        refine ⟨367336856940699026798351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244891237960466017865567 367336856940699026798351)
        ·
          refine ⟨551005285411048540197527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367336856940699026798351 551005285411048540197527)
          ·
            refine ⟨826507928116572810296291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551005285411048540197527 826507928116572810296291)
            ·
              refine ⟨1239761892174859215444437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826507928116572810296291 1239761892174859215444437)
              ·
                refine ⟨29056919347848262861979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1239761892174859215444437 29056919347848262861979)
                ·
                  rfl

theorem cell21_381970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_381970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_381970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_381970 prefixEnd_381970 := by exact prefixLift 381970
  have htrace : WordTrace (prefixWord ++ tailWord_381970) baseStart_381970 baseEnd_381970 := by
    simpa [prefixWord, tailWord_381970, baseEnd_381970] using wordTrace_append hprefix tailTrace_381970
  have hstable : (prefixWord ++ tailWord_381970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381970).length < 2 ^ (prefixWord ++ tailWord_381970).sum := by decide
  have hdescent : baseEnd_381970 < baseStart_381970 := by decide
  rcases family_descends (prefixWord ++ tailWord_381970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382057 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_382057 : Nat := 118140960795 + 382057 * 2 ^ 59
def prefixEnd_382057 : Nat := 4983230072969 + 3 ^ 40 * 382057 * 2
def baseEnd_382057 : Nat := 87190612628851970635759

theorem tailTrace_382057 : CollatzResearch.WordTrace tailWord_382057 prefixEnd_382057 87190612628851970635759 := by
  unfold tailWord_382057
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934763576880213985880425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9289842384586809323920283 13934763576880213985880425)
  ·
    refine ⟨10451072682660160489410319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13934763576880213985880425 10451072682660160489410319)
    ·
      refine ⟨15676609023990240734115479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10451072682660160489410319 15676609023990240734115479)
      ·
        refine ⟨23514913535985361101173219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676609023990240734115479 23514913535985361101173219)
        ·
          refine ⟨35272370303978041651759829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23514913535985361101173219 35272370303978041651759829)
          ·
            refine ⟨826696178999485351213121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35272370303978041651759829 826696178999485351213121)
            ·
              refine ⟨620022134249614013409841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826696178999485351213121 620022134249614013409841)
              ·
                refine ⟨465016600687210510057381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620022134249614013409841 465016600687210510057381)
                ·
                  refine ⟨87190612628851970635759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465016600687210510057381 87190612628851970635759)
                  ·
                    rfl

theorem cell21_382057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_382057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382057 prefixEnd_382057 := by exact prefixLift 382057
  have htrace : WordTrace (prefixWord ++ tailWord_382057) baseStart_382057 baseEnd_382057 := by
    simpa [prefixWord, tailWord_382057, baseEnd_382057] using wordTrace_append hprefix tailTrace_382057
  have hstable : (prefixWord ++ tailWord_382057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382057).length < 2 ^ (prefixWord ++ tailWord_382057).sum := by decide
  have hdescent : baseEnd_382057 < baseStart_382057 := by decide
  rcases family_descends (prefixWord ++ tailWord_382057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382119 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_382119 : Nat := 118140960795 + 382119 * 2 ^ 59
def prefixEnd_382119 : Nat := 4983230072969 + 3 ^ 40 * 382119 * 2
def baseEnd_382119 : Nat := 87204761873553640602299

theorem tailTrace_382119 : CollatzResearch.WordTrace tailWord_382119 prefixEnd_382119 87204761873553640602299 := by
  unfold tailWord_382119
  simp only [CollatzResearch.WordTrace]
  refine ⟨13937024902655598574637411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9291349935103732383091607 13937024902655598574637411)
  ·
    refine ⟨20905537353983397861956117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13937024902655598574637411 20905537353983397861956117)
    ·
      refine ⟨979947063467971774779193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20905537353983397861956117 979947063467971774779193)
      ·
        refine ⟨734960297600978831084395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 979947063467971774779193 734960297600978831084395)
        ·
          refine ⟨1102440446401468246626593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734960297600978831084395 1102440446401468246626593)
          ·
            refine ⟨826830334801101184969945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102440446401468246626593 826830334801101184969945)
            ·
              refine ⟨620122751100825888727459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826830334801101184969945 620122751100825888727459)
              ·
                refine ⟨930184126651238833091189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620122751100825888727459 930184126651238833091189)
                ·
                  refine ⟨87204761873553640602299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 930184126651238833091189 87204761873553640602299)
                  ·
                    rfl

theorem cell21_382119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_382119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382119 prefixEnd_382119 := by exact prefixLift 382119
  have htrace : WordTrace (prefixWord ++ tailWord_382119) baseStart_382119 baseEnd_382119 := by
    simpa [prefixWord, tailWord_382119, baseEnd_382119] using wordTrace_append hprefix tailTrace_382119
  have hstable : (prefixWord ++ tailWord_382119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382119).length < 2 ^ (prefixWord ++ tailWord_382119).sum := by decide
  have hdescent : baseEnd_382119 < baseStart_382119 := by decide
  rcases family_descends (prefixWord ++ tailWord_382119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382240 : List Nat := [2, 1, 1, 5, 3, 2, 1, 6]
def baseStart_382240 : Nat := 118140960795 + 382240 * 2 ^ 59
def prefixEnd_382240 : Nat := 4983230072969 + 3 ^ 40 * 382240 * 2
def baseEnd_382240 : Nat := 29077458574028106361795

theorem tailTrace_382240 : CollatzResearch.WordTrace tailWord_382240 prefixEnd_382240 29077458574028106361795 := by
  unfold tailWord_382240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970719067608618119896087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9294292090144824159861449 6970719067608618119896087)
  ·
    refine ⟨10456078601412927179844131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6970719067608618119896087 10456078601412927179844131)
    ·
      refine ⟨15684117902119390769766197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10456078601412927179844131 15684117902119390769766197)
      ·
        refine ⟨1470386053323692884665581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15684117902119390769766197 1470386053323692884665581)
        ·
          refine ⟨551394769996384831749593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1470386053323692884665581 551394769996384831749593)
          ·
            refine ⟨413546077497288623812195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551394769996384831749593 413546077497288623812195)
            ·
              refine ⟨620319116245932935718293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413546077497288623812195 620319116245932935718293)
              ·
                refine ⟨29077458574028106361795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 620319116245932935718293 29077458574028106361795)
                ·
                  rfl

theorem cell21_382240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_382240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382240 prefixEnd_382240 := by exact prefixLift 382240
  have htrace : WordTrace (prefixWord ++ tailWord_382240) baseStart_382240 baseEnd_382240 := by
    simpa [prefixWord, tailWord_382240, baseEnd_382240] using wordTrace_append hprefix tailTrace_382240
  have hstable : (prefixWord ++ tailWord_382240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382240).length < 2 ^ (prefixWord ++ tailWord_382240).sum := by decide
  have hdescent : baseEnd_382240 < baseStart_382240 := by decide
  rcases family_descends (prefixWord ++ tailWord_382240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382271 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 3]
def baseStart_382271 : Nat := 118140960795 + 382271 * 2 ^ 59
def prefixEnd_382271 : Nat := 4983230072969 + 3 ^ 40 * 382271 * 2
def baseEnd_382271 : Nat := 87239450344435154068655

theorem tailTrace_382271 : CollatzResearch.WordTrace tailWord_382271 prefixEnd_382271 87239450344435154068655 := by
  unfold tailWord_382271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942568798104928534170667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9295045865403285689447111 13942568798104928534170667)
  ·
    refine ⟨20913853197157392801256001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13942568798104928534170667 20913853197157392801256001)
    ·
      refine ⟨15685389897868044600942001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20913853197157392801256001 15685389897868044600942001)
      ·
        refine ⟨11764042423401033450706501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15685389897868044600942001 11764042423401033450706501)
        ·
          refine ⟨2205757954387693772007469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11764042423401033450706501 2205757954387693772007469)
          ·
            refine ⟨827159232895385164502801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2205757954387693772007469 827159232895385164502801)
            ·
              refine ⟨620369424671538873377101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827159232895385164502801 620369424671538873377101)
              ·
                refine ⟨232638534251827077516413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620369424671538873377101 232638534251827077516413)
                ·
                  refine ⟨87239450344435154068655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232638534251827077516413 87239450344435154068655)
                  ·
                    rfl

theorem cell21_382271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 3].length) (baseStart_382271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382271 prefixEnd_382271 := by exact prefixLift 382271
  have htrace : WordTrace (prefixWord ++ tailWord_382271) baseStart_382271 baseEnd_382271 := by
    simpa [prefixWord, tailWord_382271, baseEnd_382271] using wordTrace_append hprefix tailTrace_382271
  have hstable : (prefixWord ++ tailWord_382271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382271).length < 2 ^ (prefixWord ++ tailWord_382271).sum := by decide
  have hdescent : baseEnd_382271 < baseStart_382271 := by decide
  rcases family_descends (prefixWord ++ tailWord_382271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382316 : List Nat := [2, 2, 1, 1, 5, 3, 2, 5]
def baseStart_382316 : Nat := 118140960795 + 382316 * 2 ^ 59
def prefixEnd_382316 : Nat := 4983230072969 + 3 ^ 40 * 382316 * 2
def baseEnd_382316 : Nat := 29083239985841691939521

theorem tailTrace_382316 : CollatzResearch.WordTrace tailWord_382316 prefixEnd_382316 29083239985841691939521 := by
  unfold tailWord_382316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972105041470950609779401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9296140055294600813039201 6972105041470950609779401)
  ·
    refine ⟨5229078781103212957334551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6972105041470950609779401 5229078781103212957334551)
    ·
      refine ⟨7843618171654819436001827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229078781103212957334551 7843618171654819436001827)
      ·
        refine ⟨11765427257482229154002741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843618171654819436001827 11765427257482229154002741)
        ·
          refine ⟨1103008805388958983187757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11765427257482229154002741 1103008805388958983187757)
          ·
            refine ⟨413628302020859618695409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103008805388958983187757 413628302020859618695409)
            ·
              refine ⟨310221226515644714021557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413628302020859618695409 310221226515644714021557)
              ·
                refine ⟨29083239985841691939521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310221226515644714021557 29083239985841691939521)
                ·
                  rfl

theorem cell21_382316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_382316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382316 prefixEnd_382316 := by exact prefixLift 382316
  have htrace : WordTrace (prefixWord ++ tailWord_382316) baseStart_382316 baseEnd_382316 := by
    simpa [prefixWord, tailWord_382316, baseEnd_382316] using wordTrace_append hprefix tailTrace_382316
  have hstable : (prefixWord ++ tailWord_382316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382316).length < 2 ^ (prefixWord ++ tailWord_382316).sum := by decide
  have hdescent : baseEnd_382316 < baseStart_382316 := by decide
  rcases family_descends (prefixWord ++ tailWord_382316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382327 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_382327 : Nat := 118140960795 + 382327 * 2 ^ 59
def prefixEnd_382327 : Nat := 4983230072969 + 3 ^ 40 * 382327 * 2
def baseEnd_382327 : Nat := 87252230307391501135207

theorem tailTrace_382327 : CollatzResearch.WordTrace tailWord_382327 prefixEnd_382327 87252230307391501135207 := by
  unfold tailWord_382327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944611285902050098209235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9296407523934700065472823 13944611285902050098209235)
  ·
    refine ⟨20916916928853075147313853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13944611285902050098209235 20916916928853075147313853)
    ·
      refine ⟨7843843848319903180242695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20916916928853075147313853 7843843848319903180242695)
      ·
        refine ⟨11765765772479854770364043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843843848319903180242695 11765765772479854770364043)
        ·
          refine ⟨17648648658719782155546065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11765765772479854770364043 17648648658719782155546065)
          ·
            refine ⟨13236486494039836616659549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17648648658719782155546065 13236486494039836616659549)
            ·
              refine ⟨4963682435264938731247331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13236486494039836616659549 4963682435264938731247331)
              ·
                refine ⟨7445523652897408096870997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963682435264938731247331 7445523652897408096870997)
                ·
                  refine ⟨87252230307391501135207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7445523652897408096870997 87252230307391501135207)
                  ·
                    rfl

theorem cell21_382327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_382327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382327 prefixEnd_382327 := by exact prefixLift 382327
  have htrace : WordTrace (prefixWord ++ tailWord_382327) baseStart_382327 baseEnd_382327 := by
    simpa [prefixWord, tailWord_382327, baseEnd_382327] using wordTrace_append hprefix tailTrace_382327
  have hstable : (prefixWord ++ tailWord_382327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382327).length < 2 ^ (prefixWord ++ tailWord_382327).sum := by decide
  have hdescent : baseEnd_382327 < baseStart_382327 := by decide
  rcases family_descends (prefixWord ++ tailWord_382327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382344 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_382344 : Nat := 118140960795 + 382344 * 2 ^ 59
def prefixEnd_382344 : Nat := 4983230072969 + 3 ^ 40 * 382344 * 2
def baseEnd_382344 : Nat := 87256109939003249351839

theorem tailTrace_382344 : CollatzResearch.WordTrace tailWord_382344 prefixEnd_382344 87256109939003249351839 := by
  unfold tailWord_382344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972615663420231000789043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9296820884560308001052057 6972615663420231000789043)
  ·
    refine ⟨10458923495130346501183565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6972615663420231000789043 10458923495130346501183565)
    ·
      refine ⟨3922096310673879937943837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10458923495130346501183565 3922096310673879937943837)
      ·
        refine ⟨1470786116502704976728939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3922096310673879937943837 1470786116502704976728939)
        ·
          refine ⟨2206179174754057465093409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470786116502704976728939 2206179174754057465093409)
          ·
            refine ⟨1654634381065543098820057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206179174754057465093409 1654634381065543098820057)
            ·
              refine ⟨1240975785799157324115043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654634381065543098820057 1240975785799157324115043)
              ·
                refine ⟨1861463678698735986172565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240975785799157324115043 1861463678698735986172565)
                ·
                  refine ⟨87256109939003249351839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861463678698735986172565 87256109939003249351839)
                  ·
                    rfl

theorem cell21_382344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_382344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382344 prefixEnd_382344 := by exact prefixLift 382344
  have htrace : WordTrace (prefixWord ++ tailWord_382344) baseStart_382344 baseEnd_382344 := by
    simpa [prefixWord, tailWord_382344, baseEnd_382344] using wordTrace_append hprefix tailTrace_382344
  have hstable : (prefixWord ++ tailWord_382344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382344).length < 2 ^ (prefixWord ++ tailWord_382344).sum := by decide
  have hdescent : baseEnd_382344 < baseStart_382344 := by decide
  rcases family_descends (prefixWord ++ tailWord_382344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382347 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 3]
def baseStart_382347 : Nat := 118140960795 + 382347 * 2 ^ 59
def prefixEnd_382347 : Nat := 4983230072969 + 3 ^ 40 * 382347 * 2
def baseEnd_382347 : Nat := 87256794579875910801833

theorem tailTrace_382347 : CollatzResearch.WordTrace tailWord_382347 prefixEnd_382347 87256794579875910801833 := by
  unfold tailWord_382347
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945340745829593513937295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9296893830553062342624863 13945340745829593513937295)
  ·
    refine ⟨20918011118744390270905943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13945340745829593513937295 20918011118744390270905943)
    ·
      refine ⟨31377016678116585406358915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20918011118744390270905943 31377016678116585406358915)
      ·
        refine ⟨47065525017174878109538373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31377016678116585406358915 47065525017174878109538373)
        ·
          refine ⟨8824785940720289645538445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47065525017174878109538373 8824785940720289645538445)
          ·
            refine ⟨3309294727770108617076917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8824785940720289645538445 3309294727770108617076917)
            ·
              refine ⟨310246380728447682850961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3309294727770108617076917 310246380728447682850961)
              ·
                refine ⟨232684785546335762138221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310246380728447682850961 232684785546335762138221)
                ·
                  refine ⟨87256794579875910801833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232684785546335762138221 87256794579875910801833)
                  ·
                    rfl

theorem cell21_382347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3].length) (baseStart_382347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382347 prefixEnd_382347 := by exact prefixLift 382347
  have htrace : WordTrace (prefixWord ++ tailWord_382347) baseStart_382347 baseEnd_382347 := by
    simpa [prefixWord, tailWord_382347, baseEnd_382347] using wordTrace_append hprefix tailTrace_382347
  have hstable : (prefixWord ++ tailWord_382347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382347).length < 2 ^ (prefixWord ++ tailWord_382347).sum := by decide
  have hdescent : baseEnd_382347 < baseStart_382347 := by decide
  rcases family_descends (prefixWord ++ tailWord_382347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382361 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 4]
def baseStart_382361 : Nat := 118140960795 + 382361 * 2 ^ 59
def prefixEnd_382361 : Nat := 4983230072969 + 3 ^ 40 * 382361 * 2
def baseEnd_382361 : Nat := 87259989570614997568471

theorem tailTrace_382361 : CollatzResearch.WordTrace tailWord_382361 prefixEnd_382361 87259989570614997568471 := by
  unfold tailWord_382361
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945851367778873904946937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9297234245185915936631291 13945851367778873904946937)
  ·
    refine ⟨10459388525834155428710203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13945851367778873904946937 10459388525834155428710203)
    ·
      refine ⟨15689082788751233143065305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459388525834155428710203 15689082788751233143065305)
      ·
        refine ⟨11766812091563424857298979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15689082788751233143065305 11766812091563424857298979)
        ·
          refine ⟨17650218137345137285948469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11766812091563424857298979 17650218137345137285948469)
          ·
            refine ⟨1654707950376106620557669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17650218137345137285948469 1654707950376106620557669)
            ·
              refine ⟨310257740695519991354563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1654707950376106620557669 310257740695519991354563)
              ·
                refine ⟨465386611043279987031845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310257740695519991354563 465386611043279987031845)
                ·
                  refine ⟨87259989570614997568471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465386611043279987031845 87259989570614997568471)
                  ·
                    rfl

theorem cell21_382361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_382361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382361 prefixEnd_382361 := by exact prefixLift 382361
  have htrace : WordTrace (prefixWord ++ tailWord_382361) baseStart_382361 baseEnd_382361 := by
    simpa [prefixWord, tailWord_382361, baseEnd_382361] using wordTrace_append hprefix tailTrace_382361
  have hstable : (prefixWord ++ tailWord_382361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382361).length < 2 ^ (prefixWord ++ tailWord_382361).sum := by decide
  have hdescent : baseEnd_382361 < baseStart_382361 := by decide
  rcases family_descends (prefixWord ++ tailWord_382361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382403 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_382403 : Nat := 118140960795 + 382403 * 2 ^ 59
def prefixEnd_382403 : Nat := 4983230072969 + 3 ^ 40 * 382403 * 2
def baseEnd_382403 : Nat := 87269574542832257868385

theorem tailTrace_382403 : CollatzResearch.WordTrace tailWord_382403 prefixEnd_382403 87269574542832257868385 := by
  unfold tailWord_382403
  simp only [CollatzResearch.WordTrace]
  refine ⟨13947383233626715077975863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9298255489084476718650575 13947383233626715077975863)
  ·
    refine ⟨20921074850440072616963795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13947383233626715077975863 20921074850440072616963795)
    ·
      refine ⟨31381612275660108925445693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20921074850440072616963795 31381612275660108925445693)
      ·
        refine ⟨11768104603372540847042135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31381612275660108925445693 11768104603372540847042135)
        ·
          refine ⟨17652156905058811270563203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11768104603372540847042135 17652156905058811270563203)
          ·
            refine ⟨26478235357588216905844805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17652156905058811270563203 26478235357588216905844805)
            ·
              refine ⟨4964669129547790669845901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26478235357588216905844805 4964669129547790669845901)
              ·
                refine ⟨1861750923580421501192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4964669129547790669845901 1861750923580421501192213)
                ·
                  refine ⟨87269574542832257868385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1861750923580421501192213 87269574542832257868385)
                  ·
                    rfl

theorem cell21_382403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_382403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382403 prefixEnd_382403 := by exact prefixLift 382403
  have htrace : WordTrace (prefixWord ++ tailWord_382403) baseStart_382403 baseEnd_382403 := by
    simpa [prefixWord, tailWord_382403, baseEnd_382403] using wordTrace_append hprefix tailTrace_382403
  have hstable : (prefixWord ++ tailWord_382403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382403).length < 2 ^ (prefixWord ++ tailWord_382403).sum := by decide
  have hdescent : baseEnd_382403 < baseStart_382403 := by decide
  rcases family_descends (prefixWord ++ tailWord_382403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382454 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_382454 : Nat := 118140960795 + 382454 * 2 ^ 59
def prefixEnd_382454 : Nat := 4983230072969 + 3 ^ 40 * 382454 * 2
def baseEnd_382454 : Nat := 87281213437667502518281

theorem tailTrace_382454 : CollatzResearch.WordTrace tailWord_382454 prefixEnd_382454 87281213437667502518281 := by
  unfold tailWord_382454
  simp only [CollatzResearch.WordTrace]
  refine ⟨871827709777621924255151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9299495570961300525388277 871827709777621924255151)
  ·
    refine ⟨1307741564666432886382727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 871827709777621924255151 1307741564666432886382727)
    ·
      refine ⟨1961612346999649329574091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307741564666432886382727 1961612346999649329574091)
      ·
        refine ⟨2942418520499473994361137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961612346999649329574091 2942418520499473994361137)
        ·
          refine ⟨2206813890374605495770853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2942418520499473994361137 2206813890374605495770853)
          ·
            refine ⟨413777604445238530457035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2206813890374605495770853 413777604445238530457035)
            ·
              refine ⟨620666406667857795685553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413777604445238530457035 620666406667857795685553)
              ·
                refine ⟨465499805000893346764165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620666406667857795685553 465499805000893346764165)
                ·
                  refine ⟨87281213437667502518281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465499805000893346764165 87281213437667502518281)
                  ·
                    rfl

theorem cell21_382454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_382454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382454 prefixEnd_382454 := by exact prefixLift 382454
  have htrace : WordTrace (prefixWord ++ tailWord_382454) baseStart_382454 baseEnd_382454 := by
    simpa [prefixWord, tailWord_382454, baseEnd_382454] using wordTrace_append hprefix tailTrace_382454
  have hstable : (prefixWord ++ tailWord_382454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382454).length < 2 ^ (prefixWord ++ tailWord_382454).sum := by decide
  have hdescent : baseEnd_382454 < baseStart_382454 := by decide
  rcases family_descends (prefixWord ++ tailWord_382454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382496 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_382496 : Nat := 118140960795 + 382496 * 2 ^ 59
def prefixEnd_382496 : Nat := 4983230072969 + 3 ^ 40 * 382496 * 2
def baseEnd_382496 : Nat := 87290798409884762818195

theorem tailTrace_382496 : CollatzResearch.WordTrace tailWord_382496 prefixEnd_382496 87290798409884762818195 := by
  unfold tailWord_382496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975387611144895980555671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9300516814859861307407561 6975387611144895980555671)
  ·
    refine ⟨10463081416717343970833507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6975387611144895980555671 10463081416717343970833507)
    ·
      refine ⟨15694622125076015956250261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10463081416717343970833507 15694622125076015956250261)
      ·
        refine ⟨735685412112938247949231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15694622125076015956250261 735685412112938247949231)
        ·
          refine ⟨1103528118169407371923847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735685412112938247949231 1103528118169407371923847)
          ·
            refine ⟨1655292177254111057885771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103528118169407371923847 1655292177254111057885771)
            ·
              refine ⟨2482938265881166586828657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655292177254111057885771 2482938265881166586828657)
              ·
                refine ⟨1862203699410874940121493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2482938265881166586828657 1862203699410874940121493)
                ·
                  refine ⟨87290798409884762818195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1862203699410874940121493 87290798409884762818195)
                  ·
                    rfl

theorem cell21_382496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_382496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382496 prefixEnd_382496 := by exact prefixLift 382496
  have htrace : WordTrace (prefixWord ++ tailWord_382496) baseStart_382496 baseEnd_382496 := by
    simpa [prefixWord, tailWord_382496, baseEnd_382496] using wordTrace_append hprefix tailTrace_382496
  have hstable : (prefixWord ++ tailWord_382496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382496).length < 2 ^ (prefixWord ++ tailWord_382496).sum := by decide
  have hdescent : baseEnd_382496 < baseStart_382496 := by decide
  rcases family_descends (prefixWord ++ tailWord_382496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382623 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 4]
def baseStart_382623 : Nat := 118140960795 + 382623 * 2 ^ 59
def prefixEnd_382623 : Nat := 4983230072969 + 3 ^ 40 * 382623 * 2
def baseEnd_382623 : Nat := 87319781540160764201269

theorem tailTrace_382623 : CollatzResearch.WordTrace tailWord_382623 prefixEnd_382623 87319781540160764201269 := by
  unfold tailWord_382623
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955407292829692650984523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9303604861886461767323015 13955407292829692650984523)
  ·
    refine ⟨20933110939244538976476785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13955407292829692650984523 20933110939244538976476785)
    ·
      refine ⟨15699833204433404232357589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20933110939244538976476785 15699833204433404232357589)
      ·
        refine ⟨367964840728907911695881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15699833204433404232357589 367964840728907911695881)
        ·
          refine ⟨275973630546680933771911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367964840728907911695881 275973630546680933771911)
          ·
            refine ⟨413960445820021400657867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275973630546680933771911 413960445820021400657867)
            ·
              refine ⟨620940668730032100986801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413960445820021400657867 620940668730032100986801)
              ·
                refine ⟨465705501547524075740101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620940668730032100986801 465705501547524075740101)
                ·
                  refine ⟨87319781540160764201269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465705501547524075740101 87319781540160764201269)
                  ·
                    rfl

theorem cell21_382623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4].length) (baseStart_382623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382623 prefixEnd_382623 := by exact prefixLift 382623
  have htrace : WordTrace (prefixWord ++ tailWord_382623) baseStart_382623 baseEnd_382623 := by
    simpa [prefixWord, tailWord_382623, baseEnd_382623] using wordTrace_append hprefix tailTrace_382623
  have hstable : (prefixWord ++ tailWord_382623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382623).length < 2 ^ (prefixWord ++ tailWord_382623).sum := by decide
  have hdescent : baseEnd_382623 < baseStart_382623 := by decide
  rcases family_descends (prefixWord ++ tailWord_382623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382668 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_382668 : Nat := 118140960795 + 382668 * 2 ^ 59
def prefixEnd_382668 : Nat := 4983230072969 + 3 ^ 40 * 382668 * 2
def baseEnd_382668 : Nat := 87330051153250685951177

theorem tailTrace_382668 : CollatzResearch.WordTrace tailWord_382668 prefixEnd_382668 87330051153250685951177 := by
  unfold tailWord_382668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978524288833332668186329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9304699051777776890915105 6978524288833332668186329)
  ·
    refine ⟨5233893216624999501139747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6978524288833332668186329 5233893216624999501139747)
    ·
      refine ⟨7850839824937499251709621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233893216624999501139747 7850839824937499251709621)
      ·
        refine ⟨736016233587890554847777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7850839824937499251709621 736016233587890554847777)
        ·
          refine ⟨552012175190917916135833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736016233587890554847777 552012175190917916135833)
          ·
            refine ⟨414009131393188437101875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552012175190917916135833 414009131393188437101875)
            ·
              refine ⟨621013697089782655652813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414009131393188437101875 621013697089782655652813)
              ·
                refine ⟨232880136408668495869805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621013697089782655652813 232880136408668495869805)
                ·
                  refine ⟨87330051153250685951177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232880136408668495869805 87330051153250685951177)
                  ·
                    rfl

theorem cell21_382668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_382668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382668 prefixEnd_382668 := by exact prefixLift 382668
  have htrace : WordTrace (prefixWord ++ tailWord_382668) baseStart_382668 baseEnd_382668 := by
    simpa [prefixWord, tailWord_382668, baseEnd_382668] using wordTrace_append hprefix tailTrace_382668
  have hstable : (prefixWord ++ tailWord_382668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382668).length < 2 ^ (prefixWord ++ tailWord_382668).sum := by decide
  have hdescent : baseEnd_382668 < baseStart_382668 := by decide
  rcases family_descends (prefixWord ++ tailWord_382668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382685 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 3]
def baseStart_382685 : Nat := 118140960795 + 382685 * 2 ^ 59
def prefixEnd_382685 : Nat := 4983230072969 + 3 ^ 40 * 382685 * 2
def baseEnd_382685 : Nat := 87333930784862434167809

theorem tailTrace_382685 : CollatzResearch.WordTrace tailWord_382685 prefixEnd_382685 87333930784862434167809 := by
  unfold tailWord_382685
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957668618605077239741509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9305112412403384826494339 13957668618605077239741509)
  ·
    refine ⟨2617062865988451982451533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13957668618605077239741509 2617062865988451982451533)
    ·
      refine ⟨981398574745669493419325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2617062865988451982451533 981398574745669493419325)
      ·
        refine ⟨368024465529626060032247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 981398574745669493419325 368024465529626060032247)
        ·
          refine ⟨552036698294439090048371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368024465529626060032247 552036698294439090048371)
          ·
            refine ⟨828055047441658635072557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552036698294439090048371 828055047441658635072557)
            ·
              refine ⟨310520642790621988152209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828055047441658635072557 310520642790621988152209)
              ·
                refine ⟨232890482092966491114157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310520642790621988152209 232890482092966491114157)
                ·
                  refine ⟨87333930784862434167809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232890482092966491114157 87333930784862434167809)
                  ·
                    rfl

theorem cell21_382685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_382685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382685 prefixEnd_382685 := by exact prefixLift 382685
  have htrace : WordTrace (prefixWord ++ tailWord_382685) baseStart_382685 baseEnd_382685 := by
    simpa [prefixWord, tailWord_382685, baseEnd_382685] using wordTrace_append hprefix tailTrace_382685
  have hstable : (prefixWord ++ tailWord_382685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382685).length < 2 ^ (prefixWord ++ tailWord_382685).sum := by decide
  have hdescent : baseEnd_382685 < baseStart_382685 := by decide
  rcases family_descends (prefixWord ++ tailWord_382685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382769 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_382769 : Nat := 118140960795 + 382769 * 2 ^ 59
def prefixEnd_382769 : Nat := 4983230072969 + 3 ^ 40 * 382769 * 2
def baseEnd_382769 : Nat := 87353100729296954767637

theorem tailTrace_382769 : CollatzResearch.WordTrace tailWord_382769 prefixEnd_382769 87353100729296954767637 := by
  unfold tailWord_382769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960732350300759585799361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9307154900200506390532907 13960732350300759585799361)
  ·
    refine ⟨10470549262725569689349521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13960732350300759585799361 10470549262725569689349521)
    ·
      refine ⟨7852911947044177267012141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10470549262725569689349521 7852911947044177267012141)
      ·
        refine ⟨2944841980141566475129553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7852911947044177267012141 2944841980141566475129553)
        ·
          refine ⟨2208631485106174856347165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944841980141566475129553 2208631485106174856347165)
          ·
            refine ⟨828236806914815571130187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2208631485106174856347165 828236806914815571130187)
            ·
              refine ⟨1242355210372223356695281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828236806914815571130187 1242355210372223356695281)
              ·
                refine ⟨931766407779167517521461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242355210372223356695281 931766407779167517521461)
                ·
                  refine ⟨87353100729296954767637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931766407779167517521461 87353100729296954767637)
                  ·
                    rfl

theorem cell21_382769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_382769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382769 prefixEnd_382769 := by exact prefixLift 382769
  have htrace : WordTrace (prefixWord ++ tailWord_382769) baseStart_382769 baseEnd_382769 := by
    simpa [prefixWord, tailWord_382769, baseEnd_382769] using wordTrace_append hprefix tailTrace_382769
  have hstable : (prefixWord ++ tailWord_382769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382769).length < 2 ^ (prefixWord ++ tailWord_382769).sum := by decide
  have hdescent : baseEnd_382769 < baseStart_382769 := by decide
  rcases family_descends (prefixWord ++ tailWord_382769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382772 : List Nat := [2, 5, 1, 1, 2, 2, 3, 5]
def baseStart_382772 : Nat := 118140960795 + 382772 * 2 ^ 59
def prefixEnd_382772 : Nat := 4983230072969 + 3 ^ 40 * 382772 * 2
def baseEnd_382772 : Nat := 29117928456723205405877

theorem tailTrace_382772 : CollatzResearch.WordTrace tailWord_382772 prefixEnd_382772 29117928456723205405877 := by
  unfold tailWord_382772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980420884644945549079285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9307227846193260732105713 6980420884644945549079285)
  ·
    refine ⟨654414457935463645226183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6980420884644945549079285 654414457935463645226183)
    ·
      refine ⟨981621686903195467839275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654414457935463645226183 981621686903195467839275)
      ·
        refine ⟨1472432530354793201758913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981621686903195467839275 1472432530354793201758913)
        ·
          refine ⟨1104324397766094901319185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472432530354793201758913 1104324397766094901319185)
          ·
            refine ⟨828243298324571175989389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104324397766094901319185 828243298324571175989389)
            ·
              refine ⟨310591236871714190996021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828243298324571175989389 310591236871714190996021)
              ·
                refine ⟨29117928456723205405877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310591236871714190996021 29117928456723205405877)
                ·
                  rfl

theorem cell21_382772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_382772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382772 prefixEnd_382772 := by exact prefixLift 382772
  have htrace : WordTrace (prefixWord ++ tailWord_382772) baseStart_382772 baseEnd_382772 := by
    simpa [prefixWord, tailWord_382772, baseEnd_382772] using wordTrace_append hprefix tailTrace_382772
  have hstable : (prefixWord ++ tailWord_382772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382772).length < 2 ^ (prefixWord ++ tailWord_382772).sum := by decide
  have hdescent : baseEnd_382772 < baseStart_382772 := by decide
  rcases family_descends (prefixWord ++ tailWord_382772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382859 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_382859 : Nat := 118140960795 + 382859 * 2 ^ 59
def prefixEnd_382859 : Nat := 4983230072969 + 3 ^ 40 * 382859 * 2
def baseEnd_382859 : Nat := 87373639955476798267453

theorem tailTrace_382859 : CollatzResearch.WordTrace tailWord_382859 prefixEnd_382859 87373639955476798267453 := by
  unfold tailWord_382859
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964014919974704956575631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9309343279983136637717087 13964014919974704956575631)
  ·
    refine ⟨20946022379962057434863447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964014919974704956575631 20946022379962057434863447)
    ·
      refine ⟨31419033569943086152295171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20946022379962057434863447 31419033569943086152295171)
      ·
        refine ⟨47128550354914629228442757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31419033569943086152295171 47128550354914629228442757)
        ·
          refine ⟨8836603191546492980333017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47128550354914629228442757 8836603191546492980333017)
          ·
            refine ⟨6627452393659869735249763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8836603191546492980333017 6627452393659869735249763)
            ·
              refine ⟨9941178590489804602874645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627452393659869735249763 9941178590489804602874645)
              ·
                refine ⟨465992746429209590759749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9941178590489804602874645 465992746429209590759749)
                ·
                  refine ⟨87373639955476798267453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465992746429209590759749 87373639955476798267453)
                  ·
                    rfl

theorem cell21_382859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_382859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382859 prefixEnd_382859 := by exact prefixLift 382859
  have htrace : WordTrace (prefixWord ++ tailWord_382859) baseStart_382859 baseEnd_382859 := by
    simpa [prefixWord, tailWord_382859, baseEnd_382859] using wordTrace_append hprefix tailTrace_382859
  have hstable : (prefixWord ++ tailWord_382859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382859).length < 2 ^ (prefixWord ++ tailWord_382859).sum := by decide
  have hdescent : baseEnd_382859 < baseStart_382859 := by decide
  rcases family_descends (prefixWord ++ tailWord_382859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382873 : List Nat := [1, 2, 1, 2, 1, 3, 3, 8]
def baseStart_382873 : Nat := 118140960795 + 382873 * 2 ^ 59
def prefixEnd_382873 : Nat := 4983230072969 + 3 ^ 40 * 382873 * 2
def baseEnd_382873 : Nat := 29125611648738628344697

theorem tailTrace_382873 : CollatzResearch.WordTrace tailWord_382873 prefixEnd_382873 29125611648738628344697 := by
  unfold tailWord_382873
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964525541923985347585273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9309683694615990231723515 13964525541923985347585273)
  ·
    refine ⟨10473394156442989010688955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13964525541923985347585273 10473394156442989010688955)
    ·
      refine ⟨15710091234664483516033433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10473394156442989010688955 15710091234664483516033433)
      ·
        refine ⟨11782568425998362637025075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15710091234664483516033433 11782568425998362637025075)
        ·
          refine ⟨17673852638997543955537613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11782568425998362637025075 17673852638997543955537613)
          ·
            refine ⟨6627694739624078983326605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17673852638997543955537613 6627694739624078983326605)
            ·
              refine ⟨2485385527359029618747477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6627694739624078983326605 2485385527359029618747477)
              ·
                refine ⟨29125611648738628344697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2485385527359029618747477 29125611648738628344697)
                ·
                  rfl

theorem cell21_382873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_382873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382873 prefixEnd_382873 := by exact prefixLift 382873
  have htrace : WordTrace (prefixWord ++ tailWord_382873) baseStart_382873 baseEnd_382873 := by
    simpa [prefixWord, tailWord_382873, baseEnd_382873] using wordTrace_append hprefix tailTrace_382873
  have hstable : (prefixWord ++ tailWord_382873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382873).length < 2 ^ (prefixWord ++ tailWord_382873).sum := by decide
  have hdescent : baseEnd_382873 < baseStart_382873 := by decide
  rcases family_descends (prefixWord ++ tailWord_382873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382921 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 3]
def baseStart_382921 : Nat := 118140960795 + 382921 * 2 ^ 59
def prefixEnd_382921 : Nat := 4983230072969 + 3 ^ 40 * 382921 * 2
def baseEnd_382921 : Nat := 87387789200178468233993

theorem tailTrace_382921 : CollatzResearch.WordTrace tailWord_382921 prefixEnd_382921 87387789200178468233993 := by
  unfold tailWord_382921
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966276245750089545332617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9310850830500059696888411 13966276245750089545332617)
  ·
    refine ⟨10474707184312567158999463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13966276245750089545332617 10474707184312567158999463)
    ·
      refine ⟨15712060776468850738499195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10474707184312567158999463 15712060776468850738499195)
      ·
        refine ⟨23568091164703276107748793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15712060776468850738499195 23568091164703276107748793)
        ·
          refine ⟨17676068373527457080811595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23568091164703276107748793 17676068373527457080811595)
          ·
            refine ⟨26514102560291185621217393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676068373527457080811595 26514102560291185621217393)
            ·
              refine ⟨19885576920218389215913045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26514102560291185621217393 19885576920218389215913045)
              ·
                refine ⟨233034104533809248623981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19885576920218389215913045 233034104533809248623981)
                ·
                  refine ⟨87387789200178468233993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233034104533809248623981 87387789200178468233993)
                  ·
                    rfl

theorem cell21_382921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_382921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382921 prefixEnd_382921 := by exact prefixLift 382921
  have htrace : WordTrace (prefixWord ++ tailWord_382921) baseStart_382921 baseEnd_382921 := by
    simpa [prefixWord, tailWord_382921, baseEnd_382921] using wordTrace_append hprefix tailTrace_382921
  have hstable : (prefixWord ++ tailWord_382921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382921).length < 2 ^ (prefixWord ++ tailWord_382921).sum := by decide
  have hdescent : baseEnd_382921 < baseStart_382921 := by decide
  rcases family_descends (prefixWord ++ tailWord_382921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382935 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_382935 : Nat := 118140960795 + 382935 * 2 ^ 59
def prefixEnd_382935 : Nat := 4983230072969 + 3 ^ 40 * 382935 * 2
def baseEnd_382935 : Nat := 87390984190917555000631

theorem tailTrace_382935 : CollatzResearch.WordTrace tailWord_382935 prefixEnd_382935 87390984190917555000631 := by
  unfold tailWord_382935
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966786867699369936342259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9311191245132913290894839 13966786867699369936342259)
  ·
    refine ⟨20950180301549054904513389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13966786867699369936342259 20950180301549054904513389)
    ·
      refine ⟨7856317613080895589192521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20950180301549054904513389 7856317613080895589192521)
      ·
        refine ⟨5892238209810671691894391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7856317613080895589192521 5892238209810671691894391)
        ·
          refine ⟨8838357314716007537841587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892238209810671691894391 8838357314716007537841587)
          ·
            refine ⟨13257535972074011306762381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838357314716007537841587 13257535972074011306762381)
            ·
              refine ⟨4971575989527754240035893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13257535972074011306762381 4971575989527754240035893)
              ·
                refine ⟨466085249018226960003365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4971575989527754240035893 466085249018226960003365)
                ·
                  refine ⟨87390984190917555000631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466085249018226960003365 87390984190917555000631)
                  ·
                    rfl

theorem cell21_382935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_382935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_382935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_382935 prefixEnd_382935 := by exact prefixLift 382935
  have htrace : WordTrace (prefixWord ++ tailWord_382935) baseStart_382935 baseEnd_382935 := by
    simpa [prefixWord, tailWord_382935, baseEnd_382935] using wordTrace_append hprefix tailTrace_382935
  have hstable : (prefixWord ++ tailWord_382935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382935).length < 2 ^ (prefixWord ++ tailWord_382935).sum := by decide
  have hdescent : baseEnd_382935 < baseStart_382935 := by decide
  rcases family_descends (prefixWord ++ tailWord_382935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383025 : List Nat := [1, 2, 2, 3, 1, 3, 9]
def baseStart_383025 : Nat := 118140960795 + 383025 * 2 ^ 59
def prefixEnd_383025 : Nat := 4983230072969 + 3 ^ 40 * 383025 * 2
def baseEnd_383025 : Nat := 9712391490788599833383

theorem tailTrace_383025 : CollatzResearch.WordTrace tailWord_383025 prefixEnd_383025 9712391490788599833383 := by
  unfold tailWord_383025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970069437373315307118529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9313379624915543538079019 13970069437373315307118529)
  ·
    refine ⟨10477552078029986480338897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13970069437373315307118529 10477552078029986480338897)
    ·
      refine ⟨7858164058522489860254173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10477552078029986480338897 7858164058522489860254173)
      ·
        refine ⟨2946811521945933697595315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7858164058522489860254173 2946811521945933697595315)
        ·
          refine ⟨4420217282918900546392973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946811521945933697595315 4420217282918900546392973)
          ·
            refine ⟨1657581481094587704897365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4420217282918900546392973 1657581481094587704897365)
            ·
              refine ⟨9712391490788599833383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1657581481094587704897365 9712391490788599833383)
              ·
                rfl

theorem cell21_383025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 9].length) (baseStart_383025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383025 prefixEnd_383025 := by exact prefixLift 383025
  have htrace : WordTrace (prefixWord ++ tailWord_383025) baseStart_383025 baseEnd_383025 := by
    simpa [prefixWord, tailWord_383025, baseEnd_383025] using wordTrace_append hprefix tailTrace_383025
  have hstable : (prefixWord ++ tailWord_383025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383025).length < 2 ^ (prefixWord ++ tailWord_383025).sum := by decide
  have hdescent : baseEnd_383025 < baseStart_383025 := by decide
  rcases family_descends (prefixWord ++ tailWord_383025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383073 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 3]
def baseStart_383073 : Nat := 118140960795 + 383073 * 2 ^ 59
def prefixEnd_383073 : Nat := 4983230072969 + 3 ^ 40 * 383073 * 2
def baseEnd_383073 : Nat := 87422477671059981700349

theorem tailTrace_383073 : CollatzResearch.WordTrace tailWord_383073 prefixEnd_383073 87422477671059981700349 := by
  unfold tailWord_383073
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971820141199419504865873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9314546760799613003243915 13971820141199419504865873)
  ·
    refine ⟨10478865105899564628649405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13971820141199419504865873 10478865105899564628649405)
    ·
      refine ⟨3929574414712336735743527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10478865105899564628649405 3929574414712336735743527)
      ·
        refine ⟨5894361622068505103615291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929574414712336735743527 5894361622068505103615291)
        ·
          refine ⟨8841542433102757655422937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894361622068505103615291 8841542433102757655422937)
          ·
            refine ⟨6631156824827068241567203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8841542433102757655422937 6631156824827068241567203)
            ·
              refine ⟨9946735237240602362350805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631156824827068241567203 9946735237240602362350805)
              ·
                refine ⟨233126607122826617867597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9946735237240602362350805 233126607122826617867597)
                ·
                  refine ⟨87422477671059981700349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233126607122826617867597 87422477671059981700349)
                  ·
                    rfl

theorem cell21_383073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_383073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383073 prefixEnd_383073 := by exact prefixLift 383073
  have htrace : WordTrace (prefixWord ++ tailWord_383073) baseStart_383073 baseEnd_383073 := by
    simpa [prefixWord, tailWord_383073, baseEnd_383073] using wordTrace_append hprefix tailTrace_383073
  have hstable : (prefixWord ++ tailWord_383073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383073).length < 2 ^ (prefixWord ++ tailWord_383073).sum := by decide
  have hdescent : baseEnd_383073 < baseStart_383073 := by decide
  rcases family_descends (prefixWord ++ tailWord_383073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383087 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_383087 : Nat := 118140960795 + 383087 * 2 ^ 59
def prefixEnd_383087 : Nat := 4983230072969 + 3 ^ 40 * 383087 * 2
def baseEnd_383087 : Nat := 87425672661799068466987

theorem tailTrace_383087 : CollatzResearch.WordTrace tailWord_383087 prefixEnd_383087 87425672661799068466987 := by
  unfold tailWord_383087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972330763148699895875515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9314887175432466597250343 13972330763148699895875515)
  ·
    refine ⟨20958496144723049843813273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13972330763148699895875515 20958496144723049843813273)
    ·
      refine ⟨15718872108542287382859955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20958496144723049843813273 15718872108542287382859955)
      ·
        refine ⟨23578308162813431074289933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15718872108542287382859955 23578308162813431074289933)
        ·
          refine ⟨8841865561055036652858725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23578308162813431074289933 8841865561055036652858725)
          ·
            refine ⟨1657849792697819372411011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8841865561055036652858725 1657849792697819372411011)
            ·
              refine ⟨2486774689046729058616517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657849792697819372411011 2486774689046729058616517)
              ·
                refine ⟨466270254196261698490597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2486774689046729058616517 466270254196261698490597)
                ·
                  refine ⟨87425672661799068466987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466270254196261698490597 87425672661799068466987)
                  ·
                    rfl

theorem cell21_383087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_383087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383087 prefixEnd_383087 := by exact prefixLift 383087
  have htrace : WordTrace (prefixWord ++ tailWord_383087) baseStart_383087 baseEnd_383087 := by
    simpa [prefixWord, tailWord_383087, baseEnd_383087] using wordTrace_append hprefix tailTrace_383087
  have hstable : (prefixWord ++ tailWord_383087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383087).length < 2 ^ (prefixWord ++ tailWord_383087).sum := by decide
  have hdescent : baseEnd_383087 < baseStart_383087 := by decide
  rcases family_descends (prefixWord ++ tailWord_383087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383090 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_383090 : Nat := 118140960795 + 383090 * 2 ^ 59
def prefixEnd_383090 : Nat := 4983230072969 + 3 ^ 40 * 383090 * 2
def baseEnd_383090 : Nat := 87426357302671729916981

theorem tailTrace_383090 : CollatzResearch.WordTrace tailWord_383090 prefixEnd_383090 87426357302671729916981 := by
  unfold tailWord_383090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493110045534457852058681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9314960121425220938823149 3493110045534457852058681)
  ·
    refine ⟨2619832534150843389044011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3493110045534457852058681 2619832534150843389044011)
    ·
      refine ⟨3929748801226265083566017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619832534150843389044011 3929748801226265083566017)
      ·
        refine ⟨2947311600919698812674513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3929748801226265083566017 2947311600919698812674513)
        ·
          refine ⟨2210483700689774109505885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947311600919698812674513 2210483700689774109505885)
          ·
            refine ⟨828931387758665291064707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2210483700689774109505885 828931387758665291064707)
            ·
              refine ⟨1243397081637997936597061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828931387758665291064707 1243397081637997936597061)
              ·
                refine ⟨233136952807124613111949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1243397081637997936597061 233136952807124613111949)
                ·
                  refine ⟨87426357302671729916981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233136952807124613111949 87426357302671729916981)
                  ·
                    rfl

theorem cell21_383090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_383090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383090 prefixEnd_383090 := by exact prefixLift 383090
  have htrace : WordTrace (prefixWord ++ tailWord_383090) baseStart_383090 baseEnd_383090 := by
    simpa [prefixWord, tailWord_383090, baseEnd_383090] using wordTrace_append hprefix tailTrace_383090
  have hstable : (prefixWord ++ tailWord_383090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383090).length < 2 ^ (prefixWord ++ tailWord_383090).sum := by decide
  have hdescent : baseEnd_383090 < baseStart_383090 := by decide
  rcases family_descends (prefixWord ++ tailWord_383090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383124 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_383124 : Nat := 118140960795 + 383124 * 2 ^ 59
def prefixEnd_383124 : Nat := 4983230072969 + 3 ^ 40 * 383124 * 2
def baseEnd_383124 : Nat := 87434116565895226350245

theorem tailTrace_383124 : CollatzResearch.WordTrace tailWord_383124 prefixEnd_383124 87434116565895226350245 := by
  unfold tailWord_383124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986840132007327607486213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9315786842676436809981617 6986840132007327607486213)
  ·
    refine ⟨1310032524751373926403665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6986840132007327607486213 1310032524751373926403665)
    ·
      refine ⟨982524393563530444802749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310032524751373926403665 982524393563530444802749)
      ·
        refine ⟨368446647586323916801031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 982524393563530444802749 368446647586323916801031)
        ·
          refine ⟨552669971379485875201547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368446647586323916801031 552669971379485875201547)
          ·
            refine ⟨829004957069228812802321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552669971379485875201547 829004957069228812802321)
            ·
              refine ⟨621753717801921609601741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829004957069228812802321 621753717801921609601741)
              ·
                refine ⟨233157644175720603600653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621753717801921609601741 233157644175720603600653)
                ·
                  refine ⟨87434116565895226350245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233157644175720603600653 87434116565895226350245)
                  ·
                    rfl

theorem cell21_383124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_383124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383124 prefixEnd_383124 := by exact prefixLift 383124
  have htrace : WordTrace (prefixWord ++ tailWord_383124) baseStart_383124 baseEnd_383124 := by
    simpa [prefixWord, tailWord_383124, baseEnd_383124] using wordTrace_append hprefix tailTrace_383124
  have hstable : (prefixWord ++ tailWord_383124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383124).length < 2 ^ (prefixWord ++ tailWord_383124).sum := by decide
  have hdescent : baseEnd_383124 < baseStart_383124 := by decide
  rcases family_descends (prefixWord ++ tailWord_383124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383132 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_383132 : Nat := 118140960795 + 383132 * 2 ^ 59
def prefixEnd_383132 : Nat := 4983230072969 + 3 ^ 40 * 383132 * 2
def baseEnd_383132 : Nat := 87435942274888990216895

theorem tailTrace_383132 : CollatzResearch.WordTrace tailWord_383132 prefixEnd_383132 87435942274888990216895 := by
  unfold tailWord_383132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986986023992836290631825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9315981365323781720842433 6986986023992836290631825)
  ·
    refine ⟨5240239517994627217973869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6986986023992836290631825 5240239517994627217973869)
    ·
      refine ⟨1965089819247985206740201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5240239517994627217973869 1965089819247985206740201)
      ·
        refine ⟨1473817364435988905055151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1965089819247985206740201 1473817364435988905055151)
        ·
          refine ⟨2210726046653983357582727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473817364435988905055151 2210726046653983357582727)
          ·
            refine ⟨3316089069980975036374091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210726046653983357582727 3316089069980975036374091)
            ·
              refine ⟨4974133604971462554561137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316089069980975036374091 4974133604971462554561137)
              ·
                refine ⟨3730600203728596915920853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974133604971462554561137 3730600203728596915920853)
                ·
                  refine ⟨87435942274888990216895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3730600203728596915920853 87435942274888990216895)
                  ·
                    rfl

theorem cell21_383132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_383132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383132 prefixEnd_383132 := by exact prefixLift 383132
  have htrace : WordTrace (prefixWord ++ tailWord_383132) baseStart_383132 baseEnd_383132 := by
    simpa [prefixWord, tailWord_383132, baseEnd_383132] using wordTrace_append hprefix tailTrace_383132
  have hstable : (prefixWord ++ tailWord_383132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383132).length < 2 ^ (prefixWord ++ tailWord_383132).sum := by decide
  have hdescent : baseEnd_383132 < baseStart_383132 := by decide
  rcases family_descends (prefixWord ++ tailWord_383132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383149 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_383149 : Nat := 118140960795 + 383149 * 2 ^ 59
def prefixEnd_383149 : Nat := 4983230072969 + 3 ^ 40 * 383149 * 2
def baseEnd_383149 : Nat := 87439821906500738433527

theorem tailTrace_383149 : CollatzResearch.WordTrace tailWord_383149 prefixEnd_383149 87439821906500738433527 := by
  unfold tailWord_383149
  simp only [CollatzResearch.WordTrace]
  refine ⟨13974592088924084484632501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9316394725949389656421667 13974592088924084484632501)
  ·
    refine ⟨1310118008336632920434297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13974592088924084484632501 1310118008336632920434297)
    ·
      refine ⟨982588506252474690325723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310118008336632920434297 982588506252474690325723)
      ·
        refine ⟨1473882759378712035488585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982588506252474690325723 1473882759378712035488585)
        ·
          refine ⟨1105412069534034026616439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473882759378712035488585 1105412069534034026616439)
          ·
            refine ⟨1658118104301051039924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105412069534034026616439 1658118104301051039924659)
            ·
              refine ⟨2487177156451576559886989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658118104301051039924659 2487177156451576559886989)
              ·
                refine ⟨932691433669341209957621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2487177156451576559886989 932691433669341209957621)
                ·
                  refine ⟨87439821906500738433527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 932691433669341209957621 87439821906500738433527)
                  ·
                    rfl

theorem cell21_383149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_383149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383149 prefixEnd_383149 := by exact prefixLift 383149
  have htrace : WordTrace (prefixWord ++ tailWord_383149) baseStart_383149 baseEnd_383149 := by
    simpa [prefixWord, tailWord_383149, baseEnd_383149] using wordTrace_append hprefix tailTrace_383149
  have hstable : (prefixWord ++ tailWord_383149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383149).length < 2 ^ (prefixWord ++ tailWord_383149).sum := by decide
  have hdescent : baseEnd_383149 < baseStart_383149 := by decide
  rcases family_descends (prefixWord ++ tailWord_383149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383169 : List Nat := [1, 2, 6, 1, 3, 1, 2, 5]
def baseStart_383169 : Nat := 118140960795 + 383169 * 2 ^ 59
def prefixEnd_383169 : Nat := 4983230072969 + 3 ^ 40 * 383169 * 2
def baseEnd_383169 : Nat := 29148128726328382700051

theorem tailTrace_383169 : CollatzResearch.WordTrace tailWord_383169 prefixEnd_383169 29148128726328382700051 := by
  unfold tailWord_383169
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975321548851627900360561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9316881032567751933573707 13975321548851627900360561)
  ·
    refine ⟨10481491161638720925270421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13975321548851627900360561 10481491161638720925270421)
    ·
      refine ⟨491319898201815043372051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10481491161638720925270421 491319898201815043372051)
      ·
        refine ⟨736979847302722565058077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491319898201815043372051 736979847302722565058077)
        ·
          refine ⟨276367442738520961896779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736979847302722565058077 276367442738520961896779)
          ·
            refine ⟨414551164107781442845169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276367442738520961896779 414551164107781442845169)
            ·
              refine ⟨310913373080836082133877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414551164107781442845169 310913373080836082133877)
              ·
                refine ⟨29148128726328382700051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310913373080836082133877 29148128726328382700051)
                ·
                  rfl

theorem cell21_383169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 5].length) (baseStart_383169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383169 prefixEnd_383169 := by exact prefixLift 383169
  have htrace : WordTrace (prefixWord ++ tailWord_383169) baseStart_383169 baseEnd_383169 := by
    simpa [prefixWord, tailWord_383169, baseEnd_383169] using wordTrace_append hprefix tailTrace_383169
  have hstable : (prefixWord ++ tailWord_383169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383169).length < 2 ^ (prefixWord ++ tailWord_383169).sum := by decide
  have hdescent : baseEnd_383169 < baseStart_383169 := by decide
  rcases family_descends (prefixWord ++ tailWord_383169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383332 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_383332 : Nat := 118140960795 + 383332 * 2 ^ 59
def prefixEnd_383332 : Nat := 4983230072969 + 3 ^ 40 * 383332 * 2
def baseEnd_383332 : Nat := 87481584999733086883153

theorem tailTrace_383332 : CollatzResearch.WordTrace tailWord_383332 prefixEnd_383332 87481584999733086883153 := by
  unfold tailWord_383332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6990633323630553369272125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9320844431507404492362833 6990633323630553369272125)
  ·
    refine ⟨2621487496361457513477047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6990633323630553369272125 2621487496361457513477047)
    ·
      refine ⟨3932231244542186270215571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621487496361457513477047 3932231244542186270215571)
      ·
        refine ⟨5898346866813279405323357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932231244542186270215571 5898346866813279405323357)
        ·
          refine ⟨2211880075054979776996259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5898346866813279405323357 2211880075054979776996259)
          ·
            refine ⟨3317820112582469665494389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211880075054979776996259 3317820112582469665494389)
            ·
              refine ⟨311045635554606531140099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3317820112582469665494389 311045635554606531140099)
              ·
                refine ⟨466568453331909796710149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311045635554606531140099 466568453331909796710149)
                ·
                  refine ⟨87481584999733086883153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466568453331909796710149 87481584999733086883153)
                  ·
                    rfl

theorem cell21_383332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_383332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383332 prefixEnd_383332 := by exact prefixLift 383332
  have htrace : WordTrace (prefixWord ++ tailWord_383332) baseStart_383332 baseEnd_383332 := by
    simpa [prefixWord, tailWord_383332, baseEnd_383332] using wordTrace_append hprefix tailTrace_383332
  have hstable : (prefixWord ++ tailWord_383332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383332).length < 2 ^ (prefixWord ++ tailWord_383332).sum := by decide
  have hdescent : baseEnd_383332 < baseStart_383332 := by decide
  rcases family_descends (prefixWord ++ tailWord_383332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383343 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_383343 : Nat := 118140960795 + 383343 * 2 ^ 59
def prefixEnd_383343 : Nat := 4983230072969 + 3 ^ 40 * 383343 * 2
def baseEnd_383343 : Nat := 87484095349599512199797

theorem tailTrace_383343 : CollatzResearch.WordTrace tailWord_383343 prefixEnd_383343 87484095349599512199797 := by
  unfold tailWord_383343
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981667850221255617194683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321111900147503744796455 13981667850221255617194683)
  ·
    refine ⟨20972501775331883425792025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13981667850221255617194683 20972501775331883425792025)
    ·
      refine ⟨15729376331498912569344019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20972501775331883425792025 15729376331498912569344019)
      ·
        refine ⟨23594064497248368854016029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15729376331498912569344019 23594064497248368854016029)
        ·
          refine ⟨8847774186468138320256011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23594064497248368854016029 8847774186468138320256011)
          ·
            refine ⟨13271661279702207480384017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847774186468138320256011 13271661279702207480384017)
            ·
              refine ⟨9953745959776655610288013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13271661279702207480384017 9953745959776655610288013)
              ·
                refine ⟨3732654734916245853858005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9953745959776655610288013 3732654734916245853858005)
                ·
                  refine ⟨87484095349599512199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3732654734916245853858005 87484095349599512199797)
                  ·
                    rfl

theorem cell21_383343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_383343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383343 prefixEnd_383343 := by exact prefixLift 383343
  have htrace : WordTrace (prefixWord ++ tailWord_383343) baseStart_383343 baseEnd_383343 := by
    simpa [prefixWord, tailWord_383343, baseEnd_383343] using wordTrace_append hprefix tailTrace_383343
  have hstable : (prefixWord ++ tailWord_383343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383343).length < 2 ^ (prefixWord ++ tailWord_383343).sum := by decide
  have hdescent : baseEnd_383343 < baseStart_383343 := by decide
  rcases family_descends (prefixWord ++ tailWord_383343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383346 : List Nat := [3, 2, 1, 2, 1, 3, 4, 5]
def baseStart_383346 : Nat := 118140960795 + 383346 * 2 ^ 59
def prefixEnd_383346 : Nat := 4983230072969 + 3 ^ 40 * 383346 * 2
def baseEnd_383346 : Nat := 29161593330157391216597

theorem tailTrace_383346 : CollatzResearch.WordTrace tailWord_383346 prefixEnd_383346 29161593330157391216597 := by
  unfold tailWord_383346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495444317302596782388473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9321184846140258086369261 3495444317302596782388473)
  ·
    refine ⟨2621583237976947586791355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3495444317302596782388473 2621583237976947586791355)
    ·
      refine ⟨3932374856965421380187033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621583237976947586791355 3932374856965421380187033)
      ·
        refine ⟨2949281142724066035140275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3932374856965421380187033 2949281142724066035140275)
        ·
          refine ⟨4423921714086099052710413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949281142724066035140275 4423921714086099052710413)
          ·
            refine ⟨1658970642782287144766405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4423921714086099052710413 1658970642782287144766405)
            ·
              refine ⟨311056995521678839643701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1658970642782287144766405 311056995521678839643701)
              ·
                refine ⟨29161593330157391216597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311056995521678839643701 29161593330157391216597)
                ·
                  rfl

theorem cell21_383346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_383346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383346 prefixEnd_383346 := by exact prefixLift 383346
  have htrace : WordTrace (prefixWord ++ tailWord_383346) baseStart_383346 baseEnd_383346 := by
    simpa [prefixWord, tailWord_383346, baseEnd_383346] using wordTrace_append hprefix tailTrace_383346
  have hstable : (prefixWord ++ tailWord_383346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383346).length < 2 ^ (prefixWord ++ tailWord_383346).sum := by decide
  have hdescent : baseEnd_383346 < baseStart_383346 := by decide
  rcases family_descends (prefixWord ++ tailWord_383346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383391 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_383391 : Nat := 118140960795 + 383391 * 2 ^ 59
def prefixEnd_383391 : Nat := 4983230072969 + 3 ^ 40 * 383391 * 2
def baseEnd_383391 : Nat := 87495049603562095399699

theorem tailTrace_383391 : CollatzResearch.WordTrace tailWord_383391 prefixEnd_383391 87495049603562095399699 := by
  unfold tailWord_383391
  simp only [CollatzResearch.WordTrace]
  refine ⟨13983418554047359814942027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9322279036031573209961351 13983418554047359814942027)
  ·
    refine ⟨20975127831071039722413041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13983418554047359814942027 20975127831071039722413041)
    ·
      refine ⟨15731345873303279791809781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20975127831071039722413041 15731345873303279791809781)
      ·
        refine ⟨1474813675622182480482167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15731345873303279791809781 1474813675622182480482167)
        ·
          refine ⟨2212220513433273720723251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474813675622182480482167 2212220513433273720723251)
          ·
            refine ⟨3318330770149910581084877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212220513433273720723251 3318330770149910581084877)
            ·
              refine ⟨1244374038806216467906829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3318330770149910581084877 1244374038806216467906829)
              ·
                refine ⟨466640264552331175465061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244374038806216467906829 466640264552331175465061)
                ·
                  refine ⟨87495049603562095399699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466640264552331175465061 87495049603562095399699)
                  ·
                    rfl

theorem cell21_383391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_383391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383391 prefixEnd_383391 := by exact prefixLift 383391
  have htrace : WordTrace (prefixWord ++ tailWord_383391) baseStart_383391 baseEnd_383391 := by
    simpa [prefixWord, tailWord_383391, baseEnd_383391] using wordTrace_append hprefix tailTrace_383391
  have hstable : (prefixWord ++ tailWord_383391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383391).length < 2 ^ (prefixWord ++ tailWord_383391).sum := by decide
  have hdescent : baseEnd_383391 < baseStart_383391 := by decide
  rcases family_descends (prefixWord ++ tailWord_383391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383428 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_383428 : Nat := 118140960795 + 383428 * 2 ^ 59
def prefixEnd_383428 : Nat := 4983230072969 + 3 ^ 40 * 383428 * 2
def baseEnd_383428 : Nat := 87503493507658253282957

theorem tailTrace_383428 : CollatzResearch.WordTrace tailWord_383428 prefixEnd_383428 87503493507658253282957 := by
  unfold tailWord_383428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992384027456657567019469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9323178703275543422692625 6992384027456657567019469)
  ·
    refine ⟨2622144010296246587632301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6992384027456657567019469 2622144010296246587632301)
    ·
      refine ⟨983304003861092470362113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2622144010296246587632301 983304003861092470362113)
      ·
        refine ⟨737478002895819352771585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983304003861092470362113 737478002895819352771585)
        ·
          refine ⟨553108502171864514578689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737478002895819352771585 553108502171864514578689)
          ·
            refine ⟨414831376628898385934017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553108502171864514578689 414831376628898385934017)
            ·
              refine ⟨311123532471673789450513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414831376628898385934017 311123532471673789450513)
              ·
                refine ⟨233342649353755342087885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311123532471673789450513 233342649353755342087885)
                ·
                  refine ⟨87503493507658253282957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233342649353755342087885 87503493507658253282957)
                  ·
                    rfl

theorem cell21_383428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_383428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383428 prefixEnd_383428 := by exact prefixLift 383428
  have htrace : WordTrace (prefixWord ++ tailWord_383428) baseStart_383428 baseEnd_383428 := by
    simpa [prefixWord, tailWord_383428, baseEnd_383428] using wordTrace_append hprefix tailTrace_383428
  have hstable : (prefixWord ++ tailWord_383428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383428).length < 2 ^ (prefixWord ++ tailWord_383428).sum := by decide
  have hdescent : baseEnd_383428 < baseStart_383428 := by decide
  rcases family_descends (prefixWord ++ tailWord_383428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383470 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_383470 : Nat := 118140960795 + 383470 * 2 ^ 59
def prefixEnd_383470 : Nat := 4983230072969 + 3 ^ 40 * 383470 * 2
def baseEnd_383470 : Nat := 87513078479875513582871

theorem tailTrace_383470 : CollatzResearch.WordTrace tailWord_383470 prefixEnd_383470 87513078479875513582871 := by
  unfold tailWord_383470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748287490095144538383483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9324199947174104204711909 1748287490095144538383483)
  ·
    refine ⟨2622431235142716807575225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748287490095144538383483 2622431235142716807575225)
    ·
      refine ⟨1966823426357037605681419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2622431235142716807575225 1966823426357037605681419)
      ·
        refine ⟨2950235139535556408522129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966823426357037605681419 2950235139535556408522129)
        ·
          refine ⟨2212676354651667306391597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950235139535556408522129 2212676354651667306391597)
          ·
            refine ⟨829753632994375239896849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2212676354651667306391597 829753632994375239896849)
            ·
              refine ⟨622315224745781429922637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829753632994375239896849 622315224745781429922637)
              ·
                refine ⟨233368209279668036220989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622315224745781429922637 233368209279668036220989)
                ·
                  refine ⟨87513078479875513582871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233368209279668036220989 87513078479875513582871)
                  ·
                    rfl

theorem cell21_383470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_383470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383470 prefixEnd_383470 := by exact prefixLift 383470
  have htrace : WordTrace (prefixWord ++ tailWord_383470) baseStart_383470 baseEnd_383470 := by
    simpa [prefixWord, tailWord_383470, baseEnd_383470] using wordTrace_append hprefix tailTrace_383470
  have hstable : (prefixWord ++ tailWord_383470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383470).length < 2 ^ (prefixWord ++ tailWord_383470).sum := by decide
  have hdescent : baseEnd_383470 < baseStart_383470 := by decide
  rcases family_descends (prefixWord ++ tailWord_383470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383512 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_383512 : Nat := 118140960795 + 383512 * 2 ^ 59
def prefixEnd_383512 : Nat := 4983230072969 + 3 ^ 40 * 383512 * 2
def baseEnd_383512 : Nat := 87522663452092773882785

theorem tailTrace_383512 : CollatzResearch.WordTrace tailWord_383512 prefixEnd_383512 87522663452092773882785 := by
  unfold tailWord_383512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993915893304498740048395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9325221191072664986731193 6993915893304498740048395)
  ·
    refine ⟨10490873839956748110072593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993915893304498740048395 10490873839956748110072593)
    ·
      refine ⟨7868155379967561082554445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10490873839956748110072593 7868155379967561082554445)
      ·
        refine ⟨2950558267487835405957917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7868155379967561082554445 2950558267487835405957917)
        ·
          refine ⟨1106459350307938277234219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2950558267487835405957917 1106459350307938277234219)
          ·
            refine ⟨1659689025461907415851329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106459350307938277234219 1659689025461907415851329)
            ·
              refine ⟨1244766769096430561888497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659689025461907415851329 1244766769096430561888497)
              ·
                refine ⟨933575076822322921416373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244766769096430561888497 933575076822322921416373)
                ·
                  refine ⟨87522663452092773882785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933575076822322921416373 87522663452092773882785)
                  ·
                    rfl

theorem cell21_383512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_383512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383512 prefixEnd_383512 := by exact prefixLift 383512
  have htrace : WordTrace (prefixWord ++ tailWord_383512) baseStart_383512 baseEnd_383512 := by
    simpa [prefixWord, tailWord_383512, baseEnd_383512] using wordTrace_append hprefix tailTrace_383512
  have hstable : (prefixWord ++ tailWord_383512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383512).length < 2 ^ (prefixWord ++ tailWord_383512).sum := by decide
  have hdescent : baseEnd_383512 < baseStart_383512 := by decide
  rcases family_descends (prefixWord ++ tailWord_383512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383546 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_383546 : Nat := 118140960795 + 383546 * 2 ^ 59
def prefixEnd_383546 : Nat := 4983230072969 + 3 ^ 40 * 383546 * 2
def baseEnd_383546 : Nat := 87530422715316270316049

theorem tailTrace_383546 : CollatzResearch.WordTrace tailWord_383546 prefixEnd_383546 87530422715316270316049 := by
  unfold tailWord_383546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497267967121455321708623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9326047912323880857889661 3497267967121455321708623)
  ·
    refine ⟨5245901950682182982562935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497267967121455321708623 5245901950682182982562935)
    ·
      refine ⟨7868852926023274473844403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245901950682182982562935 7868852926023274473844403)
      ·
        refine ⟨11803279389034911710766605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7868852926023274473844403 11803279389034911710766605)
        ·
          refine ⟨4426229770888091891537477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11803279389034911710766605 4426229770888091891537477)
          ·
            refine ⟨829918082041517229663277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4426229770888091891537477 829918082041517229663277)
            ·
              refine ⟨311219280765568961123729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829918082041517229663277 311219280765568961123729)
              ·
                refine ⟨233414460574176720842797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311219280765568961123729 233414460574176720842797)
                ·
                  refine ⟨87530422715316270316049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233414460574176720842797 87530422715316270316049)
                  ·
                    rfl

theorem cell21_383546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_383546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383546 prefixEnd_383546 := by exact prefixLift 383546
  have htrace : WordTrace (prefixWord ++ tailWord_383546) baseStart_383546 baseEnd_383546 := by
    simpa [prefixWord, tailWord_383546, baseEnd_383546] using wordTrace_append hprefix tailTrace_383546
  have hstable : (prefixWord ++ tailWord_383546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383546).length < 2 ^ (prefixWord ++ tailWord_383546).sum := by decide
  have hdescent : baseEnd_383546 < baseStart_383546 := by decide
  rcases family_descends (prefixWord ++ tailWord_383546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383557 : List Nat := [1, 3, 1, 1, 1, 6, 2, 6]
def baseStart_383557 : Nat := 118140960795 + 383557 * 2 ^ 59
def prefixEnd_383557 : Nat := 4983230072969 + 3 ^ 40 * 383557 * 2
def baseEnd_383557 : Nat := 29177644355060898544231

theorem tailTrace_383557 : CollatzResearch.WordTrace tailWord_383557 prefixEnd_383557 29177644355060898544231 := by
  unfold tailWord_383557
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989473071445970165484925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9326315380963980110323283 13989473071445970165484925)
  ·
    refine ⟨5246052401792238812056847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13989473071445970165484925 5246052401792238812056847)
    ·
      refine ⟨7869078602688358218085271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5246052401792238812056847 7869078602688358218085271)
      ·
        refine ⟨11803617904032537327127907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869078602688358218085271 11803617904032537327127907)
        ·
          refine ⟨17705426856048805990691861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11803617904032537327127907 17705426856048805990691861)
          ·
            refine ⟨829941883877287780813681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17705426856048805990691861 829941883877287780813681)
            ·
              refine ⟨622456412907965835610261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829941883877287780813681 622456412907965835610261)
              ·
                refine ⟨29177644355060898544231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 622456412907965835610261 29177644355060898544231)
                ·
                  rfl

theorem cell21_383557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_383557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383557 prefixEnd_383557 := by exact prefixLift 383557
  have htrace : WordTrace (prefixWord ++ tailWord_383557) baseStart_383557 baseEnd_383557 := by
    simpa [prefixWord, tailWord_383557, baseEnd_383557] using wordTrace_append hprefix tailTrace_383557
  have hstable : (prefixWord ++ tailWord_383557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383557).length < 2 ^ (prefixWord ++ tailWord_383557).sum := by decide
  have hdescent : baseEnd_383557 < baseStart_383557 := by decide
  rcases family_descends (prefixWord ++ tailWord_383557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383670 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_383670 : Nat := 118140960795 + 383670 * 2 ^ 59
def prefixEnd_383670 : Nat := 4983230072969 + 3 ^ 40 * 383670 * 2
def baseEnd_383670 : Nat := 87558721204719610249129

theorem tailTrace_383670 : CollatzResearch.WordTrace tailWord_383670 prefixEnd_383670 87558721204719610249129 := by
  unfold tailWord_383670
  simp only [CollatzResearch.WordTrace]
  refine ⟨874599657502286904021779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9329063013357726976232309 874599657502286904021779)
  ·
    refine ⟨1311899486253430356032669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874599657502286904021779 1311899486253430356032669)
    ·
      refine ⟨491962307345036383512251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1311899486253430356032669 491962307345036383512251)
      ·
        refine ⟨737943461017554575268377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491962307345036383512251 737943461017554575268377)
        ·
          refine ⟨553457595763165931451283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737943461017554575268377 553457595763165931451283)
          ·
            refine ⟨830186393644748897176925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553457595763165931451283 830186393644748897176925)
            ·
              refine ⟨311319897616780836441347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 830186393644748897176925 311319897616780836441347)
              ·
                refine ⟨466979846425171254662021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311319897616780836441347 466979846425171254662021)
                ·
                  refine ⟨87558721204719610249129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466979846425171254662021 87558721204719610249129)
                  ·
                    rfl

theorem cell21_383670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_383670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383670 prefixEnd_383670 := by exact prefixLift 383670
  have htrace : WordTrace (prefixWord ++ tailWord_383670) baseStart_383670 baseEnd_383670 := by
    simpa [prefixWord, tailWord_383670, baseEnd_383670] using wordTrace_append hprefix tailTrace_383670
  have hstable : (prefixWord ++ tailWord_383670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383670).length < 2 ^ (prefixWord ++ tailWord_383670).sum := by decide
  have hdescent : baseEnd_383670 < baseStart_383670 := by decide
  rcases family_descends (prefixWord ++ tailWord_383670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383799 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_383799 : Nat := 118140960795 + 383799 * 2 ^ 59
def prefixEnd_383799 : Nat := 4983230072969 + 3 ^ 40 * 383799 * 2
def baseEnd_383799 : Nat := 87588160762244052598865

theorem tailTrace_383799 : CollatzResearch.WordTrace tailWord_383799 prefixEnd_383799 87588160762244052598865 := by
  unfold tailWord_383799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998299536569245495794451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9332199691046163663862967 13998299536569245495794451)
  ·
    refine ⟨20997449304853868243691677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13998299536569245495794451 20997449304853868243691677)
    ·
      refine ⟨7874043489320200591384379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20997449304853868243691677 7874043489320200591384379)
      ·
        refine ⟨11811065233980300887076569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7874043489320200591384379 11811065233980300887076569)
        ·
          refine ⟨8858298925485225665307427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11811065233980300887076569 8858298925485225665307427)
          ·
            refine ⟨13287448388227838497961141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8858298925485225665307427 13287448388227838497961141)
            ·
              refine ⟨1245698286396359859183857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13287448388227838497961141 1245698286396359859183857)
              ·
                refine ⟨934273714797269894387893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245698286396359859183857 934273714797269894387893)
                ·
                  refine ⟨87588160762244052598865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934273714797269894387893 87588160762244052598865)
                  ·
                    rfl

theorem cell21_383799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_383799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383799 prefixEnd_383799 := by exact prefixLift 383799
  have htrace : WordTrace (prefixWord ++ tailWord_383799) baseStart_383799 baseEnd_383799 := by
    simpa [prefixWord, tailWord_383799, baseEnd_383799] using wordTrace_append hprefix tailTrace_383799
  have hstable : (prefixWord ++ tailWord_383799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383799).length < 2 ^ (prefixWord ++ tailWord_383799).sum := by decide
  have hdescent : baseEnd_383799 < baseStart_383799 := by decide
  rcases family_descends (prefixWord ++ tailWord_383799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383802 : List Nat := [3, 1, 1, 1, 6, 1, 3, 5]
def baseStart_383802 : Nat := 118140960795 + 383802 * 2 ^ 59
def prefixEnd_383802 : Nat := 4983230072969 + 3 ^ 40 * 383802 * 2
def baseEnd_383802 : Nat := 29196281801038904682953

theorem tailTrace_383802 : CollatzResearch.WordTrace tailWord_383802 prefixEnd_383802 29196281801038904682953 := by
  unfold tailWord_383802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499602238889594252038415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9332272637038918005435773 3499602238889594252038415)
  ·
    refine ⟨5249403358334391378057623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3499602238889594252038415 5249403358334391378057623)
    ·
      refine ⟨7874105037501587067086435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5249403358334391378057623 7874105037501587067086435)
      ·
        refine ⟨11811157556252380600629653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7874105037501587067086435 11811157556252380600629653)
        ·
          refine ⟨553648010449330340654515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11811157556252380600629653 553648010449330340654515)
          ·
            refine ⟨830472015673995510981773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553648010449330340654515 830472015673995510981773)
            ·
              refine ⟨311427005877748316618165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 830472015673995510981773 311427005877748316618165)
              ·
                refine ⟨29196281801038904682953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311427005877748316618165 29196281801038904682953)
                ·
                  rfl

theorem cell21_383802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_383802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383802 prefixEnd_383802 := by exact prefixLift 383802
  have htrace : WordTrace (prefixWord ++ tailWord_383802) baseStart_383802 baseEnd_383802 := by
    simpa [prefixWord, tailWord_383802, baseEnd_383802] using wordTrace_append hprefix tailTrace_383802
  have hstable : (prefixWord ++ tailWord_383802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383802).length < 2 ^ (prefixWord ++ tailWord_383802).sum := by decide
  have hdescent : baseEnd_383802 < baseStart_383802 := by decide
  rcases family_descends (prefixWord ++ tailWord_383802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383861 : List Nat := [1, 3, 4, 1, 1, 3, 1, 7]
def baseStart_383861 : Nat := 118140960795 + 383861 * 2 ^ 59
def prefixEnd_383861 : Nat := 4983230072969 + 3 ^ 40 * 383861 * 2
def baseEnd_383861 : Nat := 29200770002315240855135

theorem tailTrace_383861 : CollatzResearch.WordTrace tailWord_383861 prefixEnd_383861 29200770002315240855135 := by
  unfold tailWord_383861
  simp only [CollatzResearch.WordTrace]
  refine ⟨14000560862344630084551437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9333707241563086723034291 14000560862344630084551437)
  ·
    refine ⟨5250210323379236281706789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14000560862344630084551437 5250210323379236281706789)
    ·
      refine ⟨984414435633606802820023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5250210323379236281706789 984414435633606802820023)
      ·
        refine ⟨1476621653450410204230035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984414435633606802820023 1476621653450410204230035)
        ·
          refine ⟨2214932480175615306345053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476621653450410204230035 2214932480175615306345053)
          ·
            refine ⟨830599680065855739879395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214932480175615306345053 830599680065855739879395)
            ·
              refine ⟨1245899520098783609819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830599680065855739879395 1245899520098783609819093)
              ·
                refine ⟨29200770002315240855135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1245899520098783609819093 29200770002315240855135)
                ·
                  rfl

theorem cell21_383861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_383861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383861 prefixEnd_383861 := by exact prefixLift 383861
  have htrace : WordTrace (prefixWord ++ tailWord_383861) baseStart_383861 baseEnd_383861 := by
    simpa [prefixWord, tailWord_383861, baseEnd_383861] using wordTrace_append hprefix tailTrace_383861
  have hstable : (prefixWord ++ tailWord_383861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383861).length < 2 ^ (prefixWord ++ tailWord_383861).sum := by decide
  have hdescent : baseEnd_383861 < baseStart_383861 := by decide
  rcases family_descends (prefixWord ++ tailWord_383861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383954 : List Nat := [3, 2, 2, 3, 1, 3, 1, 6]
def baseStart_383954 : Nat := 118140960795 + 383954 * 2 ^ 59
def prefixEnd_383954 : Nat := 4983230072969 + 3 ^ 40 * 383954 * 2
def baseEnd_383954 : Nat := 29207844624666075838405

theorem tailTrace_383954 : CollatzResearch.WordTrace tailWord_383954 prefixEnd_383954 29207844624666075838405 := by
  unfold tailWord_383954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500988212751926741921729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9335968567338471311791277 3500988212751926741921729)
  ·
    refine ⟨2625741159563945056441297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3500988212751926741921729 2625741159563945056441297)
    ·
      refine ⟨1969305869672958792330973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2625741159563945056441297 1969305869672958792330973)
      ·
        refine ⟨738489701127359547124115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1969305869672958792330973 738489701127359547124115)
        ·
          refine ⟨1107734551691039320686173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738489701127359547124115 1107734551691039320686173)
          ·
            refine ⟨415400456884139745257315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1107734551691039320686173 415400456884139745257315)
            ·
              refine ⟨623100685326209617885973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415400456884139745257315 623100685326209617885973)
              ·
                refine ⟨29207844624666075838405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623100685326209617885973 29207844624666075838405)
                ·
                  rfl

theorem cell21_383954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_383954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383954 prefixEnd_383954 := by exact prefixLift 383954
  have htrace : WordTrace (prefixWord ++ tailWord_383954) baseStart_383954 baseEnd_383954 := by
    simpa [prefixWord, tailWord_383954, baseEnd_383954] using wordTrace_append hprefix tailTrace_383954
  have hstable : (prefixWord ++ tailWord_383954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383954).length < 2 ^ (prefixWord ++ tailWord_383954).sum := by decide
  have hdescent : baseEnd_383954 < baseStart_383954 := by decide
  rcases family_descends (prefixWord ++ tailWord_383954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383985 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 3]
def baseStart_383985 : Nat := 118140960795 + 383985 * 2 ^ 59
def prefixEnd_383985 : Nat := 4983230072969 + 3 ^ 40 * 383985 * 2
def baseEnd_383985 : Nat := 87630608496349062498485

theorem tailTrace_383985 : CollatzResearch.WordTrace tailWord_383985 prefixEnd_383985 87630608496349062498485 := by
  unfold tailWord_383985
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005083513895399262065409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9336722342596932841376939 14005083513895399262065409)
  ·
    refine ⟨10503812635421549446549057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14005083513895399262065409 10503812635421549446549057)
    ·
      refine ⟨7877859476566162084911793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10503812635421549446549057 7877859476566162084911793)
      ·
        refine ⟨5908394607424621563683845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877859476566162084911793 5908394607424621563683845)
        ·
          refine ⟨1107823988892116543190721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5908394607424621563683845 1107823988892116543190721)
          ·
            refine ⟨830867991669087407393041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107823988892116543190721 830867991669087407393041)
            ·
              refine ⟨623150993751815555544781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830867991669087407393041 623150993751815555544781)
              ·
                refine ⟨233681622656930833329293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623150993751815555544781 233681622656930833329293)
                ·
                  refine ⟨87630608496349062498485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233681622656930833329293 87630608496349062498485)
                  ·
                    rfl

theorem cell21_383985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_383985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383985 prefixEnd_383985 := by exact prefixLift 383985
  have htrace : WordTrace (prefixWord ++ tailWord_383985) baseStart_383985 baseEnd_383985 := by
    simpa [prefixWord, tailWord_383985, baseEnd_383985] using wordTrace_append hprefix tailTrace_383985
  have hstable : (prefixWord ++ tailWord_383985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383985).length < 2 ^ (prefixWord ++ tailWord_383985).sum := by decide
  have hdescent : baseEnd_383985 < baseStart_383985 := by decide
  rcases family_descends (prefixWord ++ tailWord_383985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383988 : List Nat := [2, 6, 2, 1, 1, 1, 8]
def baseStart_383988 : Nat := 118140960795 + 383988 * 2 ^ 59
def prefixEnd_383988 : Nat := 4983230072969 + 3 ^ 40 * 383988 * 2
def baseEnd_383988 : Nat := 9736810348580191549831

theorem tailTrace_383988 : CollatzResearch.WordTrace tailWord_383988 prefixEnd_383988 9736810348580191549831 := by
  unfold tailWord_383988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002596466442265387212309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9336795288589687182949745 7002596466442265387212309)
  ·
    refine ⟨328246709364481190025577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7002596466442265387212309 328246709364481190025577)
    ·
      refine ⟨246185032023360892519183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328246709364481190025577 246185032023360892519183)
      ·
        refine ⟨369277548035041338778775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246185032023360892519183 369277548035041338778775)
        ·
          refine ⟨553916322052562008168163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369277548035041338778775 553916322052562008168163)
          ·
            refine ⟨830874483078843012252245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553916322052562008168163 830874483078843012252245)
            ·
              refine ⟨9736810348580191549831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 830874483078843012252245 9736810348580191549831)
              ·
                rfl

theorem cell21_383988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 8].length) (baseStart_383988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383988 prefixEnd_383988 := by exact prefixLift 383988
  have htrace : WordTrace (prefixWord ++ tailWord_383988) baseStart_383988 baseEnd_383988 := by
    simpa [prefixWord, tailWord_383988, baseEnd_383988] using wordTrace_append hprefix tailTrace_383988
  have hstable : (prefixWord ++ tailWord_383988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383988).length < 2 ^ (prefixWord ++ tailWord_383988).sum := by decide
  have hdescent : baseEnd_383988 < baseStart_383988 := by decide
  rcases family_descends (prefixWord ++ tailWord_383988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383996 : List Nat := [2, 2, 2, 1, 2, 4, 8]
def baseStart_383996 : Nat := 118140960795 + 383996 * 2 ^ 59
def prefixEnd_383996 : Nat := 4983230072969 + 3 ^ 40 * 383996 * 2
def baseEnd_383996 : Nat := 9737013205135054201681

theorem tailTrace_383996 : CollatzResearch.WordTrace tailWord_383996 prefixEnd_383996 9737013205135054201681 := by
  unfold tailWord_383996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002742358427774070357921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9336989811237032093810561 7002742358427774070357921)
  ·
    refine ⟨5252056768820830552768441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7002742358427774070357921 5252056768820830552768441)
    ·
      refine ⟨3939042576615622914576331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5252056768820830552768441 3939042576615622914576331)
      ·
        refine ⟨5908563864923434371864497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939042576615622914576331 5908563864923434371864497)
        ·
          refine ⟨4431422898692575778898373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5908563864923434371864497 4431422898692575778898373)
          ·
            refine ⟨830891793504857958543445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4431422898692575778898373 830891793504857958543445)
            ·
              refine ⟨9737013205135054201681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 830891793504857958543445 9737013205135054201681)
              ·
                rfl

theorem cell21_383996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 8].length) (baseStart_383996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_383996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_383996 prefixEnd_383996 := by exact prefixLift 383996
  have htrace : WordTrace (prefixWord ++ tailWord_383996) baseStart_383996 baseEnd_383996 := by
    simpa [prefixWord, tailWord_383996, baseEnd_383996] using wordTrace_append hprefix tailTrace_383996
  have hstable : (prefixWord ++ tailWord_383996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383996).length < 2 ^ (prefixWord ++ tailWord_383996).sum := by decide
  have hdescent : baseEnd_383996 < baseStart_383996 := by decide
  rcases family_descends (prefixWord ++ tailWord_383996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384002 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_384002 : Nat := 118140960795 + 384002 * 2 ^ 59
def prefixEnd_384002 : Nat := 4983230072969 + 3 ^ 40 * 384002 * 2
def baseEnd_384002 : Nat := 87634488127960810715117

theorem tailTrace_384002 : CollatzResearch.WordTrace tailWord_384002 prefixEnd_384002 87634488127960810715117 := by
  unfold tailWord_384002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501425888708452791358565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9337135703222540776956173 3501425888708452791358565)
  ·
    refine ⟨656517354132834898379731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3501425888708452791358565 656517354132834898379731)
    ·
      refine ⟨984776031199252347569597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656517354132834898379731 984776031199252347569597)
      ·
        refine ⟨369291011699719630338599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 984776031199252347569597 369291011699719630338599)
        ·
          refine ⟨553936517549579445507899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369291011699719630338599 553936517549579445507899)
          ·
            refine ⟨830904776324369168261849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553936517549579445507899 830904776324369168261849)
            ·
              refine ⟨623178582243276876196387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830904776324369168261849 623178582243276876196387)
              ·
                refine ⟨934767873364915314294581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623178582243276876196387 934767873364915314294581)
                ·
                  refine ⟨87634488127960810715117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934767873364915314294581 87634488127960810715117)
                  ·
                    rfl

theorem cell21_384002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_384002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384002 prefixEnd_384002 := by exact prefixLift 384002
  have htrace : WordTrace (prefixWord ++ tailWord_384002) baseStart_384002 baseEnd_384002 := by
    simpa [prefixWord, tailWord_384002, baseEnd_384002] using wordTrace_append hprefix tailTrace_384002
  have hstable : (prefixWord ++ tailWord_384002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384002).length < 2 ^ (prefixWord ++ tailWord_384002).sum := by decide
  have hdescent : baseEnd_384002 < baseStart_384002 := by decide
  rcases family_descends (prefixWord ++ tailWord_384002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384072 : List Nat := [2, 1, 3, 1, 1, 1, 6, 6]
def baseStart_384072 : Nat := 118140960795 + 384072 * 2 ^ 59
def prefixEnd_384072 : Nat := 4983230072969 + 3 ^ 40 * 384072 * 2
def baseEnd_384072 : Nat := 29216821027218748182769

theorem tailTrace_384072 : CollatzResearch.WordTrace tailWord_384072 prefixEnd_384072 29216821027218748182769 := by
  unfold tailWord_384072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004128332290106560241235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9338837776386808746988313 7004128332290106560241235)
  ·
    refine ⟨10506192498435159840361853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7004128332290106560241235 10506192498435159840361853)
    ·
      refine ⟨3939822186913184940135695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10506192498435159840361853 3939822186913184940135695)
      ·
        refine ⟨5909733280369777410203543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939822186913184940135695 5909733280369777410203543)
        ·
          refine ⟨8864599920554666115305315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909733280369777410203543 8864599920554666115305315)
          ·
            refine ⟨13296899880831999172957973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8864599920554666115305315 13296899880831999172957973)
            ·
              refine ⟨623292181913999961232405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13296899880831999172957973 623292181913999961232405)
              ·
                refine ⟨29216821027218748182769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623292181913999961232405 29216821027218748182769)
                ·
                  rfl

theorem cell21_384072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_384072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384072 prefixEnd_384072 := by exact prefixLift 384072
  have htrace : WordTrace (prefixWord ++ tailWord_384072) baseStart_384072 baseEnd_384072 := by
    simpa [prefixWord, tailWord_384072, baseEnd_384072] using wordTrace_append hprefix tailTrace_384072
  have hstable : (prefixWord ++ tailWord_384072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384072).length < 2 ^ (prefixWord ++ tailWord_384072).sum := by decide
  have hdescent : baseEnd_384072 < baseStart_384072 := by decide
  rcases family_descends (prefixWord ++ tailWord_384072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384213 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 3]
def baseStart_384213 : Nat := 118140960795 + 384213 * 2 ^ 59
def prefixEnd_384213 : Nat := 4983230072969 + 3 ^ 40 * 384213 * 2
def baseEnd_384213 : Nat := 87682641202671332698019

theorem tailTrace_384213 : CollatzResearch.WordTrace tailWord_384213 prefixEnd_384213 87682641202671332698019 := by
  unfold tailWord_384213
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013399357069394201365293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342266238046262800910195 14013399357069394201365293)
  ·
    refine ⟨5255024758901022825511985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14013399357069394201365293 5255024758901022825511985)
    ·
      refine ⟨3941268569175767119133989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5255024758901022825511985 3941268569175767119133989)
      ·
        refine ⟨738987856720456334837623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3941268569175767119133989 738987856720456334837623)
        ·
          refine ⟨1108481785080684502256435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738987856720456334837623 1108481785080684502256435)
          ·
            refine ⟨1662722677621026753384653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108481785080684502256435 1662722677621026753384653)
            ·
              refine ⟨623521004107885032519245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1662722677621026753384653 623521004107885032519245)
              ·
                refine ⟨233820376540456887194717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623521004107885032519245 233820376540456887194717)
                ·
                  refine ⟨87682641202671332698019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233820376540456887194717 87682641202671332698019)
                  ·
                    rfl

theorem cell21_384213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_384213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384213 prefixEnd_384213 := by exact prefixLift 384213
  have htrace : WordTrace (prefixWord ++ tailWord_384213) baseStart_384213 baseEnd_384213 := by
    simpa [prefixWord, tailWord_384213, baseEnd_384213] using wordTrace_append hprefix tailTrace_384213
  have hstable : (prefixWord ++ tailWord_384213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384213).length < 2 ^ (prefixWord ++ tailWord_384213).sum := by decide
  have hdescent : baseEnd_384213 < baseStart_384213 := by decide
  rcases family_descends (prefixWord ++ tailWord_384213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384224 : List Nat := [2, 1, 1, 3, 1, 6, 7]
def baseStart_384224 : Nat := 118140960795 + 384224 * 2 ^ 59
def prefixEnd_384224 : Nat := 4983230072969 + 3 ^ 40 * 384224 * 2
def baseEnd_384224 : Nat := 9742794616948639779407

theorem tailTrace_384224 : CollatzResearch.WordTrace tailWord_384224 prefixEnd_384224 9742794616948639779407 := by
  unfold tailWord_384224
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006900280014771540007863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9342533706686362053343817 7006900280014771540007863)
  ·
    refine ⟨10510350420022157310011795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7006900280014771540007863 10510350420022157310011795)
    ·
      refine ⟨15765525630033235965017693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10510350420022157310011795 15765525630033235965017693)
      ·
        refine ⟨5912072111262463486881635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15765525630033235965017693 5912072111262463486881635)
        ·
          refine ⟨8868108166893695230322453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912072111262463486881635 8868108166893695230322453)
          ·
            refine ⟨415692570323141963921365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8868108166893695230322453 415692570323141963921365)
            ·
              refine ⟨9742794616948639779407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 415692570323141963921365 9742794616948639779407)
              ·
                rfl

theorem cell21_384224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 7].length) (baseStart_384224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384224 prefixEnd_384224 := by exact prefixLift 384224
  have htrace : WordTrace (prefixWord ++ tailWord_384224) baseStart_384224 baseEnd_384224 := by
    simpa [prefixWord, tailWord_384224, baseEnd_384224] using wordTrace_append hprefix tailTrace_384224
  have hstable : (prefixWord ++ tailWord_384224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384224).length < 2 ^ (prefixWord ++ tailWord_384224).sum := by decide
  have hdescent : baseEnd_384224 < baseStart_384224 := by decide
  rcases family_descends (prefixWord ++ tailWord_384224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384393 : List Nat := [1, 2, 1, 1, 8, 1, 7]
def baseStart_384393 : Nat := 118140960795 + 384393 * 2 ^ 59
def prefixEnd_384393 : Nat := 4983230072969 + 3 ^ 40 * 384393 * 2
def baseEnd_384393 : Nat := 9747079961670113299739

theorem tailTrace_384393 : CollatzResearch.WordTrace tailWord_384393 prefixEnd_384393 9747079961670113299739 := by
  unfold tailWord_384393
  simp only [CollatzResearch.WordTrace]
  refine ⟨14019964496417284942917833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9346642997611523295278555 14019964496417284942917833)
  ·
    refine ⟨10514973372312963707188375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14019964496417284942917833 10514973372312963707188375)
    ·
      refine ⟨15772460058469445560782563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10514973372312963707188375 15772460058469445560782563)
      ·
        refine ⟨23658690087704168341173845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15772460058469445560782563 23658690087704168341173845)
        ·
          refine ⟨277250274465283222748131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 23658690087704168341173845 277250274465283222748131)
          ·
            refine ⟨415875411697924834122197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277250274465283222748131 415875411697924834122197)
            ·
              refine ⟨9747079961670113299739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 415875411697924834122197 9747079961670113299739)
              ·
                rfl

theorem cell21_384393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 7].length) (baseStart_384393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384393 prefixEnd_384393 := by exact prefixLift 384393
  have htrace : WordTrace (prefixWord ++ tailWord_384393) baseStart_384393 baseEnd_384393 := by
    simpa [prefixWord, tailWord_384393, baseEnd_384393] using wordTrace_append hprefix tailTrace_384393
  have hstable : (prefixWord ++ tailWord_384393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384393).length < 2 ^ (prefixWord ++ tailWord_384393).sum := by decide
  have hdescent : baseEnd_384393 < baseStart_384393 := by decide
  rcases family_descends (prefixWord ++ tailWord_384393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384450 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_384450 : Nat := 118140960795 + 384450 * 2 ^ 59
def prefixEnd_384450 : Nat := 4983230072969 + 3 ^ 40 * 384450 * 2
def baseEnd_384450 : Nat := 87736727831611587247535

theorem tailTrace_384450 : CollatzResearch.WordTrace tailWord_384450 prefixEnd_384450 87736727831611587247535 := by
  unfold tailWord_384450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505510864302695919435701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9348028971473855785161869 3505510864302695919435701)
  ·
    refine ⟨328641643528377742447097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3505510864302695919435701 328641643528377742447097)
    ·
      refine ⟨246481232646283306835323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328641643528377742447097 246481232646283306835323)
      ·
        refine ⟨369721848969424960252985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246481232646283306835323 369721848969424960252985)
        ·
          refine ⟨277291386727068720189739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369721848969424960252985 277291386727068720189739)
          ·
            refine ⟨415937080090603080284609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277291386727068720189739 415937080090603080284609)
            ·
              refine ⟨311952810067952310213457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415937080090603080284609 311952810067952310213457)
              ·
                refine ⟨233964607550964232660093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311952810067952310213457 233964607550964232660093)
                ·
                  refine ⟨87736727831611587247535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233964607550964232660093 87736727831611587247535)
                  ·
                    rfl

theorem cell21_384450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_384450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384450 prefixEnd_384450 := by exact prefixLift 384450
  have htrace : WordTrace (prefixWord ++ tailWord_384450) baseStart_384450 baseEnd_384450 := by
    simpa [prefixWord, tailWord_384450, baseEnd_384450] using wordTrace_append hprefix tailTrace_384450
  have hstable : (prefixWord ++ tailWord_384450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384450).length < 2 ^ (prefixWord ++ tailWord_384450).sum := by decide
  have hdescent : baseEnd_384450 < baseStart_384450 := by decide
  rcases family_descends (prefixWord ++ tailWord_384450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384452 : List Nat := [2, 3, 3, 2, 1, 10]
def baseStart_384452 : Nat := 118140960795 + 384452 * 2 ^ 59
def prefixEnd_384452 : Nat := 4983230072969 + 3 ^ 40 * 384452 * 2
def baseEnd_384452 : Nat := 3249525342920741785711

theorem tailTrace_384452 : CollatzResearch.WordTrace tailWord_384452 prefixEnd_384452 3249525342920741785711 := by
  unfold tailWord_384452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011058201601769009657805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9348077602135692012877073 7011058201601769009657805)
  ·
    refine ⟨2629146825600663378621677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7011058201601769009657805 2629146825600663378621677)
    ·
      refine ⟨985930059600248766983129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2629146825600663378621677 985930059600248766983129)
      ·
        refine ⟨739447544700186575237347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985930059600248766983129 739447544700186575237347)
        ·
          refine ⟨1109171317050279862856021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739447544700186575237347 1109171317050279862856021)
          ·
            refine ⟨3249525342920741785711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1109171317050279862856021 3249525342920741785711)
            ·
              rfl

theorem cell21_384452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 10].length) (baseStart_384452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384452 prefixEnd_384452 := by exact prefixLift 384452
  have htrace : WordTrace (prefixWord ++ tailWord_384452) baseStart_384452 baseEnd_384452 := by
    simpa [prefixWord, tailWord_384452, baseEnd_384452] using wordTrace_append hprefix tailTrace_384452
  have hstable : (prefixWord ++ tailWord_384452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384452).length < 2 ^ (prefixWord ++ tailWord_384452).sum := by decide
  have hdescent : baseEnd_384452 < baseStart_384452 := by decide
  rcases family_descends (prefixWord ++ tailWord_384452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384483 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_384483 : Nat := 118140960795 + 384483 * 2 ^ 59
def prefixEnd_384483 : Nat := 4983230072969 + 3 ^ 40 * 384483 * 2
def baseEnd_384483 : Nat := 87744258881210863197467

theorem tailTrace_384483 : CollatzResearch.WordTrace tailWord_384483 prefixEnd_384483 87744258881210863197467 := by
  unfold tailWord_384483
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023247066091230313694103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9348831377394153542462735 14023247066091230313694103)
  ·
    refine ⟨21034870599136845470541155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14023247066091230313694103 21034870599136845470541155)
    ·
      refine ⟨31552305898705268205811733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21034870599136845470541155 31552305898705268205811733)
      ·
        refine ⟨1479014339001809447147425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31552305898705268205811733 1479014339001809447147425)
        ·
          refine ⟨1109260754251357085360569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479014339001809447147425 1109260754251357085360569)
          ·
            refine ⟨831945565688517814020427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109260754251357085360569 831945565688517814020427)
            ·
              refine ⟨1247918348532776721030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831945565688517814020427 1247918348532776721030641)
              ·
                refine ⟨935938761399582540772981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247918348532776721030641 935938761399582540772981)
                ·
                  refine ⟨87744258881210863197467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935938761399582540772981 87744258881210863197467)
                  ·
                    rfl

theorem cell21_384483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_384483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384483 prefixEnd_384483 := by exact prefixLift 384483
  have htrace : WordTrace (prefixWord ++ tailWord_384483) baseStart_384483 baseEnd_384483 := by
    simpa [prefixWord, tailWord_384483, baseEnd_384483] using wordTrace_append hprefix tailTrace_384483
  have hstable : (prefixWord ++ tailWord_384483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384483).length < 2 ^ (prefixWord ++ tailWord_384483).sum := by decide
  have hdescent : baseEnd_384483 < baseStart_384483 := by decide
  rcases family_descends (prefixWord ++ tailWord_384483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384545 : List Nat := [1, 2, 3, 2, 2, 4, 2, 5]
def baseStart_384545 : Nat := 118140960795 + 384545 * 2 ^ 59
def prefixEnd_384545 : Nat := 4983230072969 + 3 ^ 40 * 384545 * 2
def baseEnd_384545 : Nat := 29252802708637511054669

theorem tailTrace_384545 : CollatzResearch.WordTrace tailWord_384545 prefixEnd_384545 29252802708637511054669 := by
  unfold tailWord_384545
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025508391866614902451089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9350338927911076601634059 14025508391866614902451089)
  ·
    refine ⟨10519131293899961176838317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14025508391866614902451089 10519131293899961176838317)
    ·
      refine ⟨3944674235212485441314369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10519131293899961176838317 3944674235212485441314369)
      ·
        refine ⟨2958505676409364080985777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944674235212485441314369 2958505676409364080985777)
        ·
          refine ⟨2218879257307023060739333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958505676409364080985777 2218879257307023060739333)
          ·
            refine ⟨416039860745066823888625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2218879257307023060739333 416039860745066823888625)
            ·
              refine ⟨312029895558800117916469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416039860745066823888625 312029895558800117916469)
              ·
                refine ⟨29252802708637511054669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312029895558800117916469 29252802708637511054669)
                ·
                  rfl

theorem cell21_384545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 5].length) (baseStart_384545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384545 prefixEnd_384545 := by exact prefixLift 384545
  have htrace : WordTrace (prefixWord ++ tailWord_384545) baseStart_384545 baseEnd_384545 := by
    simpa [prefixWord, tailWord_384545, baseEnd_384545] using wordTrace_append hprefix tailTrace_384545
  have hstable : (prefixWord ++ tailWord_384545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384545).length < 2 ^ (prefixWord ++ tailWord_384545).sum := by decide
  have hdescent : baseEnd_384545 < baseStart_384545 := by decide
  rcases family_descends (prefixWord ++ tailWord_384545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384582 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_384582 : Nat := 118140960795 + 384582 * 2 ^ 59
def prefixEnd_384582 : Nat := 4983230072969 + 3 ^ 40 * 384582 * 2
def baseEnd_384582 : Nat := 87766852030008691047265

theorem tailTrace_384582 : CollatzResearch.WordTrace tailWord_384582 prefixEnd_384582 87766852030008691047265 := by
  unfold tailWord_384582
  simp only [CollatzResearch.WordTrace]
  refine ⟨438339309147892819423375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9351238595155046814365333 438339309147892819423375)
  ·
    refine ⟨657508963721839229135063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438339309147892819423375 657508963721839229135063)
    ·
      refine ⟨986263445582758843702595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657508963721839229135063 986263445582758843702595)
      ·
        refine ⟨1479395168374138265553893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986263445582758843702595 1479395168374138265553893)
        ·
          refine ⟨277386594070150924791355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1479395168374138265553893 277386594070150924791355)
          ·
            refine ⟨416079891105226387187033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277386594070150924791355 416079891105226387187033)
            ·
              refine ⟨312059918328919790390275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416079891105226387187033 312059918328919790390275)
              ·
                refine ⟨468089877493379685585413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312059918328919790390275 468089877493379685585413)
                ·
                  refine ⟨87766852030008691047265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468089877493379685585413 87766852030008691047265)
                  ·
                    rfl

theorem cell21_384582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_384582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384582 prefixEnd_384582 := by exact prefixLift 384582
  have htrace : WordTrace (prefixWord ++ tailWord_384582) baseStart_384582 baseEnd_384582 := by
    simpa [prefixWord, tailWord_384582, baseEnd_384582] using wordTrace_append hprefix tailTrace_384582
  have hstable : (prefixWord ++ tailWord_384582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384582).length < 2 ^ (prefixWord ++ tailWord_384582).sum := by decide
  have hdescent : baseEnd_384582 < baseStart_384582 := by decide
  rcases family_descends (prefixWord ++ tailWord_384582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384604 : List Nat := [2, 2, 4, 1, 2, 1, 2, 7]
def baseStart_384604 : Nat := 118140960795 + 384604 * 2 ^ 59
def prefixEnd_384604 : Nat := 4983230072969 + 3 ^ 40 * 384604 * 2
def baseEnd_384604 : Nat := 29257290909913847226851

theorem tailTrace_384604 : CollatzResearch.WordTrace tailWord_384604 prefixEnd_384604 29257290909913847226851 := by
  unfold tailWord_384604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013830149326433989424433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9351773532435245319232577 7013830149326433989424433)
  ·
    refine ⟨5260372611994825492068325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7013830149326433989424433 5260372611994825492068325)
    ·
      refine ⟨986319864749029779762811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5260372611994825492068325 986319864749029779762811)
      ·
        refine ⟨1479479797123544669644217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986319864749029779762811 1479479797123544669644217)
        ·
          refine ⟨1109609847842658502233163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479479797123544669644217 1109609847842658502233163)
          ·
            refine ⟨1664414771763987753349745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109609847842658502233163 1664414771763987753349745)
            ·
              refine ⟨1248311078822990815012309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1664414771763987753349745 1248311078822990815012309)
              ·
                refine ⟨29257290909913847226851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1248311078822990815012309 29257290909913847226851)
                ·
                  rfl

theorem cell21_384604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_384604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384604 prefixEnd_384604 := by exact prefixLift 384604
  have htrace : WordTrace (prefixWord ++ tailWord_384604) baseStart_384604 baseEnd_384604 := by
    simpa [prefixWord, tailWord_384604, baseEnd_384604] using wordTrace_append hprefix tailTrace_384604
  have hstable : (prefixWord ++ tailWord_384604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384604).length < 2 ^ (prefixWord ++ tailWord_384604).sum := by decide
  have hdescent : baseEnd_384604 < baseStart_384604 := by decide
  rcases family_descends (prefixWord ++ tailWord_384604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384635 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 3]
def baseStart_384635 : Nat := 118140960795 + 384635 * 2 ^ 59
def prefixEnd_384635 : Nat := 4983230072969 + 3 ^ 40 * 384635 * 2
def baseEnd_384635 : Nat := 87778947352092376663823

theorem tailTrace_384635 : CollatzResearch.WordTrace tailWord_384635 prefixEnd_384635 87778947352092376663823 := by
  unfold tailWord_384635
  simp only [CollatzResearch.WordTrace]
  refine ⟨14028790961540560273227359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9352527307693706848818239 14028790961540560273227359)
  ·
    refine ⟨21043186442310840409841039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14028790961540560273227359 21043186442310840409841039)
    ·
      refine ⟨31564779663466260614761559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21043186442310840409841039 31564779663466260614761559)
      ·
        refine ⟨47347169495199390922142339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31564779663466260614761559 47347169495199390922142339)
        ·
          refine ⟨71020754242799086383213509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47347169495199390922142339 71020754242799086383213509)
          ·
            refine ⟨13316391420524828696852533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71020754242799086383213509 13316391420524828696852533)
            ·
              refine ⟨1248411695674202690329925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13316391420524828696852533 1248411695674202690329925)
              ·
                refine ⟨234077192938913004436861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1248411695674202690329925 234077192938913004436861)
                ·
                  refine ⟨87778947352092376663823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234077192938913004436861 87778947352092376663823)
                  ·
                    rfl

theorem cell21_384635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 3].length) (baseStart_384635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384635 prefixEnd_384635 := by exact prefixLift 384635
  have htrace : WordTrace (prefixWord ++ tailWord_384635) baseStart_384635 baseEnd_384635 := by
    simpa [prefixWord, tailWord_384635, baseEnd_384635] using wordTrace_append hprefix tailTrace_384635
  have hstable : (prefixWord ++ tailWord_384635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384635).length < 2 ^ (prefixWord ++ tailWord_384635).sum := by decide
  have hdescent : baseEnd_384635 < baseStart_384635 := by decide
  rcases family_descends (prefixWord ++ tailWord_384635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384649 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_384649 : Nat := 118140960795 + 384649 * 2 ^ 59
def prefixEnd_384649 : Nat := 4983230072969 + 3 ^ 40 * 384649 * 2
def baseEnd_384649 : Nat := 87782142342831463430461

theorem tailTrace_384649 : CollatzResearch.WordTrace tailWord_384649 prefixEnd_384649 87782142342831463430461 := by
  unfold tailWord_384649
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029301583489840664237001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9352867722326560442824667 14029301583489840664237001)
  ·
    refine ⟨10521976187617380498177751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14029301583489840664237001 10521976187617380498177751)
    ·
      refine ⟨15782964281426070747266627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521976187617380498177751 15782964281426070747266627)
      ·
        refine ⟨23674446422139106120899941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782964281426070747266627 23674446422139106120899941)
        ·
          refine ⟨4438958704151082397668739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23674446422139106120899941 4438958704151082397668739)
          ·
            refine ⟨6658438056226623596503109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438958704151082397668739 6658438056226623596503109)
            ·
              refine ⟨1248457135542491924344333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6658438056226623596503109 1248457135542491924344333)
              ·
                refine ⟨468171425828434471629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1248457135542491924344333 468171425828434471629125)
                ·
                  refine ⟨87782142342831463430461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468171425828434471629125 87782142342831463430461)
                  ·
                    rfl

theorem cell21_384649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_384649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384649 prefixEnd_384649 := by exact prefixLift 384649
  have htrace : WordTrace (prefixWord ++ tailWord_384649) baseStart_384649 baseEnd_384649 := by
    simpa [prefixWord, tailWord_384649, baseEnd_384649] using wordTrace_append hprefix tailTrace_384649
  have hstable : (prefixWord ++ tailWord_384649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384649).length < 2 ^ (prefixWord ++ tailWord_384649).sum := by decide
  have hdescent : baseEnd_384649 < baseStart_384649 := by decide
  rcases family_descends (prefixWord ++ tailWord_384649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384714 : List Nat := [3, 1, 2, 1, 6, 1, 2, 5]
def baseStart_384714 : Nat := 118140960795 + 384714 * 2 ^ 59
def prefixEnd_384714 : Nat := 4983230072969 + 3 ^ 40 * 384714 * 2
def baseEnd_384714 : Nat := 29265658742801931615665

theorem tailTrace_384714 : CollatzResearch.WordTrace tailWord_384714 prefixEnd_384714 29265658742801931615665 := by
  unfold tailWord_384714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507918082063589191338299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9354448218836237843568797 3507918082063589191338299)
  ·
    refine ⟨5261877123095383787007449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3507918082063589191338299 5261877123095383787007449)
    ·
      refine ⟨3946407842321537840255587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5261877123095383787007449 3946407842321537840255587)
      ·
        refine ⟨5919611763482306760383381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946407842321537840255587 5919611763482306760383381)
        ·
          refine ⟨277481801413233129392971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5919611763482306760383381 277481801413233129392971)
          ·
            refine ⟨416222702119849694089457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277481801413233129392971 416222702119849694089457)
            ·
              refine ⟨312167026589887270567093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416222702119849694089457 312167026589887270567093)
              ·
                refine ⟨29265658742801931615665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312167026589887270567093 29265658742801931615665)
                ·
                  rfl

theorem cell21_384714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_384714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384714 prefixEnd_384714 := by exact prefixLift 384714
  have htrace : WordTrace (prefixWord ++ tailWord_384714) baseStart_384714 baseEnd_384714 := by
    simpa [prefixWord, tailWord_384714, baseEnd_384714] using wordTrace_append hprefix tailTrace_384714
  have hstable : (prefixWord ++ tailWord_384714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384714).length < 2 ^ (prefixWord ++ tailWord_384714).sum := by decide
  have hdescent : baseEnd_384714 < baseStart_384714 := by decide
  rcases family_descends (prefixWord ++ tailWord_384714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384801 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_384801 : Nat := 118140960795 + 384801 * 2 ^ 59
def prefixEnd_384801 : Nat := 4983230072969 + 3 ^ 40 * 384801 * 2
def baseEnd_384801 : Nat := 87816830813712976896817

theorem tailTrace_384801 : CollatzResearch.WordTrace tailWord_384801 prefixEnd_384801 87816830813712976896817 := by
  unfold tailWord_384801
  simp only [CollatzResearch.WordTrace]
  refine ⟨14034845478939170623770257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9356563652626113749180171 14034845478939170623770257)
  ·
    refine ⟨10526134109204377967827693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14034845478939170623770257 10526134109204377967827693)
    ·
      refine ⟨3947300290951641737935385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10526134109204377967827693 3947300290951641737935385)
      ·
        refine ⟨2960475218213731303451539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3947300290951641737935385 2960475218213731303451539)
        ·
          refine ⟨4440712827320596955177309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960475218213731303451539 4440712827320596955177309)
          ·
            refine ⟨1665267310245223858191491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4440712827320596955177309 1665267310245223858191491)
            ·
              refine ⟨2497900965367835787287237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665267310245223858191491 2497900965367835787287237)
              ·
                refine ⟨468356431006469210116357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2497900965367835787287237 468356431006469210116357)
                ·
                  refine ⟨87816830813712976896817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468356431006469210116357 87816830813712976896817)
                  ·
                    rfl

theorem cell21_384801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_384801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384801 prefixEnd_384801 := by exact prefixLift 384801
  have htrace : WordTrace (prefixWord ++ tailWord_384801) baseStart_384801 baseEnd_384801 := by
    simpa [prefixWord, tailWord_384801, baseEnd_384801] using wordTrace_append hprefix tailTrace_384801
  have hstable : (prefixWord ++ tailWord_384801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384801).length < 2 ^ (prefixWord ++ tailWord_384801).sum := by decide
  have hdescent : baseEnd_384801 < baseStart_384801 := by decide
  rcases family_descends (prefixWord ++ tailWord_384801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384804 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_384804 : Nat := 118140960795 + 384804 * 2 ^ 59
def prefixEnd_384804 : Nat := 4983230072969 + 3 ^ 40 * 384804 * 2
def baseEnd_384804 : Nat := 87817515454585638346811

theorem tailTrace_384804 : CollatzResearch.WordTrace tailWord_384804 prefixEnd_384804 87817515454585638346811 := by
  unfold tailWord_384804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017477448964151068064733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9356636598618868090752977 7017477448964151068064733)
  ·
    refine ⟨2631554043361556650524275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7017477448964151068064733 2631554043361556650524275)
    ·
      refine ⟨3947331065042334975786413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2631554043361556650524275 3947331065042334975786413)
      ·
        refine ⟨1480249149390875615919905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3947331065042334975786413 1480249149390875615919905)
        ·
          refine ⟨1110186862043156711939929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480249149390875615919905 1110186862043156711939929)
          ·
            refine ⟨832640146532367533954947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110186862043156711939929 832640146532367533954947)
            ·
              refine ⟨1248960219798551300932421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832640146532367533954947 1248960219798551300932421)
              ·
                refine ⟨234180041212228368924829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1248960219798551300932421 234180041212228368924829)
                ·
                  refine ⟨87817515454585638346811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234180041212228368924829 87817515454585638346811)
                  ·
                    rfl

theorem cell21_384804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_384804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384804 prefixEnd_384804 := by exact prefixLift 384804
  have htrace : WordTrace (prefixWord ++ tailWord_384804) baseStart_384804 baseEnd_384804 := by
    simpa [prefixWord, tailWord_384804, baseEnd_384804] using wordTrace_append hprefix tailTrace_384804
  have hstable : (prefixWord ++ tailWord_384804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384804).length < 2 ^ (prefixWord ++ tailWord_384804).sum := by decide
  have hdescent : baseEnd_384804 < baseStart_384804 := by decide
  rcases family_descends (prefixWord ++ tailWord_384804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384838 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_384838 : Nat := 118140960795 + 384838 * 2 ^ 59
def prefixEnd_384838 : Nat := 4983230072969 + 3 ^ 40 * 384838 * 2
def baseEnd_384838 : Nat := 87825274717809134780075

theorem tailTrace_384838 : CollatzResearch.WordTrace tailWord_384838 prefixEnd_384838 87825274717809134780075 := by
  unfold tailWord_384838
  simp only [CollatzResearch.WordTrace]
  refine ⟨438631093118910185714599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9357463319870083961911445 438631093118910185714599)
  ·
    refine ⟨657946639678365278571899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438631093118910185714599 657946639678365278571899)
    ·
      refine ⟨986919959517547917857849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657946639678365278571899 986919959517547917857849)
      ·
        refine ⟨740189969638160938393387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986919959517547917857849 740189969638160938393387)
        ·
          refine ⟨1110284954457241407590081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740189969638160938393387 1110284954457241407590081)
          ·
            refine ⟨832713715842931055692561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110284954457241407590081 832713715842931055692561)
            ·
              refine ⟨624535286882198291769421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832713715842931055692561 624535286882198291769421)
              ·
                refine ⟨234200732580824359413533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624535286882198291769421 234200732580824359413533)
                ·
                  refine ⟨87825274717809134780075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234200732580824359413533 87825274717809134780075)
                  ·
                    rfl

theorem cell21_384838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_384838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384838 prefixEnd_384838 := by exact prefixLift 384838
  have htrace : WordTrace (prefixWord ++ tailWord_384838) baseStart_384838 baseEnd_384838 := by
    simpa [prefixWord, tailWord_384838, baseEnd_384838] using wordTrace_append hprefix tailTrace_384838
  have hstable : (prefixWord ++ tailWord_384838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384838).length < 2 ^ (prefixWord ++ tailWord_384838).sum := by decide
  have hdescent : baseEnd_384838 < baseStart_384838 := by decide
  rcases family_descends (prefixWord ++ tailWord_384838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384863 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 3]
def baseStart_384863 : Nat := 118140960795 + 384863 * 2 ^ 59
def prefixEnd_384863 : Nat := 4983230072969 + 3 ^ 40 * 384863 * 2
def baseEnd_384863 : Nat := 87830980058414646863357

theorem tailTrace_384863 : CollatzResearch.WordTrace tailWord_384863 prefixEnd_384863 87830980058414646863357 := by
  unfold tailWord_384863
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037106804714555212527243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9358071203143036808351495 14037106804714555212527243)
  ·
    refine ⟨21055660207071832818790865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14037106804714555212527243 21055660207071832818790865)
    ·
      refine ⟨15791745155303874614093149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21055660207071832818790865 15791745155303874614093149)
      ·
        refine ⟨5921904433238952980284931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15791745155303874614093149 5921904433238952980284931)
        ·
          refine ⟨8882856649858429470427397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921904433238952980284931 8882856649858429470427397)
          ·
            refine ⟨1665535621848455525705137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8882856649858429470427397 1665535621848455525705137)
            ·
              refine ⟨1249151716386341644278853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665535621848455525705137 1249151716386341644278853)
              ·
                refine ⟨234215946822439058302285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1249151716386341644278853 234215946822439058302285)
                ·
                  refine ⟨87830980058414646863357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234215946822439058302285 87830980058414646863357)
                  ·
                    rfl

theorem cell21_384863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 3].length) (baseStart_384863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384863 prefixEnd_384863 := by exact prefixLift 384863
  have htrace : WordTrace (prefixWord ++ tailWord_384863) baseStart_384863 baseEnd_384863 := by
    simpa [prefixWord, tailWord_384863, baseEnd_384863] using wordTrace_append hprefix tailTrace_384863
  have hstable : (prefixWord ++ tailWord_384863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384863).length < 2 ^ (prefixWord ++ tailWord_384863).sum := by decide
  have hdescent : baseEnd_384863 < baseStart_384863 := by decide
  rcases family_descends (prefixWord ++ tailWord_384863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384877 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_384877 : Nat := 118140960795 + 384877 * 2 ^ 59
def prefixEnd_384877 : Nat := 4983230072969 + 3 ^ 40 * 384877 * 2
def baseEnd_384877 : Nat := 87834175049153733629995

theorem tailTrace_384877 : CollatzResearch.WordTrace tailWord_384877 prefixEnd_384877 87834175049153733629995 := by
  unfold tailWord_384877
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037617426663835603536885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9358411617775890402357923 14037617426663835603536885)
  ·
    refine ⟨1316026633749734587831583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14037617426663835603536885 1316026633749734587831583)
    ·
      refine ⟨1974039950624601881747375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316026633749734587831583 1974039950624601881747375)
      ·
        refine ⟨2961059925936902822621063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974039950624601881747375 2961059925936902822621063)
        ·
          refine ⟨4441589888905354233931595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961059925936902822621063 4441589888905354233931595)
          ·
            refine ⟨6662384833358031350897393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441589888905354233931595 6662384833358031350897393)
            ·
              refine ⟨4996788625018523513173045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6662384833358031350897393 4996788625018523513173045)
              ·
                refine ⟨468448933595486579359973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4996788625018523513173045 468448933595486579359973)
                ·
                  refine ⟨87834175049153733629995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468448933595486579359973 87834175049153733629995)
                  ·
                    rfl

theorem cell21_384877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_384877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384877 prefixEnd_384877 := by exact prefixLift 384877
  have htrace : WordTrace (prefixWord ++ tailWord_384877) baseStart_384877 baseEnd_384877 := by
    simpa [prefixWord, tailWord_384877, baseEnd_384877] using wordTrace_append hprefix tailTrace_384877
  have hstable : (prefixWord ++ tailWord_384877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384877).length < 2 ^ (prefixWord ++ tailWord_384877).sum := by decide
  have hdescent : baseEnd_384877 < baseStart_384877 := by decide
  rcases family_descends (prefixWord ++ tailWord_384877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384894 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_384894 : Nat := 118140960795 + 384894 * 2 ^ 59
def prefixEnd_384894 : Nat := 4983230072969 + 3 ^ 40 * 384894 * 2
def baseEnd_384894 : Nat := 87838054680765481846627

theorem tailTrace_384894 : CollatzResearch.WordTrace tailWord_384894 prefixEnd_384894 87838054680765481846627 := by
  unfold tailWord_384894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754779683450280938363217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9358824978401498337937157 1754779683450280938363217)
  ·
    refine ⟨1316084762587710703772413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1754779683450280938363217 1316084762587710703772413)
    ·
      refine ⟨493531785970391513914655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1316084762587710703772413 493531785970391513914655)
      ·
        refine ⟨740297678955587270871983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493531785970391513914655 740297678955587270871983)
        ·
          refine ⟨1110446518433380906307975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740297678955587270871983 1110446518433380906307975)
          ·
            refine ⟨1665669777650071359461963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110446518433380906307975 1665669777650071359461963)
            ·
              refine ⟨2498504666475107039192945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665669777650071359461963 2498504666475107039192945)
              ·
                refine ⟨1873878499856330279394709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498504666475107039192945 1873878499856330279394709)
                ·
                  refine ⟨87838054680765481846627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1873878499856330279394709 87838054680765481846627)
                  ·
                    rfl

theorem cell21_384894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_384894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_384894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_384894 prefixEnd_384894 := by exact prefixLift 384894
  have htrace : WordTrace (prefixWord ++ tailWord_384894) baseStart_384894 baseEnd_384894 := by
    simpa [prefixWord, tailWord_384894, baseEnd_384894] using wordTrace_append hprefix tailTrace_384894
  have hstable : (prefixWord ++ tailWord_384894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384894).length < 2 ^ (prefixWord ++ tailWord_384894).sum := by decide
  have hdescent : baseEnd_384894 < baseStart_384894 := by decide
  rcases family_descends (prefixWord ++ tailWord_384894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385029 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_385029 : Nat := 118140960795 + 385029 * 2 ^ 59
def prefixEnd_385029 : Nat := 4983230072969 + 3 ^ 40 * 385029 * 2
def baseEnd_385029 : Nat := 87868863520035247096351

theorem tailTrace_385029 : CollatzResearch.WordTrace tailWord_385029 prefixEnd_385029 87868863520035247096351 := by
  unfold tailWord_385029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14043161322113165563070141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9362107548075443708713427 14043161322113165563070141)
  ·
    refine ⟨5266185495792437086151303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14043161322113165563070141 5266185495792437086151303)
    ·
      refine ⟨7899278243688655629226955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266185495792437086151303 7899278243688655629226955)
      ·
        refine ⟨11848917365532983443840433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899278243688655629226955 11848917365532983443840433)
        ·
          refine ⟨8886688024149737582880325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11848917365532983443840433 8886688024149737582880325)
          ·
            refine ⟨1666254004528075796790061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8886688024149737582880325 1666254004528075796790061)
            ·
              refine ⟨624845251698028423796273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666254004528075796790061 624845251698028423796273)
              ·
                refine ⟨468633938773521317847205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624845251698028423796273 468633938773521317847205)
                ·
                  refine ⟨87868863520035247096351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468633938773521317847205 87868863520035247096351)
                  ·
                    rfl

theorem cell21_385029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_385029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385029 prefixEnd_385029 := by exact prefixLift 385029
  have htrace : WordTrace (prefixWord ++ tailWord_385029) baseStart_385029 baseEnd_385029 := by
    simpa [prefixWord, tailWord_385029, baseEnd_385029] using wordTrace_append hprefix tailTrace_385029
  have hstable : (prefixWord ++ tailWord_385029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385029).length < 2 ^ (prefixWord ++ tailWord_385029).sum := by decide
  have hdescent : baseEnd_385029 < baseStart_385029 := by decide
  rcases family_descends (prefixWord ++ tailWord_385029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385060 : List Nat := [2, 3, 1, 4, 2, 1, 1, 7]
def baseStart_385060 : Nat := 118140960795 + 385060 * 2 ^ 59
def prefixEnd_385060 : Nat := 4983230072969 + 3 ^ 40 * 385060 * 2
def baseEnd_385060 : Nat := 29291979380795360693207

theorem tailTrace_385060 : CollatzResearch.WordTrace tailWord_385060 prefixEnd_385060 29291979380795360693207 := by
  unfold tailWord_385060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022145992500428928724317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9362861323333905238299089 7022145992500428928724317)
  ·
    refine ⟨2633304747187660848271619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7022145992500428928724317 2633304747187660848271619)
    ·
      refine ⟨3949957120781491272407429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633304747187660848271619 3949957120781491272407429)
      ·
        refine ⟨740616960146529613576393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3949957120781491272407429 740616960146529613576393)
        ·
          refine ⟨555462720109897210182295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740616960146529613576393 555462720109897210182295)
          ·
            refine ⟨833194080164845815273443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555462720109897210182295 833194080164845815273443)
            ·
              refine ⟨1249791120247268722910165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833194080164845815273443 1249791120247268722910165)
              ·
                refine ⟨29291979380795360693207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1249791120247268722910165 29291979380795360693207)
                ·
                  rfl

theorem cell21_385060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_385060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385060 prefixEnd_385060 := by exact prefixLift 385060
  have htrace : WordTrace (prefixWord ++ tailWord_385060) baseStart_385060 baseEnd_385060 := by
    simpa [prefixWord, tailWord_385060, baseEnd_385060] using wordTrace_append hprefix tailTrace_385060
  have hstable : (prefixWord ++ tailWord_385060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385060).length < 2 ^ (prefixWord ++ tailWord_385060).sum := by decide
  have hdescent : baseEnd_385060 < baseStart_385060 := by decide
  rcases family_descends (prefixWord ++ tailWord_385060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385088 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_385088 : Nat := 118140960795 + 385088 * 2 ^ 59
def prefixEnd_385088 : Nat := 4983230072969 + 3 ^ 40 * 385088 * 2
def baseEnd_385088 : Nat := 87882328123864255612897

theorem tailTrace_385088 : CollatzResearch.WordTrace tailWord_385088 prefixEnd_385088 87882328123864255612897 := by
  unfold tailWord_385088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022656614449709319733959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9363542152599612426311945 7022656614449709319733959)
  ·
    refine ⟨10533984921674563979600939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022656614449709319733959 10533984921674563979600939)
    ·
      refine ⟨15800977382511845969401409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10533984921674563979600939 15800977382511845969401409)
      ·
        refine ⟨11850733036883884477051057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15800977382511845969401409 11850733036883884477051057)
        ·
          refine ⟨8888049777662913357788293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11850733036883884477051057 8888049777662913357788293)
          ·
            refine ⟨1666509333311796254585305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8888049777662913357788293 1666509333311796254585305)
            ·
              refine ⟨1249881999983847190938979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666509333311796254585305 1249881999983847190938979)
              ·
                refine ⟨1874822999975770786408469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249881999983847190938979 1874822999975770786408469)
                ·
                  refine ⟨87882328123864255612897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1874822999975770786408469 87882328123864255612897)
                  ·
                    rfl

theorem cell21_385088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_385088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385088 prefixEnd_385088 := by exact prefixLift 385088
  have htrace : WordTrace (prefixWord ++ tailWord_385088) baseStart_385088 baseEnd_385088 := by
    simpa [prefixWord, tailWord_385088, baseEnd_385088] using wordTrace_append hprefix tailTrace_385088
  have hstable : (prefixWord ++ tailWord_385088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385088).length < 2 ^ (prefixWord ++ tailWord_385088).sum := by decide
  have hdescent : baseEnd_385088 < baseStart_385088 := by decide
  rcases family_descends (prefixWord ++ tailWord_385088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385153 : List Nat := [1, 2, 4, 2, 4, 1, 1, 6]
def baseStart_385153 : Nat := 118140960795 + 385153 * 2 ^ 59
def prefixEnd_385153 : Nat := 4983230072969 + 3 ^ 40 * 385153 * 2
def baseEnd_385153 : Nat := 29299054003146195676477

theorem tailTrace_385153 : CollatzResearch.WordTrace tailWord_385153 prefixEnd_385153 29299054003146195676477 := by
  unfold tailWord_385153
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047683973663934740584113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9365122649109289827056075 14047683973663934740584113)
  ·
    refine ⟨10535762980247951055438085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14047683973663934740584113 10535762980247951055438085)
    ·
      refine ⟨1975455558796490822894641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10535762980247951055438085 1975455558796490822894641)
      ·
        refine ⟨1481591669097368117170981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1975455558796490822894641 1481591669097368117170981)
        ·
          refine ⟨277798437955756521969559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1481591669097368117170981 277798437955756521969559)
          ·
            refine ⟨416697656933634782954339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277798437955756521969559 416697656933634782954339)
            ·
              refine ⟨625046485400452174431509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416697656933634782954339 625046485400452174431509)
              ·
                refine ⟨29299054003146195676477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 625046485400452174431509 29299054003146195676477)
                ·
                  rfl

theorem cell21_385153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 6].length) (baseStart_385153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385153 prefixEnd_385153 := by exact prefixLift 385153
  have htrace : WordTrace (prefixWord ++ tailWord_385153) baseStart_385153 baseEnd_385153 := by
    simpa [prefixWord, tailWord_385153, baseEnd_385153] using wordTrace_append hprefix tailTrace_385153
  have hstable : (prefixWord ++ tailWord_385153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385153).length < 2 ^ (prefixWord ++ tailWord_385153).sum := by decide
  have hdescent : baseEnd_385153 < baseStart_385153 := by decide
  rcases family_descends (prefixWord ++ tailWord_385153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385240 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_385240 : Nat := 118140960795 + 385240 * 2 ^ 59
def prefixEnd_385240 : Nat := 4983230072969 + 3 ^ 40 * 385240 * 2
def baseEnd_385240 : Nat := 87917016594745769079253

theorem tailTrace_385240 : CollatzResearch.WordTrace tailWord_385240 prefixEnd_385240 87917016594745769079253 := by
  unfold tailWord_385240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025428562174374299500587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9367238082899165732667449 7025428562174374299500587)
  ·
    refine ⟨10538142843261561449250881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7025428562174374299500587 10538142843261561449250881)
    ·
      refine ⟨7903607132446171086938161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538142843261561449250881 7903607132446171086938161)
      ·
        refine ⟨5927705349334628315203621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7903607132446171086938161 5927705349334628315203621)
        ·
          refine ⟨1111444753000242809100679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5927705349334628315203621 1111444753000242809100679)
          ·
            refine ⟨1667167129500364213651019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111444753000242809100679 1667167129500364213651019)
            ·
              refine ⟨2500750694250546320476529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667167129500364213651019 2500750694250546320476529)
              ·
                refine ⟨1875563020687909740357397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500750694250546320476529 1875563020687909740357397)
                ·
                  refine ⟨87917016594745769079253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1875563020687909740357397 87917016594745769079253)
                  ·
                    rfl

theorem cell21_385240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_385240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385240 prefixEnd_385240 := by exact prefixLift 385240
  have htrace : WordTrace (prefixWord ++ tailWord_385240) baseStart_385240 baseEnd_385240 := by
    simpa [prefixWord, tailWord_385240, baseEnd_385240] using wordTrace_append hprefix tailTrace_385240
  have hstable : (prefixWord ++ tailWord_385240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385240).length < 2 ^ (prefixWord ++ tailWord_385240).sum := by decide
  have hdescent : baseEnd_385240 < baseStart_385240 := by decide
  rcases family_descends (prefixWord ++ tailWord_385240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385274 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_385274 : Nat := 118140960795 + 385274 * 2 ^ 59
def prefixEnd_385274 : Nat := 4983230072969 + 3 ^ 40 * 385274 * 2
def baseEnd_385274 : Nat := 87924775857969265512517

theorem tailTrace_385274 : CollatzResearch.WordTrace tailWord_385274 prefixEnd_385274 87924775857969265512517 := by
  unfold tailWord_385274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513024301556393101434719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9368064804150381603825917 3513024301556393101434719)
  ·
    refine ⟨5269536452334589652152079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3513024301556393101434719 5269536452334589652152079)
    ·
      refine ⟨7904304678501884478228119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269536452334589652152079 7904304678501884478228119)
      ·
        refine ⟨11856457017752826717342179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904304678501884478228119 11856457017752826717342179)
        ·
          refine ⟨17784685526629240076013269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856457017752826717342179 17784685526629240076013269)
          ·
            refine ⟨416828567030372814281561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17784685526629240076013269 416828567030372814281561)
            ·
              refine ⟨312621425272779610711171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416828567030372814281561 312621425272779610711171)
              ·
                refine ⟨468932137909169416066757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312621425272779610711171 468932137909169416066757)
                ·
                  refine ⟨87924775857969265512517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468932137909169416066757 87924775857969265512517)
                  ·
                    rfl

theorem cell21_385274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_385274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385274 prefixEnd_385274 := by exact prefixLift 385274
  have htrace : WordTrace (prefixWord ++ tailWord_385274) baseStart_385274 baseEnd_385274 := by
    simpa [prefixWord, tailWord_385274, baseEnd_385274] using wordTrace_append hprefix tailTrace_385274
  have hstable : (prefixWord ++ tailWord_385274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385274).length < 2 ^ (prefixWord ++ tailWord_385274).sum := by decide
  have hdescent : baseEnd_385274 < baseStart_385274 := by decide
  rcases family_descends (prefixWord ++ tailWord_385274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385299 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_385299 : Nat := 118140960795 + 385299 * 2 ^ 59
def prefixEnd_385299 : Nat := 4983230072969 + 3 ^ 40 * 385299 * 2
def baseEnd_385299 : Nat := 87930481198574777595799

theorem tailTrace_385299 : CollatzResearch.WordTrace tailWord_385299 prefixEnd_385299 87930481198574777595799 := by
  unfold tailWord_385299
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053009031135001675398951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9368672687423334450265967 14053009031135001675398951)
  ·
    refine ⟨21079513546702502513098427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14053009031135001675398951 21079513546702502513098427)
    ·
      refine ⟨31619270320053753769647641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21079513546702502513098427 31619270320053753769647641)
      ·
        refine ⟨23714452740040315327235731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31619270320053753769647641 23714452740040315327235731)
        ·
          refine ⟨35571679110060472990853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23714452740040315327235731 35571679110060472990853597)
          ·
            refine ⟨13339379666272677371570099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35571679110060472990853597 13339379666272677371570099)
            ·
              refine ⟨20009069499409016057355149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13339379666272677371570099 20009069499409016057355149)
              ·
                refine ⟨7503401062278381021508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20009069499409016057355149 7503401062278381021508181)
                ·
                  refine ⟨87930481198574777595799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7503401062278381021508181 87930481198574777595799)
                  ·
                    rfl

theorem cell21_385299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_385299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385299 prefixEnd_385299 := by exact prefixLift 385299
  have htrace : WordTrace (prefixWord ++ tailWord_385299) baseStart_385299 baseEnd_385299 := by
    simpa [prefixWord, tailWord_385299, baseEnd_385299] using wordTrace_append hprefix tailTrace_385299
  have hstable : (prefixWord ++ tailWord_385299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385299).length < 2 ^ (prefixWord ++ tailWord_385299).sum := by decide
  have hdescent : baseEnd_385299 < baseStart_385299 := by decide
  rcases family_descends (prefixWord ++ tailWord_385299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385378 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_385378 : Nat := 118140960795 + 385378 * 2 ^ 59
def prefixEnd_385378 : Nat := 4983230072969 + 3 ^ 40 * 385378 * 2
def baseEnd_385378 : Nat := 87948510074888195778971

theorem tailTrace_385378 : CollatzResearch.WordTrace tailWord_385378 prefixEnd_385378 87948510074888195778971 := by
  unfold tailWord_385378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513972599462199541881197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9370593598565865445016525 3513972599462199541881197)
  ·
    refine ⟨1317739724798324828205449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3513972599462199541881197 1317739724798324828205449)
    ·
      refine ⟨988304793598743621154087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1317739724798324828205449 988304793598743621154087)
      ·
        refine ⟨1482457190398115431731131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988304793598743621154087 1482457190398115431731131)
        ·
          refine ⟨2223685785597173147596697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482457190398115431731131 2223685785597173147596697)
          ·
            refine ⟨1667764339197879860697523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223685785597173147596697 1667764339197879860697523)
            ·
              refine ⟨2501646508796819791046285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667764339197879860697523 2501646508796819791046285)
              ·
                refine ⟨938117440798807421642357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2501646508796819791046285 938117440798807421642357)
                ·
                  refine ⟨87948510074888195778971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 938117440798807421642357 87948510074888195778971)
                  ·
                    rfl

theorem cell21_385378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_385378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385378 prefixEnd_385378 := by exact prefixLift 385378
  have htrace : WordTrace (prefixWord ++ tailWord_385378) baseStart_385378 baseEnd_385378 := by
    simpa [prefixWord, tailWord_385378, baseEnd_385378] using wordTrace_append hprefix tailTrace_385378
  have hstable : (prefixWord ++ tailWord_385378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385378).length < 2 ^ (prefixWord ++ tailWord_385378).sum := by decide
  have hdescent : baseEnd_385378 < baseStart_385378 := by decide
  rcases family_descends (prefixWord ++ tailWord_385378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385398 : List Nat := [5, 1, 1, 4, 1, 2, 2, 5]
def baseStart_385398 : Nat := 118140960795 + 385398 * 2 ^ 59
def prefixEnd_385398 : Nat := 4983230072969 + 3 ^ 40 * 385398 * 2
def baseEnd_385398 : Nat := 29317691449124201815199

theorem tailTrace_385398 : CollatzResearch.WordTrace tailWord_385398 prefixEnd_385398 29317691449124201815199 := by
  unfold tailWord_385398
  simp only [CollatzResearch.WordTrace]
  refine ⟨878538741111021348953303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9371079905184227722168565 878538741111021348953303)
  ·
    refine ⟨1317808111666532023429955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 878538741111021348953303 1317808111666532023429955)
    ·
      refine ⟨1976712167499798035144933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317808111666532023429955 1976712167499798035144933)
      ·
        refine ⟨370633531406212131589675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1976712167499798035144933 370633531406212131589675)
        ·
          refine ⟨555950297109318197384513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370633531406212131589675 555950297109318197384513)
          ·
            refine ⟨416962722831988648038385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555950297109318197384513 416962722831988648038385)
            ·
              refine ⟨312722042123991486028789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416962722831988648038385 312722042123991486028789)
              ·
                refine ⟨29317691449124201815199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312722042123991486028789 29317691449124201815199)
                ·
                  rfl

theorem cell21_385398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_385398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385398 prefixEnd_385398 := by exact prefixLift 385398
  have htrace : WordTrace (prefixWord ++ tailWord_385398) baseStart_385398 baseEnd_385398 := by
    simpa [prefixWord, tailWord_385398, baseEnd_385398] using wordTrace_append hprefix tailTrace_385398
  have hstable : (prefixWord ++ tailWord_385398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385398).length < 2 ^ (prefixWord ++ tailWord_385398).sum := by decide
  have hdescent : baseEnd_385398 < baseStart_385398 := by decide
  rcases family_descends (prefixWord ++ tailWord_385398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385654 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_385654 : Nat := 118140960795 + 385654 * 2 ^ 59
def prefixEnd_385654 : Nat := 4983230072969 + 3 ^ 40 * 385654 * 2
def baseEnd_385654 : Nat := 88011497035173049178407

theorem tailTrace_385654 : CollatzResearch.WordTrace tailWord_385654 prefixEnd_385654 88011497035173049178407 := by
  unfold tailWord_385654
  simp only [CollatzResearch.WordTrace]
  refine ⟨879122309053056081535751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9377304629899264869714677 879122309053056081535751)
  ·
    refine ⟨1318683463579584122303627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879122309053056081535751 1318683463579584122303627)
    ·
      refine ⟨1978025195369376183455441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318683463579584122303627 1978025195369376183455441)
      ·
        refine ⟨1483518896527032137591581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978025195369376183455441 1483518896527032137591581)
        ·
          refine ⟨556319586197637051596843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483518896527032137591581 556319586197637051596843)
          ·
            refine ⟨834479379296455577395265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556319586197637051596843 834479379296455577395265)
            ·
              refine ⟨625859534472341683046449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834479379296455577395265 625859534472341683046449)
              ·
                refine ⟨469394650854256262284837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625859534472341683046449 469394650854256262284837)
                ·
                  refine ⟨88011497035173049178407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469394650854256262284837 88011497035173049178407)
                  ·
                    rfl

theorem cell21_385654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_385654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385654 prefixEnd_385654 := by exact prefixLift 385654
  have htrace : WordTrace (prefixWord ++ tailWord_385654) baseStart_385654 baseEnd_385654 := by
    simpa [prefixWord, tailWord_385654, baseEnd_385654] using wordTrace_append hprefix tailTrace_385654
  have hstable : (prefixWord ++ tailWord_385654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385654).length < 2 ^ (prefixWord ++ tailWord_385654).sum := by decide
  have hdescent : baseEnd_385654 < baseStart_385654 := by decide
  rcases family_descends (prefixWord ++ tailWord_385654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385665 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_385665 : Nat := 118140960795 + 385665 * 2 ^ 59
def prefixEnd_385665 : Nat := 4983230072969 + 3 ^ 40 * 385665 * 2
def baseEnd_385665 : Nat := 88014007385039474495051

theorem tailTrace_385665 : CollatzResearch.WordTrace tailWord_385665 prefixEnd_385665 88014007385039474495051 := by
  unfold tailWord_385665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14066358147809046183222449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9377572098539364122148299 14066358147809046183222449)
  ·
    refine ⟨10549768610856784637416837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14066358147809046183222449 10549768610856784637416837)
    ·
      refine ⟨1978081614535647119515657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10549768610856784637416837 1978081614535647119515657)
      ·
        refine ⟨1483561210901735339636743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978081614535647119515657 1483561210901735339636743)
        ·
          refine ⟨2225341816352603009455115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483561210901735339636743 2225341816352603009455115)
          ·
            refine ⟨3338012724528904514182673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225341816352603009455115 3338012724528904514182673)
            ·
              refine ⟨2503509543396678385637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338012724528904514182673 2503509543396678385637005)
              ·
                refine ⟨938816078773754394613877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2503509543396678385637005 938816078773754394613877)
                ·
                  refine ⟨88014007385039474495051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 938816078773754394613877 88014007385039474495051)
                  ·
                    rfl

theorem cell21_385665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_385665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385665 prefixEnd_385665 := by exact prefixLift 385665
  have htrace : WordTrace (prefixWord ++ tailWord_385665) baseStart_385665 baseEnd_385665 := by
    simpa [prefixWord, tailWord_385665, baseEnd_385665] using wordTrace_append hprefix tailTrace_385665
  have hstable : (prefixWord ++ tailWord_385665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385665).length < 2 ^ (prefixWord ++ tailWord_385665).sum := by decide
  have hdescent : baseEnd_385665 < baseStart_385665 := by decide
  rcases family_descends (prefixWord ++ tailWord_385665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385682 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_385682 : Nat := 118140960795 + 385682 * 2 ^ 59
def prefixEnd_385682 : Nat := 4983230072969 + 3 ^ 40 * 385682 * 2
def baseEnd_385682 : Nat := 88017887016651222711683

theorem tailTrace_385682 : CollatzResearch.WordTrace tailWord_385682 prefixEnd_385682 88017887016651222711683 := by
  unfold tailWord_385682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516744547186864521647825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9377985459164972057727533 3516744547186864521647825)
  ·
    refine ⟨2637558410390148391235869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3516744547186864521647825 2637558410390148391235869)
    ·
      refine ⟨989084403896305646713451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2637558410390148391235869 989084403896305646713451)
      ·
        refine ⟨1483626605844458470070177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989084403896305646713451 1483626605844458470070177)
        ·
          refine ⟨1112719954383343852552633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483626605844458470070177 1112719954383343852552633)
          ·
            refine ⟨834539965787507889414475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112719954383343852552633 834539965787507889414475)
            ·
              refine ⟨1251809948681261834121713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834539965787507889414475 1251809948681261834121713)
              ·
                refine ⟨938857461510946375591285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251809948681261834121713 938857461510946375591285)
                ·
                  refine ⟨88017887016651222711683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 938857461510946375591285 88017887016651222711683)
                  ·
                    rfl

theorem cell21_385682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_385682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385682 prefixEnd_385682 := by exact prefixLift 385682
  have htrace : WordTrace (prefixWord ++ tailWord_385682) baseStart_385682 baseEnd_385682 := by
    simpa [prefixWord, tailWord_385682, baseEnd_385682] using wordTrace_append hprefix tailTrace_385682
  have hstable : (prefixWord ++ tailWord_385682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385682).length < 2 ^ (prefixWord ++ tailWord_385682).sum := by decide
  have hdescent : baseEnd_385682 < baseStart_385682 := by decide
  rcases family_descends (prefixWord ++ tailWord_385682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385713 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 6]
def baseStart_385713 : Nat := 118140960795 + 385713 * 2 ^ 59
def prefixEnd_385713 : Nat := 4983230072969 + 3 ^ 40 * 385713 * 2
def baseEnd_385713 : Nat := 88024961639002057694953

theorem tailTrace_385713 : CollatzResearch.WordTrace tailWord_385713 prefixEnd_385713 88024961639002057694953 := by
  unfold tailWord_385713
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068108851635150380969793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9378739234423433587313195 14068108851635150380969793)
  ·
    refine ⟨10551081638726362785727345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14068108851635150380969793 10551081638726362785727345)
    ·
      refine ⟨7913311229044772089295509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10551081638726362785727345 7913311229044772089295509)
      ·
        refine ⟨370936463861473691685727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7913311229044772089295509 370936463861473691685727)
        ·
          refine ⟨556404695792210537528591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370936463861473691685727 556404695792210537528591)
          ·
            refine ⟨834607043688315806292887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556404695792210537528591 834607043688315806292887)
            ·
              refine ⟨1251910565532473709439331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834607043688315806292887 1251910565532473709439331)
              ·
                refine ⟨1877865848298710564158997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251910565532473709439331 1877865848298710564158997)
                ·
                  refine ⟨88024961639002057694953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1877865848298710564158997 88024961639002057694953)
                  ·
                    rfl

theorem cell21_385713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_385713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385713 prefixEnd_385713 := by exact prefixLift 385713
  have htrace : WordTrace (prefixWord ++ tailWord_385713) baseStart_385713 baseEnd_385713 := by
    simpa [prefixWord, tailWord_385713, baseEnd_385713] using wordTrace_append hprefix tailTrace_385713
  have hstable : (prefixWord ++ tailWord_385713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385713).length < 2 ^ (prefixWord ++ tailWord_385713).sum := by decide
  have hdescent : baseEnd_385713 < baseStart_385713 := by decide
  rcases family_descends (prefixWord ++ tailWord_385713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385769 : List Nat := [1, 2, 1, 1, 1, 2, 13]
def baseStart_385769 : Nat := 118140960795 + 385769 * 2 ^ 59
def prefixEnd_385769 : Nat := 4983230072969 + 3 ^ 40 * 385769 * 2
def baseEnd_385769 : Nat := 9781971289106489417945

theorem tailTrace_385769 : CollatzResearch.WordTrace tailWord_385769 prefixEnd_385769 9781971289106489417945 := by
  unfold tailWord_385769
  simp only [CollatzResearch.WordTrace]
  refine ⟨14070151339432271945008361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9380100892954847963338907 14070151339432271945008361)
  ·
    refine ⟨10552613504574203958756271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14070151339432271945008361 10552613504574203958756271)
    ·
      refine ⟨15828920256861305938134407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552613504574203958756271 15828920256861305938134407)
      ·
        refine ⟨23743380385291958907201611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15828920256861305938134407 23743380385291958907201611)
        ·
          refine ⟨35615070577937938360802417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23743380385291958907201611 35615070577937938360802417)
          ·
            refine ⟨26711302933453453770601813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35615070577937938360802417 26711302933453453770601813)
            ·
              refine ⟨9781971289106489417945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 26711302933453453770601813 9781971289106489417945)
              ·
                rfl

theorem cell21_385769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 13].length) (baseStart_385769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385769 prefixEnd_385769 := by exact prefixLift 385769
  have htrace : WordTrace (prefixWord ++ tailWord_385769) baseStart_385769 baseEnd_385769 := by
    simpa [prefixWord, tailWord_385769, baseEnd_385769] using wordTrace_append hprefix tailTrace_385769
  have hstable : (prefixWord ++ tailWord_385769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385769).length < 2 ^ (prefixWord ++ tailWord_385769).sum := by decide
  have hdescent : baseEnd_385769 < baseStart_385769 := by decide
  rcases family_descends (prefixWord ++ tailWord_385769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385775 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 3]
def baseStart_385775 : Nat := 118140960795 + 385775 * 2 ^ 59
def prefixEnd_385775 : Nat := 4983230072969 + 3 ^ 40 * 385775 * 2
def baseEnd_385775 : Nat := 88039110883703727661493

theorem tailTrace_385775 : CollatzResearch.WordTrace tailWord_385775 prefixEnd_385775 88039110883703727661493 := by
  unfold tailWord_385775
  simp only [CollatzResearch.WordTrace]
  refine ⟨14070370177410534969726779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9380246784940356646484519 14070370177410534969726779)
  ·
    refine ⟨21105555266115802454590169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14070370177410534969726779 21105555266115802454590169)
    ·
      refine ⟨15829166449586851840942627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21105555266115802454590169 15829166449586851840942627)
      ·
        refine ⟨23743749674380277761413941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15829166449586851840942627 23743749674380277761413941)
        ·
          refine ⟨2225976531973151040132557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23743749674380277761413941 2225976531973151040132557)
          ·
            refine ⟨834741199489931640049709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2225976531973151040132557 834741199489931640049709)
            ·
              refine ⟨313027949808724365018641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 834741199489931640049709 313027949808724365018641)
              ·
                refine ⟨234770962356543273763981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313027949808724365018641 234770962356543273763981)
                ·
                  refine ⟨88039110883703727661493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234770962356543273763981 88039110883703727661493)
                  ·
                    rfl

theorem cell21_385775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3].length) (baseStart_385775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385775 prefixEnd_385775 := by exact prefixLift 385775
  have htrace : WordTrace (prefixWord ++ tailWord_385775) baseStart_385775 baseEnd_385775 := by
    simpa [prefixWord, tailWord_385775, baseEnd_385775] using wordTrace_append hprefix tailTrace_385775
  have hstable : (prefixWord ++ tailWord_385775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385775).length < 2 ^ (prefixWord ++ tailWord_385775).sum := by decide
  have hdescent : baseEnd_385775 < baseStart_385775 := by decide
  rcases family_descends (prefixWord ++ tailWord_385775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385781 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 4]
def baseStart_385781 : Nat := 118140960795 + 385781 * 2 ^ 59
def prefixEnd_385781 : Nat := 4983230072969 + 3 ^ 40 * 385781 * 2
def baseEnd_385781 : Nat := 88040480165449050561481

theorem tailTrace_385781 : CollatzResearch.WordTrace tailWord_385781 prefixEnd_385781 88040480165449050561481 := by
  unfold tailWord_385781
  simp only [CollatzResearch.WordTrace]
  refine ⟨14070589015388797994445197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9380392676925865329630131 14070589015388797994445197)
  ·
    refine ⟨5276470880770799247916949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14070589015388797994445197 5276470880770799247916949)
    ·
      refine ⟨247334572536131214746107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5276470880770799247916949 247334572536131214746107)
      ·
        refine ⟨371001858804196822119161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247334572536131214746107 371001858804196822119161)
        ·
          refine ⟨278251394103147616589371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371001858804196822119161 278251394103147616589371)
          ·
            refine ⟨417377091154721424884057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278251394103147616589371 417377091154721424884057)
            ·
              refine ⟨313032818366041068663043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417377091154721424884057 313032818366041068663043)
              ·
                refine ⟨469549227549061602994565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313032818366041068663043 469549227549061602994565)
                ·
                  refine ⟨88040480165449050561481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469549227549061602994565 88040480165449050561481)
                  ·
                    rfl

theorem cell21_385781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_385781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385781 prefixEnd_385781 := by exact prefixLift 385781
  have htrace : WordTrace (prefixWord ++ tailWord_385781) baseStart_385781 baseEnd_385781 := by
    simpa [prefixWord, tailWord_385781, baseEnd_385781] using wordTrace_append hprefix tailTrace_385781
  have hstable : (prefixWord ++ tailWord_385781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385781).length < 2 ^ (prefixWord ++ tailWord_385781).sum := by decide
  have hdescent : baseEnd_385781 < baseStart_385781 := by decide
  rcases family_descends (prefixWord ++ tailWord_385781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385837 : List Nat := [1, 5, 3, 2, 1, 2, 1, 6]
def baseStart_385837 : Nat := 118140960795 + 385837 * 2 ^ 59
def prefixEnd_385837 : Nat := 4983230072969 + 3 ^ 40 * 385837 * 2
def baseEnd_385837 : Nat := 29351086709468465876011

theorem tailTrace_385837 : CollatzResearch.WordTrace tailWord_385837 prefixEnd_385837 29351086709468465876011 := by
  unfold tailWord_385837
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072631503185919558483765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381754335457279705655843 14072631503185919558483765)
  ·
    refine ⟨1319309203423679958607853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14072631503185919558483765 1319309203423679958607853)
    ·
      refine ⟨494740951283879984477945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1319309203423679958607853 494740951283879984477945)
      ·
        refine ⟨371055713462909988358459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494740951283879984477945 371055713462909988358459)
        ·
          refine ⟨556583570194364982537689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371055713462909988358459 556583570194364982537689)
          ·
            refine ⟨417437677645773736903267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556583570194364982537689 417437677645773736903267)
            ·
              refine ⟨626156516468660605354901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417437677645773736903267 626156516468660605354901)
              ·
                refine ⟨29351086709468465876011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 626156516468660605354901 29351086709468465876011)
                ·
                  rfl

theorem cell21_385837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 6].length) (baseStart_385837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385837 prefixEnd_385837 := by exact prefixLift 385837
  have htrace : WordTrace (prefixWord ++ tailWord_385837) baseStart_385837 baseEnd_385837 := by
    simpa [prefixWord, tailWord_385837, baseEnd_385837] using wordTrace_append hprefix tailTrace_385837
  have hstable : (prefixWord ++ tailWord_385837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385837).length < 2 ^ (prefixWord ++ tailWord_385837).sum := by decide
  have hdescent : baseEnd_385837 < baseStart_385837 := by decide
  rcases family_descends (prefixWord ++ tailWord_385837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385907 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_385907 : Nat := 118140960795 + 385907 * 2 ^ 59
def prefixEnd_385907 : Nat := 4983230072969 + 3 ^ 40 * 385907 * 2
def baseEnd_385907 : Nat := 88069235082100831461223

theorem tailTrace_385907 : CollatzResearch.WordTrace tailWord_385907 prefixEnd_385907 88069235082100831461223 := by
  unfold tailWord_385907
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075184612932321513531975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383456408621547675687983 14075184612932321513531975)
  ·
    refine ⟨21112776919398482270297963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075184612932321513531975 21112776919398482270297963)
    ·
      refine ⟨31669165379097723405446945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21112776919398482270297963 31669165379097723405446945)
      ·
        refine ⟨23751874034323292554085209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31669165379097723405446945 23751874034323292554085209)
        ·
          refine ⟨17813905525742469415563907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23751874034323292554085209 17813905525742469415563907)
          ·
            refine ⟨26720858288613704123345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17813905525742469415563907 26720858288613704123345861)
            ·
              refine ⟨5010160929115069523127349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26720858288613704123345861 5010160929115069523127349)
              ·
                refine ⟨469702587104537767793189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5010160929115069523127349 469702587104537767793189)
                ·
                  refine ⟨88069235082100831461223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469702587104537767793189 88069235082100831461223)
                  ·
                    rfl

theorem cell21_385907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_385907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385907 prefixEnd_385907 := by exact prefixLift 385907
  have htrace : WordTrace (prefixWord ++ tailWord_385907) baseStart_385907 baseEnd_385907 := by
    simpa [prefixWord, tailWord_385907, baseEnd_385907] using wordTrace_append hprefix tailTrace_385907
  have hstable : (prefixWord ++ tailWord_385907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385907).length < 2 ^ (prefixWord ++ tailWord_385907).sum := by decide
  have hdescent : baseEnd_385907 < baseStart_385907 := by decide
  rcases family_descends (prefixWord ++ tailWord_385907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385910 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_385910 : Nat := 118140960795 + 385910 * 2 ^ 59
def prefixEnd_385910 : Nat := 4983230072969 + 3 ^ 40 * 385910 * 2
def baseEnd_385910 : Nat := 88069919722973492911217

theorem tailTrace_385910 : CollatzResearch.WordTrace tailWord_385910 prefixEnd_385910 88069919722973492911217 := by
  unfold tailWord_385910
  simp only [CollatzResearch.WordTrace]
  refine ⟨879705876995090814118199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9383529354614302017260789 879705876995090814118199)
  ·
    refine ⟨1319558815492636221177299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879705876995090814118199 1319558815492636221177299)
    ·
      refine ⟨1979338223238954331765949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319558815492636221177299 1979338223238954331765949)
      ·
        refine ⟨742251833714607874412231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1979338223238954331765949 742251833714607874412231)
        ·
          refine ⟨1113377750571911811618347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742251833714607874412231 1113377750571911811618347)
          ·
            refine ⟨1670066625857867717427521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113377750571911811618347 1670066625857867717427521)
            ·
              refine ⟨1252549969393400788070641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670066625857867717427521 1252549969393400788070641)
              ·
                refine ⟨939412477045050591052981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252549969393400788070641 939412477045050591052981)
                ·
                  refine ⟨88069919722973492911217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 939412477045050591052981 88069919722973492911217)
                  ·
                    rfl

theorem cell21_385910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_385910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385910 prefixEnd_385910 := by exact prefixLift 385910
  have htrace : WordTrace (prefixWord ++ tailWord_385910) baseStart_385910 baseEnd_385910 := by
    simpa [prefixWord, tailWord_385910, baseEnd_385910] using wordTrace_append hprefix tailTrace_385910
  have hstable : (prefixWord ++ tailWord_385910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385910).length < 2 ^ (prefixWord ++ tailWord_385910).sum := by decide
  have hdescent : baseEnd_385910 < baseStart_385910 := by decide
  rcases family_descends (prefixWord ++ tailWord_385910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385927 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 3]
def baseStart_385927 : Nat := 118140960795 + 385927 * 2 ^ 59
def prefixEnd_385927 : Nat := 4983230072969 + 3 ^ 40 * 385927 * 2
def baseEnd_385927 : Nat := 88073799354585241127849

theorem tailTrace_385927 : CollatzResearch.WordTrace tailWord_385927 prefixEnd_385927 88073799354585241127849 := by
  unfold tailWord_385927
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075914072859864929260035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383942715239909952840023 14075914072859864929260035)
  ·
    refine ⟨21113871109289797393890053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075914072859864929260035 21113871109289797393890053)
    ·
      refine ⟨3958850832991837011354385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21113871109289797393890053 3958850832991837011354385)
      ·
        refine ⟨2969138124743877758515789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3958850832991837011354385 2969138124743877758515789)
        ·
          refine ⟨1113426796778954159443421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2969138124743877758515789 1113426796778954159443421)
          ·
            refine ⟨417535048792107809791283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1113426796778954159443421 417535048792107809791283)
            ·
              refine ⟨626302573188161714686925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417535048792107809791283 626302573188161714686925)
              ·
                refine ⟨234863464945560643007597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 626302573188161714686925 234863464945560643007597)
                ·
                  refine ⟨88073799354585241127849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234863464945560643007597 88073799354585241127849)
                  ·
                    rfl

theorem cell21_385927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3].length) (baseStart_385927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_385927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_385927 prefixEnd_385927 := by exact prefixLift 385927
  have htrace : WordTrace (prefixWord ++ tailWord_385927) baseStart_385927 baseEnd_385927 := by
    simpa [prefixWord, tailWord_385927, baseEnd_385927] using wordTrace_append hprefix tailTrace_385927
  have hstable : (prefixWord ++ tailWord_385927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385927).length < 2 ^ (prefixWord ++ tailWord_385927).sum := by decide
  have hdescent : baseEnd_385927 < baseStart_385927 := by decide
  rcases family_descends (prefixWord ++ tailWord_385927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386059 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_386059 : Nat := 118140960795 + 386059 * 2 ^ 59
def prefixEnd_386059 : Nat := 4983230072969 + 3 ^ 40 * 386059 * 2
def baseEnd_386059 : Nat := 88103923552982344927579

theorem tailTrace_386059 : CollatzResearch.WordTrace tailWord_386059 prefixEnd_386059 88103923552982344927579 := by
  unfold tailWord_386059
  simp only [CollatzResearch.WordTrace]
  refine ⟨14080728508381651473065231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9387152338921100982043487 14080728508381651473065231)
  ·
    refine ⟨21121092762572477209597847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14080728508381651473065231 21121092762572477209597847)
    ·
      refine ⟨31681639143858715814396771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21121092762572477209597847 31681639143858715814396771)
      ·
        refine ⟨47522458715788073721595157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31681639143858715814396771 47522458715788073721595157)
        ·
          refine ⟨2227615252302565955699773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47522458715788073721595157 2227615252302565955699773)
          ·
            refine ⟨835355719613462233387415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2227615252302565955699773 835355719613462233387415)
            ·
              refine ⟨1253033579420193350081123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835355719613462233387415 1253033579420193350081123)
              ·
                refine ⟨1879550369130290025121685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253033579420193350081123 1879550369130290025121685)
                ·
                  refine ⟨88103923552982344927579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1879550369130290025121685 88103923552982344927579)
                  ·
                    rfl

theorem cell21_386059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_386059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386059 prefixEnd_386059 := by exact prefixLift 386059
  have htrace : WordTrace (prefixWord ++ tailWord_386059) baseStart_386059 baseEnd_386059 := by
    simpa [prefixWord, tailWord_386059, baseEnd_386059] using wordTrace_append hprefix tailTrace_386059
  have hstable : (prefixWord ++ tailWord_386059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386059).length < 2 ^ (prefixWord ++ tailWord_386059).sum := by decide
  have hdescent : baseEnd_386059 < baseStart_386059 := by decide
  rcases family_descends (prefixWord ++ tailWord_386059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386062 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_386062 : Nat := 118140960795 + 386062 * 2 ^ 59
def prefixEnd_386062 : Nat := 4983230072969 + 3 ^ 40 * 386062 * 2
def baseEnd_386062 : Nat := 88104608193855006377573

theorem tailTrace_386062 : CollatzResearch.WordTrace tailWord_386062 prefixEnd_386062 88104608193855006377573 := by
  unfold tailWord_386062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760104740921347873178055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9387225284913855323616293 1760104740921347873178055)
  ·
    refine ⟨2640157111382021809767083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760104740921347873178055 2640157111382021809767083)
    ·
      refine ⟨3960235667073032714650625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640157111382021809767083 3960235667073032714650625)
      ·
        refine ⟨2970176750304774535987969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3960235667073032714650625 2970176750304774535987969)
        ·
          refine ⟨2227632562728580901990977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970176750304774535987969 2227632562728580901990977)
          ·
            refine ⟨1670724422046435676493233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2227632562728580901990977 1670724422046435676493233)
            ·
              refine ⟨1253043316534826757369925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670724422046435676493233 1253043316534826757369925)
              ·
                refine ⟨234945621850280017006861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1253043316534826757369925 234945621850280017006861)
                ·
                  refine ⟨88104608193855006377573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234945621850280017006861 88104608193855006377573)
                  ·
                    rfl

theorem cell21_386062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_386062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386062 prefixEnd_386062 := by exact prefixLift 386062
  have htrace : WordTrace (prefixWord ++ tailWord_386062) baseStart_386062 baseEnd_386062 := by
    simpa [prefixWord, tailWord_386062, baseEnd_386062] using wordTrace_append hprefix tailTrace_386062
  have hstable : (prefixWord ++ tailWord_386062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386062).length < 2 ^ (prefixWord ++ tailWord_386062).sum := by decide
  have hdescent : baseEnd_386062 < baseStart_386062 := by decide
  rcases family_descends (prefixWord ++ tailWord_386062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386149 : List Nat := [1, 3, 1, 3, 2, 1, 1, 9]
def baseStart_386149 : Nat := 118140960795 + 386149 * 2 ^ 59
def prefixEnd_386149 : Nat := 4983230072969 + 3 ^ 40 * 386149 * 2
def baseEnd_386149 : Nat := 29374820926387396142465

theorem tailTrace_386149 : CollatzResearch.WordTrace tailWord_386149 prefixEnd_386149 29374820926387396142465 := by
  unfold tailWord_386149
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084011078055596843841501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389340718703731229227667 14084011078055596843841501)
  ·
    refine ⟨5281504154270848816440563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14084011078055596843841501 5281504154270848816440563)
    ·
      refine ⟨7922256231406273224660845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5281504154270848816440563 7922256231406273224660845)
      ·
        refine ⟨2970846086777352459247817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7922256231406273224660845 2970846086777352459247817)
        ·
          refine ⟨2228134565083014344435863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970846086777352459247817 2228134565083014344435863)
          ·
            refine ⟨3342201847624521516653795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228134565083014344435863 3342201847624521516653795)
            ·
              refine ⟨5013302771436782274980693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342201847624521516653795 5013302771436782274980693)
              ·
                refine ⟨29374820926387396142465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5013302771436782274980693 29374820926387396142465)
                ·
                  rfl

theorem cell21_386149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_386149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386149 prefixEnd_386149 := by exact prefixLift 386149
  have htrace : WordTrace (prefixWord ++ tailWord_386149) baseStart_386149 baseEnd_386149 := by
    simpa [prefixWord, tailWord_386149, baseEnd_386149] using wordTrace_append hprefix tailTrace_386149
  have hstable : (prefixWord ++ tailWord_386149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386149).length < 2 ^ (prefixWord ++ tailWord_386149).sum := by decide
  have hdescent : baseEnd_386149 < baseStart_386149 := by decide
  rcases family_descends (prefixWord ++ tailWord_386149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386290 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_386290 : Nat := 118140960795 + 386290 * 2 ^ 59
def prefixEnd_386290 : Nat := 4983230072969 + 3 ^ 40 * 386290 * 2
def baseEnd_386290 : Nat := 88156640900177276577107

theorem tailTrace_386290 : CollatzResearch.WordTrace tailWord_386290 prefixEnd_386290 88156640900177276577107 := by
  unfold tailWord_386290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522288442636194481181081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9392769180363185283149549 3522288442636194481181081)
  ·
    refine ⟨2641716331977145860885811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3522288442636194481181081 2641716331977145860885811)
    ·
      refine ⟨3962574497965718791328717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641716331977145860885811 3962574497965718791328717)
      ·
        refine ⟨1485965436737144546748269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3962574497965718791328717 1485965436737144546748269)
        ·
          refine ⟨557237038776429205030601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1485965436737144546748269 557237038776429205030601)
          ·
            refine ⟨417927779082321903772951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557237038776429205030601 417927779082321903772951)
            ·
              refine ⟨626891668623482855659427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417927779082321903772951 626891668623482855659427)
              ·
                refine ⟨940337502935224283489141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626891668623482855659427 940337502935224283489141)
                ·
                  refine ⟨88156640900177276577107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 940337502935224283489141 88156640900177276577107)
                  ·
                    rfl

theorem cell21_386290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_386290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386290 prefixEnd_386290 := by exact prefixLift 386290
  have htrace : WordTrace (prefixWord ++ tailWord_386290) baseStart_386290 baseEnd_386290 := by
    simpa [prefixWord, tailWord_386290, baseEnd_386290] using wordTrace_append hprefix tailTrace_386290
  have hstable : (prefixWord ++ tailWord_386290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386290).length < 2 ^ (prefixWord ++ tailWord_386290).sum := by decide
  have hdescent : baseEnd_386290 < baseStart_386290 := by decide
  rcases family_descends (prefixWord ++ tailWord_386290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386414 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_386414 : Nat := 118140960795 + 386414 * 2 ^ 59
def prefixEnd_386414 : Nat := 4983230072969 + 3 ^ 40 * 386414 * 2
def baseEnd_386414 : Nat := 88184939389580616510187

theorem tailTrace_386414 : CollatzResearch.WordTrace tailWord_386414 prefixEnd_386414 88184939389580616510187 := by
  unfold tailWord_386414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761709552761943387779787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9395784281397031401492197 1761709552761943387779787)
  ·
    refine ⟨2642564329142915081669681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1761709552761943387779787 2642564329142915081669681)
    ·
      refine ⟨1981923246857186311252261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2642564329142915081669681 1981923246857186311252261)
      ·
        refine ⟨371610608785722433359799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1981923246857186311252261 371610608785722433359799)
        ·
          refine ⟨557415913178583650039699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371610608785722433359799 557415913178583650039699)
          ·
            refine ⟨836123869767875475059549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557415913178583650039699 836123869767875475059549)
            ·
              refine ⟨313546451162953303147331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836123869767875475059549 313546451162953303147331)
              ·
                refine ⟨470319676744429954720997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313546451162953303147331 470319676744429954720997)
                ·
                  refine ⟨88184939389580616510187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470319676744429954720997 88184939389580616510187)
                  ·
                    rfl

theorem cell21_386414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_386414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386414 prefixEnd_386414 := by exact prefixLift 386414
  have htrace : WordTrace (prefixWord ++ tailWord_386414) baseStart_386414 baseEnd_386414 := by
    simpa [prefixWord, tailWord_386414, baseEnd_386414] using wordTrace_append hprefix tailTrace_386414
  have hstable : (prefixWord ++ tailWord_386414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386414).length < 2 ^ (prefixWord ++ tailWord_386414).sum := by decide
  have hdescent : baseEnd_386414 < baseStart_386414 := by decide
  rcases family_descends (prefixWord ++ tailWord_386414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386529 : List Nat := [1, 2, 3, 1, 2, 3, 3, 6]
def baseStart_386529 : Nat := 118140960795 + 386529 * 2 ^ 59
def prefixEnd_386529 : Nat := 4983230072969 + 3 ^ 40 * 386529 * 2
def baseEnd_386529 : Nat := 29403727985455324031095

theorem tailTrace_386529 : CollatzResearch.WordTrace tailWord_386529 prefixEnd_386529 29403727985455324031095 := by
  unfold tailWord_386529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14097870816678921742674641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9398580544452614495116427 14097870816678921742674641)
  ·
    refine ⟨10573403112509191307005981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14097870816678921742674641 10573403112509191307005981)
    ·
      refine ⟨3965026167190946740127243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10573403112509191307005981 3965026167190946740127243)
      ·
        refine ⟨5947539250786420110190865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965026167190946740127243 5947539250786420110190865)
        ·
          refine ⟨4460654438089815082643149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947539250786420110190865 4460654438089815082643149)
          ·
            refine ⟨1672745414283680655991181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4460654438089815082643149 1672745414283680655991181)
            ·
              refine ⟨627279530356380245996693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672745414283680655991181 627279530356380245996693)
              ·
                refine ⟨29403727985455324031095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 627279530356380245996693 29403727985455324031095)
                ·
                  rfl

theorem cell21_386529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_386529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386529 prefixEnd_386529 := by exact prefixLift 386529
  have htrace : WordTrace (prefixWord ++ tailWord_386529) baseStart_386529 baseEnd_386529 := by
    simpa [prefixWord, tailWord_386529, baseEnd_386529] using wordTrace_append hprefix tailTrace_386529
  have hstable : (prefixWord ++ tailWord_386529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386529).length < 2 ^ (prefixWord ++ tailWord_386529).sum := by decide
  have hdescent : baseEnd_386529 < baseStart_386529 := by decide
  rcases family_descends (prefixWord ++ tailWord_386529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386543 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_386543 : Nat := 118140960795 + 386543 * 2 ^ 59
def prefixEnd_386543 : Nat := 4983230072969 + 3 ^ 40 * 386543 * 2
def baseEnd_386543 : Nat := 88214378947105058859923

theorem tailTrace_386543 : CollatzResearch.WordTrace tailWord_386543 prefixEnd_386543 88214378947105058859923 := by
  unfold tailWord_386543
  simp only [CollatzResearch.WordTrace]
  refine ⟨14098381438628202133684283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9398920959085468089122855 14098381438628202133684283)
  ·
    refine ⟨21147572157942303200526425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14098381438628202133684283 21147572157942303200526425)
    ·
      refine ⟨15860679118456727400394819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21147572157942303200526425 15860679118456727400394819)
      ·
        refine ⟨23791018677685091100592229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15860679118456727400394819 23791018677685091100592229)
        ·
          refine ⟨4460816002065954581361043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23791018677685091100592229 4460816002065954581361043)
          ·
            refine ⟨6691224003098931872041565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460816002065954581361043 6691224003098931872041565)
            ·
              refine ⟨2509209001162099452015587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6691224003098931872041565 2509209001162099452015587)
              ·
                refine ⟨3763813501743149178023381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509209001162099452015587 3763813501743149178023381)
                ·
                  refine ⟨88214378947105058859923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3763813501743149178023381 88214378947105058859923)
                  ·
                    rfl

theorem cell21_386543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_386543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386543 prefixEnd_386543 := by exact prefixLift 386543
  have htrace : WordTrace (prefixWord ++ tailWord_386543) baseStart_386543 baseEnd_386543 := by
    simpa [prefixWord, tailWord_386543, baseEnd_386543] using wordTrace_append hprefix tailTrace_386543
  have hstable : (prefixWord ++ tailWord_386543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386543).length < 2 ^ (prefixWord ++ tailWord_386543).sum := by decide
  have hdescent : baseEnd_386543 < baseStart_386543 := by decide
  rcases family_descends (prefixWord ++ tailWord_386543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386566 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_386566 : Nat := 118140960795 + 386566 * 2 ^ 59
def prefixEnd_386566 : Nat := 4983230072969 + 3 ^ 40 * 386566 * 2
def baseEnd_386566 : Nat := 88219627860462129976543

theorem tailTrace_386566 : CollatzResearch.WordTrace tailWord_386566 prefixEnd_386566 88219627860462129976543 := by
  unfold tailWord_386566
  simp only [CollatzResearch.WordTrace]
  refine ⟨440600634923277408180361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9399480211696584707847701 440600634923277408180361)
  ·
    refine ⟨330450476192458056135271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 440600634923277408180361 330450476192458056135271)
    ·
      refine ⟨495675714288687084202907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330450476192458056135271 495675714288687084202907)
      ·
        refine ⟨743513571433030626304361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495675714288687084202907 743513571433030626304361)
        ·
          refine ⟨557635178574772969728271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743513571433030626304361 557635178574772969728271)
          ·
            refine ⟨836452767862159454592407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557635178574772969728271 836452767862159454592407)
            ·
              refine ⟨1254679151793239181888611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836452767862159454592407 1254679151793239181888611)
              ·
                refine ⟨1882018727689858772832917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254679151793239181888611 1882018727689858772832917)
                ·
                  refine ⟨88219627860462129976543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1882018727689858772832917 88219627860462129976543)
                  ·
                    rfl

theorem cell21_386566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_386566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386566 prefixEnd_386566 := by exact prefixLift 386566
  have htrace : WordTrace (prefixWord ++ tailWord_386566) baseStart_386566 baseEnd_386566 := by
    simpa [prefixWord, tailWord_386566, baseEnd_386566] using wordTrace_append hprefix tailTrace_386566
  have hstable : (prefixWord ++ tailWord_386566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386566).length < 2 ^ (prefixWord ++ tailWord_386566).sum := by decide
  have hdescent : baseEnd_386566 < baseStart_386566 := by decide
  rcases family_descends (prefixWord ++ tailWord_386566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386636 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_386636 : Nat := 118140960795 + 386636 * 2 ^ 59
def prefixEnd_386636 : Nat := 4983230072969 + 3 ^ 40 * 386636 * 2
def baseEnd_386636 : Nat := 88235602814157563809733

theorem tailTrace_386636 : CollatzResearch.WordTrace tailWord_386636 prefixEnd_386636 88235602814157563809733 := by
  unfold tailWord_386636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050886713645639508409881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9401182284860852677879841 7050886713645639508409881)
  ·
    refine ⟨5288165035234229631307411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7050886713645639508409881 5288165035234229631307411)
    ·
      refine ⟨7932247552851344446961117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288165035234229631307411 7932247552851344446961117)
      ·
        refine ⟨2974592832319254167610419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7932247552851344446961117 2974592832319254167610419)
        ·
          refine ⟨4461889248478881251415629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974592832319254167610419 4461889248478881251415629)
          ·
            refine ⟨1673208468179580469280861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4461889248478881251415629 1673208468179580469280861)
            ·
              refine ⟨627453175567342675980323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1673208468179580469280861 627453175567342675980323)
              ·
                refine ⟨941179763351014013970485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627453175567342675980323 941179763351014013970485)
                ·
                  refine ⟨88235602814157563809733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941179763351014013970485 88235602814157563809733)
                  ·
                    rfl

theorem cell21_386636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_386636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386636 prefixEnd_386636 := by exact prefixLift 386636
  have htrace : WordTrace (prefixWord ++ tailWord_386636) baseStart_386636 baseEnd_386636 := by
    simpa [prefixWord, tailWord_386636, baseEnd_386636] using wordTrace_append hprefix tailTrace_386636
  have hstable : (prefixWord ++ tailWord_386636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386636).length < 2 ^ (prefixWord ++ tailWord_386636).sum := by decide
  have hdescent : baseEnd_386636 < baseStart_386636 := by decide
  rcases family_descends (prefixWord ++ tailWord_386636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386698 : List Nat := [3, 1, 2, 3, 2, 3, 1, 6]
def baseStart_386698 : Nat := 118140960795 + 386698 * 2 ^ 59
def prefixEnd_386698 : Nat := 4983230072969 + 3 ^ 40 * 386698 * 2
def baseEnd_386698 : Nat := 29416584019619744592091

theorem tailTrace_386698 : CollatzResearch.WordTrace tailWord_386698 prefixEnd_386698 29416584019619744592091 := by
  unfold tailWord_386698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526008688266665901394187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9402689835377775737051165 3526008688266665901394187)
  ·
    refine ⟨5289013032399998852091281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3526008688266665901394187 5289013032399998852091281)
    ·
      refine ⟨3966759774299999139068461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5289013032399998852091281 3966759774299999139068461)
      ·
        refine ⟨1487534915362499677150673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3966759774299999139068461 1487534915362499677150673)
        ·
          refine ⟨1115651186521874757863005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487534915362499677150673 1115651186521874757863005)
          ·
            refine ⟨418369194945703034198627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1115651186521874757863005 418369194945703034198627)
            ·
              refine ⟨627553792418554551297941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418369194945703034198627 627553792418554551297941)
              ·
                refine ⟨29416584019619744592091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 627553792418554551297941 29416584019619744592091)
                ·
                  rfl

theorem cell21_386698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_386698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386698 prefixEnd_386698 := by exact prefixLift 386698
  have htrace : WordTrace (prefixWord ++ tailWord_386698) baseStart_386698 baseEnd_386698 := by
    simpa [prefixWord, tailWord_386698, baseEnd_386698] using wordTrace_append hprefix tailTrace_386698
  have hstable : (prefixWord ++ tailWord_386698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386698).length < 2 ^ (prefixWord ++ tailWord_386698).sum := by decide
  have hdescent : baseEnd_386698 < baseStart_386698 := by decide
  rcases family_descends (prefixWord ++ tailWord_386698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386712 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_386712 : Nat := 118140960795 + 386712 * 2 ^ 59
def prefixEnd_386712 : Nat := 4983230072969 + 3 ^ 40 * 386712 * 2
def baseEnd_386712 : Nat := 88252947049598320542911

theorem tailTrace_386712 : CollatzResearch.WordTrace tailWord_386712 prefixEnd_386712 88252947049598320542911 := by
  unfold tailWord_386712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052272687507971998293195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9403030250010629331057593 7052272687507971998293195)
  ·
    refine ⟨10578409031261957997439793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7052272687507971998293195 10578409031261957997439793)
    ·
      refine ⟨7933806773446468498079845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10578409031261957997439793 7933806773446468498079845)
      ·
        refine ⟨1487588770021212843389971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7933806773446468498079845 1487588770021212843389971)
        ·
          refine ⟨2231383155031819265084957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487588770021212843389971 2231383155031819265084957)
          ·
            refine ⟨836768683136932224406859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2231383155031819265084957 836768683136932224406859)
            ·
              refine ⟨1255153024705398336610289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836768683136932224406859 1255153024705398336610289)
              ·
                refine ⟨941364768529048752457717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255153024705398336610289 941364768529048752457717)
                ·
                  refine ⟨88252947049598320542911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 941364768529048752457717 88252947049598320542911)
                  ·
                    rfl

theorem cell21_386712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_386712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386712 prefixEnd_386712 := by exact prefixLift 386712
  have htrace : WordTrace (prefixWord ++ tailWord_386712) baseStart_386712 baseEnd_386712 := by
    simpa [prefixWord, tailWord_386712, baseEnd_386712] using wordTrace_append hprefix tailTrace_386712
  have hstable : (prefixWord ++ tailWord_386712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386712).length < 2 ^ (prefixWord ++ tailWord_386712).sum := by decide
  have hdescent : baseEnd_386712 < baseStart_386712 := by decide
  rcases family_descends (prefixWord ++ tailWord_386712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386743 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_386743 : Nat := 118140960795 + 386743 * 2 ^ 59
def prefixEnd_386743 : Nat := 4983230072969 + 3 ^ 40 * 386743 * 2
def baseEnd_386743 : Nat := 88260021671949155526181

theorem tailTrace_386743 : CollatzResearch.WordTrace tailWord_386743 prefixEnd_386743 88260021671949155526181 := by
  unfold tailWord_386743
  simp only [CollatzResearch.WordTrace]
  refine ⟨14105676037903636290964883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9403784025269090860643255 14105676037903636290964883)
  ·
    refine ⟨21158514056855454436447325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14105676037903636290964883 21158514056855454436447325)
    ·
      refine ⟨7934442771320795413667747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21158514056855454436447325 7934442771320795413667747)
      ·
        refine ⟨11901664156981193120501621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7934442771320795413667747 11901664156981193120501621)
        ·
          refine ⟨1115781014716986855047027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11901664156981193120501621 1115781014716986855047027)
          ·
            refine ⟨1673671522075480282570541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115781014716986855047027 1673671522075480282570541)
            ·
              refine ⟨627626820778305105963953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1673671522075480282570541 627626820778305105963953)
              ·
                refine ⟨470720115583728829472965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627626820778305105963953 470720115583728829472965)
                ·
                  refine ⟨88260021671949155526181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470720115583728829472965 88260021671949155526181)
                  ·
                    rfl

theorem cell21_386743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_386743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386743 prefixEnd_386743 := by exact prefixLift 386743
  have htrace : WordTrace (prefixWord ++ tailWord_386743) baseStart_386743 baseEnd_386743 := by
    simpa [prefixWord, tailWord_386743, baseEnd_386743] using wordTrace_append hprefix tailTrace_386743
  have hstable : (prefixWord ++ tailWord_386743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386743).length < 2 ^ (prefixWord ++ tailWord_386743).sum := by decide
  have hdescent : baseEnd_386743 < baseStart_386743 := by decide
  rcases family_descends (prefixWord ++ tailWord_386743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386780 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_386780 : Nat := 118140960795 + 386780 * 2 ^ 59
def prefixEnd_386780 : Nat := 4983230072969 + 3 ^ 40 * 386780 * 2
def baseEnd_386780 : Nat := 88268465576045313409439

theorem tailTrace_386780 : CollatzResearch.WordTrace tailWord_386780 prefixEnd_386780 88268465576045313409439 := by
  unfold tailWord_386780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053512769384795805030897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9404683692513061073374529 7053512769384795805030897)
  ·
    refine ⟨5290134577038596853773173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7053512769384795805030897 5290134577038596853773173)
    ·
      refine ⟨495950116597368455041235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5290134577038596853773173 495950116597368455041235)
      ·
        refine ⟨743925174896052682561853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495950116597368455041235 743925174896052682561853)
        ·
          refine ⟨278971940586019755960695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743925174896052682561853 278971940586019755960695)
          ·
            refine ⟨418457910879029633941043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278971940586019755960695 418457910879029633941043)
            ·
              refine ⟨627686866318544450911565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418457910879029633941043 627686866318544450911565)
              ·
                refine ⟨235382574869454169091837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627686866318544450911565 235382574869454169091837)
                ·
                  refine ⟨88268465576045313409439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235382574869454169091837 88268465576045313409439)
                  ·
                    rfl

theorem cell21_386780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_386780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386780 prefixEnd_386780 := by exact prefixLift 386780
  have htrace : WordTrace (prefixWord ++ tailWord_386780) baseStart_386780 baseEnd_386780 := by
    simpa [prefixWord, tailWord_386780, baseEnd_386780] using wordTrace_append hprefix tailTrace_386780
  have hstable : (prefixWord ++ tailWord_386780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386780).length < 2 ^ (prefixWord ++ tailWord_386780).sum := by decide
  have hdescent : baseEnd_386780 < baseStart_386780 := by decide
  rcases family_descends (prefixWord ++ tailWord_386780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386791 : List Nat := [1, 1, 5, 4, 2, 1, 7]
def baseStart_386791 : Nat := 118140960795 + 386791 * 2 ^ 59
def prefixEnd_386791 : Nat := 4983230072969 + 3 ^ 40 * 386791 * 2
def baseEnd_386791 : Nat := 9807886213990193191787

theorem tailTrace_386791 : CollatzResearch.WordTrace tailWord_386791 prefixEnd_386791 9807886213990193191787 := by
  unfold tailWord_386791
  simp only [CollatzResearch.WordTrace]
  refine ⟨14107426741729740488712227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9404951161153160325808151 14107426741729740488712227)
  ·
    refine ⟨21161140112594610733068341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14107426741729740488712227 21161140112594610733068341)
    ·
      refine ⟨1983856885555744756225157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21161140112594610733068341 1983856885555744756225157)
      ·
        refine ⟨371973166041702141792217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1983856885555744756225157 371973166041702141792217)
        ·
          refine ⟨278979874531276606344163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371973166041702141792217 278979874531276606344163)
          ·
            refine ⟨418469811796914909516245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278979874531276606344163 418469811796914909516245)
            ·
              refine ⟨9807886213990193191787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 418469811796914909516245 9807886213990193191787)
              ·
                rfl

theorem cell21_386791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 7].length) (baseStart_386791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386791 prefixEnd_386791 := by exact prefixLift 386791
  have htrace : WordTrace (prefixWord ++ tailWord_386791) baseStart_386791 baseEnd_386791 := by
    simpa [prefixWord, tailWord_386791, baseEnd_386791] using wordTrace_append hprefix tailTrace_386791
  have hstable : (prefixWord ++ tailWord_386791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386791).length < 2 ^ (prefixWord ++ tailWord_386791).sum := by decide
  have hdescent : baseEnd_386791 < baseStart_386791 := by decide
  rcases family_descends (prefixWord ++ tailWord_386791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386802 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_386802 : Nat := 118140960795 + 386802 * 2 ^ 59
def prefixEnd_386802 : Nat := 4983230072969 + 3 ^ 40 * 386802 * 2
def baseEnd_386802 : Nat := 88273486275778164042727

theorem tailTrace_386802 : CollatzResearch.WordTrace tailWord_386802 prefixEnd_386802 88273486275778164042727 := by
  unfold tailWord_386802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526956986172472341840665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9405218629793259578241773 3526956986172472341840665)
  ·
    refine ⟨2645217739629354256380499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3526956986172472341840665 2645217739629354256380499)
    ·
      refine ⟨3967826609444031384570749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645217739629354256380499 3967826609444031384570749)
      ·
        refine ⟨1487934978541511769214031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3967826609444031384570749 1487934978541511769214031)
        ·
          refine ⟨2231902467812267653821047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487934978541511769214031 2231902467812267653821047)
          ·
            refine ⟨3347853701718401480731571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231902467812267653821047 3347853701718401480731571)
            ·
              refine ⟨5021780552577602221097357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347853701718401480731571 5021780552577602221097357)
              ·
                refine ⟨1883167707216600832911509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021780552577602221097357 1883167707216600832911509)
                ·
                  refine ⟨88273486275778164042727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1883167707216600832911509 88273486275778164042727)
                  ·
                    rfl

theorem cell21_386802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_386802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386802 prefixEnd_386802 := by exact prefixLift 386802
  have htrace : WordTrace (prefixWord ++ tailWord_386802) baseStart_386802 baseEnd_386802 := by
    simpa [prefixWord, tailWord_386802, baseEnd_386802] using wordTrace_append hprefix tailTrace_386802
  have hstable : (prefixWord ++ tailWord_386802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386802).length < 2 ^ (prefixWord ++ tailWord_386802).sum := by decide
  have hdescent : baseEnd_386802 < baseStart_386802 := by decide
  rcases family_descends (prefixWord ++ tailWord_386802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386819 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 4]
def baseStart_386819 : Nat := 118140960795 + 386819 * 2 ^ 59
def prefixEnd_386819 : Nat := 4983230072969 + 3 ^ 40 * 386819 * 2
def baseEnd_386819 : Nat := 88277365907389912259359

theorem tailTrace_386819 : CollatzResearch.WordTrace tailWord_386819 prefixEnd_386819 88277365907389912259359 := by
  unfold tailWord_386819
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108447985628301270731511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9405631990418867513821007 14108447985628301270731511)
  ·
    refine ⟨21162671978442451906097267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14108447985628301270731511 21162671978442451906097267)
    ·
      refine ⟨31744007967663677859145901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21162671978442451906097267 31744007967663677859145901)
      ·
        refine ⟨11904002987873879197179713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31744007967663677859145901 11904002987873879197179713)
        ·
          refine ⟨8928002240905409397884785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11904002987873879197179713 8928002240905409397884785)
          ·
            refine ⟨6696001680679057048413589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8928002240905409397884785 6696001680679057048413589)
            ·
              refine ⟨313875078781830799144387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6696001680679057048413589 313875078781830799144387)
              ·
                refine ⟨470812618172746198716581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313875078781830799144387 470812618172746198716581)
                ·
                  refine ⟨88277365907389912259359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470812618172746198716581 88277365907389912259359)
                  ·
                    rfl

theorem cell21_386819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4].length) (baseStart_386819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_386819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_386819 prefixEnd_386819 := by exact prefixLift 386819
  have htrace : WordTrace (prefixWord ++ tailWord_386819) baseStart_386819 baseEnd_386819 := by
    simpa [prefixWord, tailWord_386819, baseEnd_386819] using wordTrace_append hprefix tailTrace_386819
  have hstable : (prefixWord ++ tailWord_386819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386819).length < 2 ^ (prefixWord ++ tailWord_386819).sum := by decide
  have hdescent : baseEnd_386819 < baseStart_386819 := by decide
  rcases family_descends (prefixWord ++ tailWord_386819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387013 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_387013 : Nat := 118140960795 + 387013 * 2 ^ 59
def prefixEnd_387013 : Nat := 4983230072969 + 3 ^ 40 * 387013 * 2
def baseEnd_387013 : Nat := 88321639350488686025629

theorem tailTrace_387013 : CollatzResearch.WordTrace tailWord_387013 prefixEnd_387013 88321639350488686025629 := by
  unfold tailWord_387013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115523746925472403293693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9410349164616981602195795 14115523746925472403293693)
  ·
    refine ⟨5293321405097052151235135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14115523746925472403293693 5293321405097052151235135)
    ·
      refine ⟨7939982107645578226852703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293321405097052151235135 7939982107645578226852703)
      ·
        refine ⟨11909973161468367340279055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939982107645578226852703 11909973161468367340279055)
        ·
          refine ⟨17864959742202551010418583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909973161468367340279055 17864959742202551010418583)
          ·
            refine ⟨26797439613303826515627875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17864959742202551010418583 26797439613303826515627875)
            ·
              refine ⟨40196159419955739773441813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26797439613303826515627875 40196159419955739773441813)
              ·
                refine ⟨1884194972810425301880085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40196159419955739773441813 1884194972810425301880085)
                ·
                  refine ⟨88321639350488686025629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1884194972810425301880085 88321639350488686025629)
                  ·
                    rfl

theorem cell21_387013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_387013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387013 prefixEnd_387013 := by exact prefixLift 387013
  have htrace : WordTrace (prefixWord ++ tailWord_387013) baseStart_387013 baseEnd_387013 := by
    simpa [prefixWord, tailWord_387013, baseEnd_387013] using wordTrace_append hprefix tailTrace_387013
  have hstable : (prefixWord ++ tailWord_387013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387013).length < 2 ^ (prefixWord ++ tailWord_387013).sum := by decide
  have hdescent : baseEnd_387013 < baseStart_387013 := by decide
  rcases family_descends (prefixWord ++ tailWord_387013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387033 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 3]
def baseStart_387033 : Nat := 118140960795 + 387033 * 2 ^ 59
def prefixEnd_387033 : Nat := 4983230072969 + 3 ^ 40 * 387033 * 2
def baseEnd_387033 : Nat := 88326203622973095692255

theorem tailTrace_387033 : CollatzResearch.WordTrace tailWord_387033 prefixEnd_387033 88326203622973095692255 := by
  unfold tailWord_387033
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116253206853015819021753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9410835471235343879347835 14116253206853015819021753)
  ·
    refine ⟨10587189905139761864266315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14116253206853015819021753 10587189905139761864266315)
    ·
      refine ⟨15880784857709642796399473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10587189905139761864266315 15880784857709642796399473)
      ·
        refine ⟨11910588643282232097299605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15880784857709642796399473 11910588643282232097299605)
        ·
          refine ⟨558308842653854629560919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11910588643282232097299605 558308842653854629560919)
          ·
            refine ⟨837463263980781944341379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558308842653854629560919 837463263980781944341379)
            ·
              refine ⟨1256194895971172916512069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837463263980781944341379 1256194895971172916512069)
              ·
                refine ⟨235536542994594921846013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1256194895971172916512069 235536542994594921846013)
                ·
                  refine ⟨88326203622973095692255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235536542994594921846013 88326203622973095692255)
                  ·
                    rfl

theorem cell21_387033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_387033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387033 prefixEnd_387033 := by exact prefixLift 387033
  have htrace : WordTrace (prefixWord ++ tailWord_387033) baseStart_387033 baseEnd_387033 := by
    simpa [prefixWord, tailWord_387033, baseEnd_387033] using wordTrace_append hprefix tailTrace_387033
  have hstable : (prefixWord ++ tailWord_387033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387033).length < 2 ^ (prefixWord ++ tailWord_387033).sum := by decide
  have hdescent : baseEnd_387033 < baseStart_387033 := by decide
  rcases family_descends (prefixWord ++ tailWord_387033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387036 : List Nat := [2, 2, 6, 1, 1, 2, 1, 6]
def baseStart_387036 : Nat := 118140960795 + 387036 * 2 ^ 59
def prefixEnd_387036 : Nat := 4983230072969 + 3 ^ 40 * 387036 * 2
def baseEnd_387036 : Nat := 29442296087948585714083

theorem tailTrace_387036 : CollatzResearch.WordTrace tailWord_387036 prefixEnd_387036 29442296087948585714083 := by
  unfold tailWord_387036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7058181312921073665690481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9410908417228098220920641 7058181312921073665690481)
  ·
    refine ⟨5293635984690805249267861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7058181312921073665690481 5293635984690805249267861)
    ·
      refine ⟨248139186782381496059431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5293635984690805249267861 248139186782381496059431)
      ·
        refine ⟨372208780173572244089147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248139186782381496059431 372208780173572244089147)
        ·
          refine ⟨558313170260358366133721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372208780173572244089147 558313170260358366133721)
          ·
            refine ⟨418734877695268774600291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558313170260358366133721 418734877695268774600291)
            ·
              refine ⟨628102316542903161900437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418734877695268774600291 628102316542903161900437)
              ·
                refine ⟨29442296087948585714083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 628102316542903161900437 29442296087948585714083)
                ·
                  rfl

theorem cell21_387036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_387036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387036 prefixEnd_387036 := by exact prefixLift 387036
  have htrace : WordTrace (prefixWord ++ tailWord_387036) baseStart_387036 baseEnd_387036 := by
    simpa [prefixWord, tailWord_387036, baseEnd_387036] using wordTrace_append hprefix tailTrace_387036
  have hstable : (prefixWord ++ tailWord_387036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387036).length < 2 ^ (prefixWord ++ tailWord_387036).sum := by decide
  have hdescent : baseEnd_387036 < baseStart_387036 := by decide
  rcases family_descends (prefixWord ++ tailWord_387036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387112 : List Nat := [2, 1, 5, 3, 2, 1, 2, 5]
def baseStart_387112 : Nat := 118140960795 + 387112 * 2 ^ 59
def prefixEnd_387112 : Nat := 4983230072969 + 3 ^ 40 * 387112 * 2
def baseEnd_387112 : Nat := 29448077499762171291809

theorem tailTrace_387112 : CollatzResearch.WordTrace tailWord_387112 prefixEnd_387112 29448077499762171291809 := by
  unfold tailWord_387112
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059567286783406155573795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9412756382377874874098393 7059567286783406155573795)
  ·
    refine ⟨10589350930175109233360693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7059567286783406155573795 10589350930175109233360693)
    ·
      refine ⟨992751649703916490627565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10589350930175109233360693 992751649703916490627565)
      ·
        refine ⟨372281868638968683985337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 992751649703916490627565 372281868638968683985337)
        ·
          refine ⟨279211401479226512989003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372281868638968683985337 279211401479226512989003)
          ·
            refine ⟨418817102218839769483505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279211401479226512989003 418817102218839769483505)
            ·
              refine ⟨314112826664129827112629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418817102218839769483505 314112826664129827112629)
              ·
                refine ⟨29448077499762171291809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314112826664129827112629 29448077499762171291809)
                ·
                  rfl

theorem cell21_387112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_387112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387112 prefixEnd_387112 := by exact prefixLift 387112
  have htrace : WordTrace (prefixWord ++ tailWord_387112) baseStart_387112 baseEnd_387112 := by
    simpa [prefixWord, tailWord_387112, baseEnd_387112] using wordTrace_append hprefix tailTrace_387112
  have hstable : (prefixWord ++ tailWord_387112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387112).length < 2 ^ (prefixWord ++ tailWord_387112).sum := by decide
  have hdescent : baseEnd_387112 < baseStart_387112 := by decide
  rcases family_descends (prefixWord ++ tailWord_387112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387120 : List Nat := [2, 1, 1, 1, 2, 6, 1, 7]
def baseStart_387120 : Nat := 118140960795 + 387120 * 2 ^ 59
def prefixEnd_387120 : Nat := 4983230072969 + 3 ^ 40 * 387120 * 2
def baseEnd_387120 : Nat := 29448686069426759247359

theorem tailTrace_387120 : CollatzResearch.WordTrace tailWord_387120 prefixEnd_387120 29448686069426759247359 := by
  unfold tailWord_387120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7059713178768914838719407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9412950905025219784959209 7059713178768914838719407)
  ·
    refine ⟨10589569768153372258079111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7059713178768914838719407 10589569768153372258079111)
    ·
      refine ⟨15884354652230058387118667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10589569768153372258079111 15884354652230058387118667)
      ·
        refine ⟨23826531978345087580678001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15884354652230058387118667 23826531978345087580678001)
        ·
          refine ⟨17869898983758815685508501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23826531978345087580678001 17869898983758815685508501)
          ·
            refine ⟨837651514863694485258211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17869898983758815685508501 837651514863694485258211)
            ·
              refine ⟨1256477272295541727887317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837651514863694485258211 1256477272295541727887317)
              ·
                refine ⟨29448686069426759247359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1256477272295541727887317 29448686069426759247359)
                ·
                  rfl

theorem cell21_387120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_387120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387120 prefixEnd_387120 := by exact prefixLift 387120
  have htrace : WordTrace (prefixWord ++ tailWord_387120) baseStart_387120 baseEnd_387120 := by
    simpa [prefixWord, tailWord_387120, baseEnd_387120] using wordTrace_append hprefix tailTrace_387120
  have hstable : (prefixWord ++ tailWord_387120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387120).length < 2 ^ (prefixWord ++ tailWord_387120).sum := by decide
  have hdescent : baseEnd_387120 < baseStart_387120 := by decide
  rcases family_descends (prefixWord ++ tailWord_387120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387137 : List Nat := [1, 2, 5, 1, 2, 3, 7]
def baseStart_387137 : Nat := 118140960795 + 387137 * 2 ^ 59
def prefixEnd_387137 : Nat := 4983230072969 + 3 ^ 40 * 387137 * 2
def baseEnd_387137 : Nat := 9816659759988002884301

theorem tailTrace_387137 : CollatzResearch.WordTrace tailWord_387137 prefixEnd_387137 9816659759988002884301 := by
  unfold tailWord_387137
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120046398476241580807665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9413364265650827720538443 14120046398476241580807665)
  ·
    refine ⟨10590034798857181185605749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14120046398476241580807665 10590034798857181185605749)
    ·
      refine ⟨992815762392860736150539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10590034798857181185605749 992815762392860736150539)
      ·
        refine ⟨1489223643589291104225809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992815762392860736150539 1489223643589291104225809)
        ·
          refine ⟨1116917732691968328169357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1489223643589291104225809 1116917732691968328169357)
          ·
            refine ⟨418844149759488123063509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1116917732691968328169357 418844149759488123063509)
            ·
              refine ⟨9816659759988002884301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 418844149759488123063509 9816659759988002884301)
              ·
                rfl

theorem cell21_387137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 7].length) (baseStart_387137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387137 prefixEnd_387137 := by exact prefixLift 387137
  have htrace : WordTrace (prefixWord ++ tailWord_387137) baseStart_387137 baseEnd_387137 := by
    simpa [prefixWord, tailWord_387137, baseEnd_387137] using wordTrace_append hprefix tailTrace_387137
  have hstable : (prefixWord ++ tailWord_387137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387137).length < 2 ^ (prefixWord ++ tailWord_387137).sum := by decide
  have hdescent : baseEnd_387137 < baseStart_387137 := by decide
  rcases family_descends (prefixWord ++ tailWord_387137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387258 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_387258 : Nat := 118140960795 + 387258 * 2 ^ 59
def prefixEnd_387258 : Nat := 4983230072969 + 3 ^ 40 * 387258 * 2
def baseEnd_387258 : Nat := 88377551688422704441795

theorem tailTrace_387258 : CollatzResearch.WordTrace tailWord_387258 prefixEnd_387258 88377551688422704441795 := by
  unfold tailWord_387258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531114907759469811490607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9416306420691919497308285 3531114907759469811490607)
  ·
    refine ⟨5296672361639204717235911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531114907759469811490607 5296672361639204717235911)
    ·
      refine ⟨7945008542458807075853867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296672361639204717235911 7945008542458807075853867)
      ·
        refine ⟨11917512813688210613780801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945008542458807075853867 11917512813688210613780801)
        ·
          refine ⟨8938134610266157960335601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11917512813688210613780801 8938134610266157960335601)
          ·
            refine ⟨6703600957699618470251701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8938134610266157960335601 6703600957699618470251701)
            ·
              refine ⟨628462589784339231586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6703600957699618470251701 628462589784339231586097)
              ·
                refine ⟨471346942338254423689573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628462589784339231586097 471346942338254423689573)
                ·
                  refine ⟨88377551688422704441795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471346942338254423689573 88377551688422704441795)
                  ·
                    rfl

theorem cell21_387258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_387258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387258 prefixEnd_387258 := by exact prefixLift 387258
  have htrace : WordTrace (prefixWord ++ tailWord_387258) baseStart_387258 baseEnd_387258 := by
    simpa [prefixWord, tailWord_387258, baseEnd_387258] using wordTrace_append hprefix tailTrace_387258
  have hstable : (prefixWord ++ tailWord_387258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387258).length < 2 ^ (prefixWord ++ tailWord_387258).sum := by decide
  have hdescent : baseEnd_387258 < baseStart_387258 := by decide
  rcases family_descends (prefixWord ++ tailWord_387258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387413 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 3]
def baseStart_387413 : Nat := 118140960795 + 387413 * 2 ^ 59
def prefixEnd_387413 : Nat := 4983230072969 + 3 ^ 40 * 387413 * 2
def baseEnd_387413 : Nat := 88412924800176879358145

theorem tailTrace_387413 : CollatzResearch.WordTrace tailWord_387413 prefixEnd_387413 88412924800176879358145 := by
  unfold tailWord_387413
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130112945476340717854893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9420075296984227145236595 14130112945476340717854893)
  ·
    refine ⟨5298792354553627769195585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14130112945476340717854893 5298792354553627769195585)
    ·
      refine ⟨3974094265915220826896689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5298792354553627769195585 3974094265915220826896689)
      ·
        refine ⟨2980570699436415620172517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3974094265915220826896689 2980570699436415620172517)
        ·
          refine ⟨558857006144327928782347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2980570699436415620172517 558857006144327928782347)
          ·
            refine ⟨838285509216491893173521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558857006144327928782347 838285509216491893173521)
            ·
              refine ⟨628714131912368919880141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838285509216491893173521 628714131912368919880141)
              ·
                refine ⟨235767799467138344955053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628714131912368919880141 235767799467138344955053)
                ·
                  refine ⟨88412924800176879358145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235767799467138344955053 88412924800176879358145)
                  ·
                    rfl

theorem cell21_387413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_387413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387413 prefixEnd_387413 := by exact prefixLift 387413
  have htrace : WordTrace (prefixWord ++ tailWord_387413) baseStart_387413 baseEnd_387413 := by
    simpa [prefixWord, tailWord_387413, baseEnd_387413] using wordTrace_append hprefix tailTrace_387413
  have hstable : (prefixWord ++ tailWord_387413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387413).length < 2 ^ (prefixWord ++ tailWord_387413).sum := by decide
  have hdescent : baseEnd_387413 < baseStart_387413 := by decide
  rcases family_descends (prefixWord ++ tailWord_387413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387424 : List Nat := [2, 1, 1, 3, 5, 1, 8]
def baseStart_387424 : Nat := 118140960795 + 387424 * 2 ^ 59
def prefixEnd_387424 : Nat := 4983230072969 + 3 ^ 40 * 387424 * 2
def baseEnd_387424 : Nat := 9823937238893700519421

theorem tailTrace_387424 : CollatzResearch.WordTrace tailWord_387424 prefixEnd_387424 9823937238893700519421 := by
  unfold tailWord_387424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065257074218244798252663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9420342765624326397670217 7065257074218244798252663)
  ·
    refine ⟨10597885611327367197378995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7065257074218244798252663 10597885611327367197378995)
    ·
      refine ⟨15896828416991050796068493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10597885611327367197378995 15896828416991050796068493)
      ·
        refine ⟨5961310656371644048525685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15896828416991050796068493 5961310656371644048525685)
        ·
          refine ⟨558872874034841629549283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5961310656371644048525685 558872874034841629549283)
          ·
            refine ⟨838309311052262444323925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558872874034841629549283 838309311052262444323925)
            ·
              refine ⟨9823937238893700519421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 838309311052262444323925 9823937238893700519421)
              ·
                rfl

theorem cell21_387424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 8].length) (baseStart_387424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387424 prefixEnd_387424 := by exact prefixLift 387424
  have htrace : WordTrace (prefixWord ++ tailWord_387424) baseStart_387424 baseEnd_387424 := by
    simpa [prefixWord, tailWord_387424, baseEnd_387424] using wordTrace_append hprefix tailTrace_387424
  have hstable : (prefixWord ++ tailWord_387424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387424).length < 2 ^ (prefixWord ++ tailWord_387424).sum := by decide
  have hdescent : baseEnd_387424 < baseStart_387424 := by decide
  rcases family_descends (prefixWord ++ tailWord_387424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387458 : List Nat := [3, 4, 2, 1, 2, 1, 1, 7]
def baseStart_387458 : Nat := 118140960795 + 387458 * 2 ^ 59
def prefixEnd_387458 : Nat := 4983230072969 + 3 ^ 40 * 387458 * 2
def baseEnd_387458 : Nat := 29474398137755600369351

theorem tailTrace_387458 : CollatzResearch.WordTrace tailWord_387458 prefixEnd_387458 29474398137755600369351 := by
  unfold tailWord_387458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532938557578328350810757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9421169486875542268828685 3532938557578328350810757)
  ·
    refine ⟨662425979545936565777017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3532938557578328350810757 662425979545936565777017)
    ·
      refine ⟨496819484659452424332763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 662425979545936565777017 496819484659452424332763)
      ·
        refine ⟨745229226989178636499145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496819484659452424332763 745229226989178636499145)
        ·
          refine ⟨558921920241883977374359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745229226989178636499145 558921920241883977374359)
          ·
            refine ⟨838382880362825966061539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558921920241883977374359 838382880362825966061539)
            ·
              refine ⟨1257574320544238949092309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838382880362825966061539 1257574320544238949092309)
              ·
                refine ⟨29474398137755600369351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1257574320544238949092309 29474398137755600369351)
                ·
                  rfl

theorem cell21_387458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_387458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387458 prefixEnd_387458 := by exact prefixLift 387458
  have htrace : WordTrace (prefixWord ++ tailWord_387458) baseStart_387458 baseEnd_387458 := by
    simpa [prefixWord, tailWord_387458, baseEnd_387458] using wordTrace_append hprefix tailTrace_387458
  have hstable : (prefixWord ++ tailWord_387458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387458).length < 2 ^ (prefixWord ++ tailWord_387458).sum := by decide
  have hdescent : baseEnd_387458 < baseStart_387458 := by decide
  rcases family_descends (prefixWord ++ tailWord_387458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387489 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 5]
def baseStart_387489 : Nat := 118140960795 + 387489 * 2 ^ 59
def prefixEnd_387489 : Nat := 4983230072969 + 3 ^ 40 * 387489 * 2
def baseEnd_387489 : Nat := 88430269035617636091323

theorem tailTrace_387489 : CollatzResearch.WordTrace tailWord_387489 prefixEnd_387489 88430269035617636091323 := by
  unfold tailWord_387489
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132884893201005697621521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9421923262134003798414347 14132884893201005697621521)
  ·
    refine ⟨10599663669900754273216141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14132884893201005697621521 10599663669900754273216141)
    ·
      refine ⟨3974873876212782852456053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10599663669900754273216141 3974873876212782852456053)
      ·
        refine ⟨372644425894948392417755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3974873876212782852456053 372644425894948392417755)
        ·
          refine ⟨558966638842422588626633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372644425894948392417755 558966638842422588626633)
          ·
            refine ⟨419224979131816941469975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558966638842422588626633 419224979131816941469975)
            ·
              refine ⟨628837468697725412204963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419224979131816941469975 628837468697725412204963)
              ·
                refine ⟨943256203046588118307445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628837468697725412204963 943256203046588118307445)
                ·
                  refine ⟨88430269035617636091323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 943256203046588118307445 88430269035617636091323)
                  ·
                    rfl

theorem cell21_387489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_387489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387489 prefixEnd_387489 := by exact prefixLift 387489
  have htrace : WordTrace (prefixWord ++ tailWord_387489) baseStart_387489 baseEnd_387489 := by
    simpa [prefixWord, tailWord_387489, baseEnd_387489] using wordTrace_append hprefix tailTrace_387489
  have hstable : (prefixWord ++ tailWord_387489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387489).length < 2 ^ (prefixWord ++ tailWord_387489).sum := by decide
  have hdescent : baseEnd_387489 < baseStart_387489 := by decide
  rcases family_descends (prefixWord ++ tailWord_387489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387514 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_387514 : Nat := 118140960795 + 387514 * 2 ^ 59
def prefixEnd_387514 : Nat := 4983230072969 + 3 ^ 40 * 387514 * 2
def baseEnd_387514 : Nat := 88435974376223148174605

theorem tailTrace_387514 : CollatzResearch.WordTrace tailWord_387514 prefixEnd_387514 88435974376223148174605 := by
  unfold tailWord_387514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533449179527608741820399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9422531145406956644854397 3533449179527608741820399)
  ·
    refine ⟨5300173769291413112730599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533449179527608741820399 5300173769291413112730599)
    ·
      refine ⟨7950260653937119669095899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300173769291413112730599 7950260653937119669095899)
      ·
        refine ⟨11925390980905679503643849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7950260653937119669095899 11925390980905679503643849)
        ·
          refine ⟨8944043235679259627732887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11925390980905679503643849 8944043235679259627732887)
          ·
            refine ⟨13416064853518889441599331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944043235679259627732887 13416064853518889441599331)
            ·
              refine ⟨20124097280278334162398997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13416064853518889441599331 20124097280278334162398997)
              ·
                refine ⟨943317060013046913862453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20124097280278334162398997 943317060013046913862453)
                ·
                  refine ⟨88435974376223148174605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 943317060013046913862453 88435974376223148174605)
                  ·
                    rfl

theorem cell21_387514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_387514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387514 prefixEnd_387514 := by exact prefixLift 387514
  have htrace : WordTrace (prefixWord ++ tailWord_387514) baseStart_387514 baseEnd_387514 := by
    simpa [prefixWord, tailWord_387514, baseEnd_387514] using wordTrace_append hprefix tailTrace_387514
  have hstable : (prefixWord ++ tailWord_387514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387514).length < 2 ^ (prefixWord ++ tailWord_387514).sum := by decide
  have hdescent : baseEnd_387514 < baseStart_387514 := by decide
  rcases family_descends (prefixWord ++ tailWord_387514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387531 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 3]
def baseStart_387531 : Nat := 118140960795 + 387531 * 2 ^ 59
def prefixEnd_387531 : Nat := 4983230072969 + 3 ^ 40 * 387531 * 2
def baseEnd_387531 : Nat := 88439854007834896391237

theorem tailTrace_387531 : CollatzResearch.WordTrace tailWord_387531 prefixEnd_387531 88439854007834896391237 := by
  unfold tailWord_387531
  simp only [CollatzResearch.WordTrace]
  refine ⟨14134416759048846870650447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9422944506032564580433631 14134416759048846870650447)
  ·
    refine ⟨21201625138573270305975671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14134416759048846870650447 21201625138573270305975671)
    ·
      refine ⟨31802437707859905458963507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21201625138573270305975671 31802437707859905458963507)
      ·
        refine ⟨47703656561789858188445261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31802437707859905458963507 47703656561789858188445261)
        ·
          refine ⟨17888871210671196820666973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47703656561789858188445261 17888871210671196820666973)
          ·
            refine ⟨6708326704001698807750115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17888871210671196820666973 6708326704001698807750115)
            ·
              refine ⟨10062490056002548211625173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708326704001698807750115 10062490056002548211625173)
              ·
                refine ⟨235839610687559723709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10062490056002548211625173 235839610687559723709965)
                ·
                  refine ⟨88439854007834896391237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235839610687559723709965 88439854007834896391237)
                  ·
                    rfl

theorem cell21_387531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3].length) (baseStart_387531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387531 prefixEnd_387531 := by exact prefixLift 387531
  have htrace : WordTrace (prefixWord ++ tailWord_387531) baseStart_387531 baseEnd_387531 := by
    simpa [prefixWord, tailWord_387531, baseEnd_387531] using wordTrace_append hprefix tailTrace_387531
  have hstable : (prefixWord ++ tailWord_387531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387531).length < 2 ^ (prefixWord ++ tailWord_387531).sum := by decide
  have hdescent : baseEnd_387531 < baseStart_387531 := by decide
  rcases family_descends (prefixWord ++ tailWord_387531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387562 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_387562 : Nat := 118140960795 + 387562 * 2 ^ 59
def prefixEnd_387562 : Nat := 4983230072969 + 3 ^ 40 * 387562 * 2
def baseEnd_387562 : Nat := 88446928630185731374507

theorem tailTrace_387562 : CollatzResearch.WordTrace tailWord_387562 prefixEnd_387562 88446928630185731374507 := by
  unfold tailWord_387562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533886855484134791257235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9423698281291026110019293 3533886855484134791257235)
  ·
    refine ⟨5300830283226202186885853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533886855484134791257235 5300830283226202186885853)
    ·
      refine ⟨1987811356209825820082195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5300830283226202186885853 1987811356209825820082195)
      ·
        refine ⟨2981717034314738730123293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987811356209825820082195 2981717034314738730123293)
        ·
          refine ⟨1118143887868027023796235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2981717034314738730123293 1118143887868027023796235)
          ·
            refine ⟨1677215831802040535694353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118143887868027023796235 1677215831802040535694353)
            ·
              refine ⟨1257911873851530401770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677215831802040535694353 1257911873851530401770765)
              ·
                refine ⟨471716952694323900664037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1257911873851530401770765 471716952694323900664037)
                ·
                  refine ⟨88446928630185731374507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471716952694323900664037 88446928630185731374507)
                  ·
                    rfl

theorem cell21_387562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_387562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387562 prefixEnd_387562 := by exact prefixLift 387562
  have htrace : WordTrace (prefixWord ++ tailWord_387562) baseStart_387562 baseEnd_387562 := by
    simpa [prefixWord, tailWord_387562, baseEnd_387562] using wordTrace_append hprefix tailTrace_387562
  have hstable : (prefixWord ++ tailWord_387562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387562).length < 2 ^ (prefixWord ++ tailWord_387562).sum := by decide
  have hdescent : baseEnd_387562 < baseStart_387562 := by decide
  rcases family_descends (prefixWord ++ tailWord_387562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387576 : List Nat := [2, 1, 2, 1, 1, 4, 5, 5]
def baseStart_387576 : Nat := 118140960795 + 387576 * 2 ^ 59
def prefixEnd_387576 : Nat := 4983230072969 + 3 ^ 40 * 387576 * 2
def baseEnd_387576 : Nat := 29483374540308272713715

theorem tailTrace_387576 : CollatzResearch.WordTrace tailWord_387576 prefixEnd_387576 29483374540308272713715 := by
  unfold tailWord_387576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068029021942909778019291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9424038695923879704025721 7068029021942909778019291)
  ·
    refine ⟨10602043532914364667028937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7068029021942909778019291 10602043532914364667028937)
    ·
      refine ⟨7951532649685773500271703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10602043532914364667028937 7951532649685773500271703)
      ·
        refine ⟨11927298974528660250407555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951532649685773500271703 11927298974528660250407555)
        ·
          refine ⟨17890948461792990375611333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11927298974528660250407555 17890948461792990375611333)
          ·
            refine ⟨3354552836586185695427125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17890948461792990375611333 3354552836586185695427125)
            ·
              refine ⟨314489328429954908946293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3354552836586185695427125 314489328429954908946293)
              ·
                refine ⟨29483374540308272713715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314489328429954908946293 29483374540308272713715)
                ·
                  rfl

theorem cell21_387576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_387576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387576 prefixEnd_387576 := by exact prefixLift 387576
  have htrace : WordTrace (prefixWord ++ tailWord_387576) baseStart_387576 baseEnd_387576 := by
    simpa [prefixWord, tailWord_387576, baseEnd_387576] using wordTrace_append hprefix tailTrace_387576
  have hstable : (prefixWord ++ tailWord_387576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387576).length < 2 ^ (prefixWord ++ tailWord_387576).sum := by decide
  have hdescent : baseEnd_387576 < baseStart_387576 := by decide
  rcases family_descends (prefixWord ++ tailWord_387576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387621 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_387621 : Nat := 118140960795 + 387621 * 2 ^ 59
def prefixEnd_387621 : Nat := 4983230072969 + 3 ^ 40 * 387621 * 2
def baseEnd_387621 : Nat := 88460393234014739891053

theorem tailTrace_387621 : CollatzResearch.WordTrace tailWord_387621 prefixEnd_387621 88460393234014739891053 := by
  unfold tailWord_387621
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137699328722792241426717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9425132885815194827617811 14137699328722792241426717)
  ·
    refine ⟨5301637248271047090535019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14137699328722792241426717 5301637248271047090535019)
    ·
      refine ⟨7952455872406570635802529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301637248271047090535019 7952455872406570635802529)
      ·
        refine ⟨5964341904304927976851897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7952455872406570635802529 5964341904304927976851897)
        ·
          refine ⟨4473256428228695982638923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5964341904304927976851897 4473256428228695982638923)
          ·
            refine ⟨6709884642343043973958385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473256428228695982638923 6709884642343043973958385)
            ·
              refine ⟨5032413481757282980468789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6709884642343043973958385 5032413481757282980468789)
              ·
                refine ⟨471788763914745279418949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5032413481757282980468789 471788763914745279418949)
                ·
                  refine ⟨88460393234014739891053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471788763914745279418949 88460393234014739891053)
                  ·
                    rfl

theorem cell21_387621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_387621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387621 prefixEnd_387621 := by exact prefixLift 387621
  have htrace : WordTrace (prefixWord ++ tailWord_387621) baseStart_387621 baseEnd_387621 := by
    simpa [prefixWord, tailWord_387621, baseEnd_387621] using wordTrace_append hprefix tailTrace_387621
  have hstable : (prefixWord ++ tailWord_387621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387621).length < 2 ^ (prefixWord ++ tailWord_387621).sum := by decide
  have hdescent : baseEnd_387621 < baseStart_387621 := by decide
  rcases family_descends (prefixWord ++ tailWord_387621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
