import V185TrunkScan23Chunk0135

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_805096 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_805096 : Nat := 118140960795 + 805096 * 2 ^ 59
def prefixEnd_805096 : Nat := 4983230072969 + 3 ^ 40 * 805096 * 2
def baseEnd_805096 : Nat := 413401221012287291897437

theorem tailTrace_805096 : CollatzResearch.WordTrace tailWord_805096 prefixEnd_805096 413401221012287291897437 := by
  unfold tailWord_805096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682131745641083147509571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19576175660854777530012761 14682131745641083147509571)
  ·
    refine ⟨22023197618461624721264357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14682131745641083147509571 22023197618461624721264357)
    ·
      refine ⟨4129349553461554635237067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22023197618461624721264357 4129349553461554635237067)
      ·
        refine ⟨6194024330192331952855601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129349553461554635237067 6194024330192331952855601)
        ·
          refine ⟨4645518247644248964641701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194024330192331952855601 4645518247644248964641701)
          ·
            refine ⟨871034671433296680870319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4645518247644248964641701 871034671433296680870319)
            ·
              refine ⟨1306552007149945021305479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871034671433296680870319 1306552007149945021305479)
              ·
                refine ⟨1959828010724917531958219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306552007149945021305479 1959828010724917531958219)
                ·
                  refine ⟨2939742016087376297937329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959828010724917531958219 2939742016087376297937329)
                  ·
                    refine ⟨2204806512065532223452997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2939742016087376297937329 2204806512065532223452997)
                    ·
                      refine ⟨413401221012287291897437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2204806512065532223452997 413401221012287291897437)
                      ·
                        rfl

theorem cell23_805096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_805096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805096 prefixEnd_805096 := by exact prefixLift 805096
  have htrace : WordTrace (prefixWord ++ tailWord_805096) baseStart_805096 baseEnd_805096 := by
    simpa [prefixWord, tailWord_805096, baseEnd_805096] using wordTrace_append hprefix tailTrace_805096
  have hstable : (prefixWord ++ tailWord_805096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805096).length < 2 ^ (prefixWord ++ tailWord_805096).sum := by decide
  have hdescent : baseEnd_805096 < baseStart_805096 := by decide
  rcases family_descends (prefixWord ++ tailWord_805096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805106 : List Nat := [3, 2, 1, 3, 2, 3, 2, 7]
def baseStart_805106 : Nat := 118140960795 + 805106 * 2 ^ 59
def prefixEnd_805106 : Nat := 4983230072969 + 3 ^ 40 * 805106 * 2
def baseEnd_805106 : Nat := 15311346511808601954533

theorem tailTrace_805106 : CollatzResearch.WordTrace tailWord_805106 prefixEnd_805106 15311346511808601954533 := by
  unfold tailWord_805106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341157055311484500720793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19576418814163958668588781 7341157055311484500720793)
  ·
    refine ⟨5505867791483613375540595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7341157055311484500720793 5505867791483613375540595)
    ·
      refine ⟨8258801687225420063310893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5505867791483613375540595 8258801687225420063310893)
      ·
        refine ⟨3097050632709532523741585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8258801687225420063310893 3097050632709532523741585)
        ·
          refine ⟨2322787974532149392806189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3097050632709532523741585 2322787974532149392806189)
          ·
            refine ⟨871045490449556022302321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2322787974532149392806189 871045490449556022302321)
            ·
              refine ⟨653284117837167016726741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871045490449556022302321 653284117837167016726741)
              ·
                refine ⟨15311346511808601954533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 653284117837167016726741 15311346511808601954533)
                ·
                  rfl

theorem cell23_805106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_805106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805106 prefixEnd_805106 := by exact prefixLift 805106
  have htrace : WordTrace (prefixWord ++ tailWord_805106) baseStart_805106 baseEnd_805106 := by
    simpa [prefixWord, tailWord_805106, baseEnd_805106] using wordTrace_append hprefix tailTrace_805106
  have hstable : (prefixWord ++ tailWord_805106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805106).length < 2 ^ (prefixWord ++ tailWord_805106).sum := by decide
  have hdescent : baseEnd_805106 < baseStart_805106 := by decide
  rcases family_descends (prefixWord ++ tailWord_805106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805116 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_805116 : Nat := 118140960795 + 805116 * 2 ^ 59
def prefixEnd_805116 : Nat := 4983230072969 + 3 ^ 40 * 805116 * 2
def baseEnd_805116 : Nat := 413411490625377213647345

theorem tailTrace_805116 : CollatzResearch.WordTrace tailWord_805116 prefixEnd_805116 413411490625377213647345 := by
  unfold tailWord_805116
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682496475604854855373601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19576661967473139807164801 14682496475604854855373601)
  ·
    refine ⟨11011872356703641141530201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14682496475604854855373601 11011872356703641141530201)
    ·
      refine ⟨8258904267527730856147651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11011872356703641141530201 8258904267527730856147651)
      ·
        refine ⟨12388356401291596284221477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258904267527730856147651 12388356401291596284221477)
        ·
          refine ⟨2322816825242174303291527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12388356401291596284221477 2322816825242174303291527)
          ·
            refine ⟨3484225237863261454937291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322816825242174303291527 3484225237863261454937291)
            ·
              refine ⟨5226337856794892182405937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484225237863261454937291 5226337856794892182405937)
              ·
                refine ⟨3919753392596169136804453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5226337856794892182405937 3919753392596169136804453)
                ·
                  refine ⟨734953761111781713150835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3919753392596169136804453 734953761111781713150835)
                  ·
                    refine ⟨1102430641667672569726253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734953761111781713150835 1102430641667672569726253)
                    ·
                      refine ⟨413411490625377213647345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1102430641667672569726253 413411490625377213647345)
                      ·
                        rfl

theorem cell23_805116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_805116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805116 prefixEnd_805116 := by exact prefixLift 805116
  have htrace : WordTrace (prefixWord ++ tailWord_805116) baseStart_805116 baseEnd_805116 := by
    simpa [prefixWord, tailWord_805116, baseEnd_805116] using wordTrace_append hprefix tailTrace_805116
  have hstable : (prefixWord ++ tailWord_805116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805116).length < 2 ^ (prefixWord ++ tailWord_805116).sum := by decide
  have hdescent : baseEnd_805116 < baseStart_805116 := by decide
  rcases family_descends (prefixWord ++ tailWord_805116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805196 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 5]
def baseStart_805196 : Nat := 118140960795 + 805196 * 2 ^ 59
def prefixEnd_805196 : Nat := 4983230072969 + 3 ^ 40 * 805196 * 2
def baseEnd_805196 : Nat := 45939174341970766738553

theorem tailTrace_805196 : CollatzResearch.WordTrace tailWord_805196 prefixEnd_805196 45939174341970766738553 := by
  unfold tailWord_805196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683955395459941686829721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19578607193946588915772961 14683955395459941686829721)
  ·
    refine ⟨11012966546594956265122291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14683955395459941686829721 11012966546594956265122291)
    ·
      refine ⟨16519449819892434397683437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012966546594956265122291 16519449819892434397683437)
      ·
        refine ⟨6194793682459662899131289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16519449819892434397683437 6194793682459662899131289)
        ·
          refine ⟨4646095261844747174348467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194793682459662899131289 4646095261844747174348467)
          ·
            refine ⟨6969142892767120761522701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646095261844747174348467 6969142892767120761522701)
            ·
              refine ⟨2613428584787670285571013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6969142892767120761522701 2613428584787670285571013)
              ·
                refine ⟨490017859647688178544565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2613428584787670285571013 490017859647688178544565)
                ·
                  refine ⟨45939174341970766738553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490017859647688178544565 45939174341970766738553)
                  ·
                    rfl

theorem cell23_805196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_805196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805196 prefixEnd_805196 := by exact prefixLift 805196
  have htrace : WordTrace (prefixWord ++ tailWord_805196) baseStart_805196 baseEnd_805196 := by
    simpa [prefixWord, tailWord_805196, baseEnd_805196] using wordTrace_append hprefix tailTrace_805196
  have hstable : (prefixWord ++ tailWord_805196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805196).length < 2 ^ (prefixWord ++ tailWord_805196).sum := by decide
  have hdescent : baseEnd_805196 < baseStart_805196 := by decide
  rcases family_descends (prefixWord ++ tailWord_805196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805226 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_805226 : Nat := 118140960795 + 805226 * 2 ^ 59
def prefixEnd_805226 : Nat := 4983230072969 + 3 ^ 40 * 805226 * 2
def baseEnd_805226 : Nat := 137822657832457261090613

theorem tailTrace_805226 : CollatzResearch.WordTrace tailWord_805226 prefixEnd_805226 137822657832457261090613 := by
  unfold tailWord_805226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342251245202799624312883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19579336653874132331501021 7342251245202799624312883)
  ·
    refine ⟨11013376867804199436469325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7342251245202799624312883 11013376867804199436469325)
    ·
      refine ⟨4130016325426574788675997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11013376867804199436469325 4130016325426574788675997)
      ·
        refine ⟨1548756122034965545753499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4130016325426574788675997 1548756122034965545753499)
        ·
          refine ⟨2323134183052448318630249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548756122034965545753499 2323134183052448318630249)
          ·
            refine ⟨1742350637289336238972687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323134183052448318630249 1742350637289336238972687)
            ·
              refine ⟨2613525955934004358459031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742350637289336238972687 2613525955934004358459031)
              ·
                refine ⟨3920288933901006537688547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613525955934004358459031 3920288933901006537688547)
                ·
                  refine ⟨5880433400851509806532821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920288933901006537688547 5880433400851509806532821)
                  ·
                    refine ⟨137822657832457261090613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5880433400851509806532821 137822657832457261090613)
                    ·
                      rfl

theorem cell23_805226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_805226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805226 prefixEnd_805226 := by exact prefixLift 805226
  have htrace : WordTrace (prefixWord ++ tailWord_805226) baseStart_805226 baseEnd_805226 := by
    simpa [prefixWord, tailWord_805226, baseEnd_805226] using wordTrace_append hprefix tailTrace_805226
  have hstable : (prefixWord ++ tailWord_805226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805226).length < 2 ^ (prefixWord ++ tailWord_805226).sum := by decide
  have hdescent : baseEnd_805226 < baseStart_805226 := by decide
  rcases family_descends (prefixWord ++ tailWord_805226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805299 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 7, 5]
def baseStart_805299 : Nat := 118140960795 + 805299 * 2 ^ 59
def prefixEnd_805299 : Nat := 4983230072969 + 3 ^ 40 * 805299 * 2
def baseEnd_805299 : Nat := 137835152528383332553001

theorem tailTrace_805299 : CollatzResearch.WordTrace tailWord_805299 prefixEnd_805299 137835152528383332553001 := by
  unfold tailWord_805299
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371667509546731964658951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19581111673031154643105967 29371667509546731964658951)
  ·
    refine ⟨44057501264320097946988427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29371667509546731964658951 44057501264320097946988427)
    ·
      refine ⟨66086251896480146920482641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44057501264320097946988427 66086251896480146920482641)
      ·
        refine ⟨49564688922360110190361981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66086251896480146920482641 49564688922360110190361981)
        ·
          refine ⟨18586758345885041321385743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49564688922360110190361981 18586758345885041321385743)
          ·
            refine ⟨27880137518827561982078615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18586758345885041321385743 27880137518827561982078615)
            ·
              refine ⟨41820206278241342973117923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27880137518827561982078615 41820206278241342973117923)
              ·
                refine ⟨62730309417362014459676885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41820206278241342973117923 62730309417362014459676885)
                ·
                  refine ⟨1470241626969422213898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62730309417362014459676885 1470241626969422213898677)
                  ·
                    refine ⟨137835152528383332553001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1470241626969422213898677 137835152528383332553001)
                    ·
                      rfl

theorem cell23_805299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 5].length) (baseStart_805299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805299 prefixEnd_805299 := by exact prefixLift 805299
  have htrace : WordTrace (prefixWord ++ tailWord_805299) baseStart_805299 baseEnd_805299 := by
    simpa [prefixWord, tailWord_805299, baseEnd_805299] using wordTrace_append hprefix tailTrace_805299
  have hstable : (prefixWord ++ tailWord_805299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805299).length < 2 ^ (prefixWord ++ tailWord_805299).sum := by decide
  have hdescent : baseEnd_805299 < baseStart_805299 := by decide
  rcases family_descends (prefixWord ++ tailWord_805299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805329 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_805329 : Nat := 118140960795 + 805329 * 2 ^ 59
def prefixEnd_805329 : Nat := 4983230072969 + 3 ^ 40 * 805329 * 2
def baseEnd_805329 : Nat := 137840287334928293427955

theorem tailTrace_805329 : CollatzResearch.WordTrace tailWord_805329 prefixEnd_805329 137840287334928293427955 := by
  unfold tailWord_805329
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372761699438047088251041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19581841132958698058834027 29372761699438047088251041)
  ·
    refine ⟨22029571274578535316188281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29372761699438047088251041 22029571274578535316188281)
    ·
      refine ⟨16522178455933901487141211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22029571274578535316188281 16522178455933901487141211)
      ·
        refine ⟨24783267683900852230711817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522178455933901487141211 24783267683900852230711817)
        ·
          refine ⟨18587450762925639173033863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24783267683900852230711817 18587450762925639173033863)
          ·
            refine ⟨27881176144388458759550795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18587450762925639173033863 27881176144388458759550795)
            ·
              refine ⟨41821764216582688139326193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27881176144388458759550795 41821764216582688139326193)
              ·
                refine ⟨31366323162437016104494645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41821764216582688139326193 31366323162437016104494645)
                ·
                  refine ⟨2940592796478470259796373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31366323162437016104494645 2940592796478470259796373)
                  ·
                    refine ⟨137840287334928293427955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2940592796478470259796373 137840287334928293427955)
                    ·
                      rfl

theorem cell23_805329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_805329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805329 prefixEnd_805329 := by exact prefixLift 805329
  have htrace : WordTrace (prefixWord ++ tailWord_805329) baseStart_805329 baseEnd_805329 := by
    simpa [prefixWord, tailWord_805329, baseEnd_805329] using wordTrace_append hprefix tailTrace_805329
  have hstable : (prefixWord ++ tailWord_805329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805329).length < 2 ^ (prefixWord ++ tailWord_805329).sum := by decide
  have hdescent : baseEnd_805329 < baseStart_805329 := by decide
  rcases family_descends (prefixWord ++ tailWord_805329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805333 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_805333 : Nat := 118140960795 + 805333 * 2 ^ 59
def prefixEnd_805333 : Nat := 4983230072969 + 3 ^ 40 * 805333 * 2
def baseEnd_805333 : Nat := 137840971975800954877949

theorem tailTrace_805333 : CollatzResearch.WordTrace tailWord_805333 prefixEnd_805333 137840971975800954877949 := by
  unfold tailWord_805333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372907591423555771396653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19581938394282370514264435 29372907591423555771396653)
  ·
    refine ⟨11014840346783833414273745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29372907591423555771396653 11014840346783833414273745)
    ·
      refine ⟨8261130260087875060705309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11014840346783833414273745 8261130260087875060705309)
      ·
        refine ⟨3097923847532953147764491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8261130260087875060705309 3097923847532953147764491)
        ·
          refine ⟨4646885771299429721646737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097923847532953147764491 4646885771299429721646737)
          ·
            refine ⟨3485164328474572291235053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646885771299429721646737 3485164328474572291235053)
            ·
              refine ⟨1306936623177964609213145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3485164328474572291235053 1306936623177964609213145)
              ·
                refine ⟨980202467383473456909859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306936623177964609213145 980202467383473456909859)
                ·
                  refine ⟨1470303701075210185364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980202467383473456909859 1470303701075210185364789)
                  ·
                    refine ⟨137840971975800954877949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1470303701075210185364789 137840971975800954877949)
                    ·
                      rfl

theorem cell23_805333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_805333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805333 prefixEnd_805333 := by exact prefixLift 805333
  have htrace : WordTrace (prefixWord ++ tailWord_805333) baseStart_805333 baseEnd_805333 := by
    simpa [prefixWord, tailWord_805333, baseEnd_805333] using wordTrace_append hprefix tailTrace_805333
  have hstable : (prefixWord ++ tailWord_805333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805333).length < 2 ^ (prefixWord ++ tailWord_805333).sum := by decide
  have hdescent : baseEnd_805333 < baseStart_805333 := by decide
  rcases family_descends (prefixWord ++ tailWord_805333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805353 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 7, 2, 2]
def baseStart_805353 : Nat := 118140960795 + 805353 * 2 ^ 59
def prefixEnd_805353 : Nat := 4983230072969 + 3 ^ 40 * 805353 * 2
def baseEnd_805353 : Nat := 413533185540492786383755

theorem tailTrace_805353 : CollatzResearch.WordTrace tailWord_805353 prefixEnd_805353 413533185540492786383755 := by
  unfold tailWord_805353
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373637051351099187124713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19582424700900732791416475 29373637051351099187124713)
  ·
    refine ⟨22030227788513324390343535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29373637051351099187124713 22030227788513324390343535)
    ·
      refine ⟨33045341682769986585515303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22030227788513324390343535 33045341682769986585515303)
      ·
        refine ⟨49568012524154979878272955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33045341682769986585515303 49568012524154979878272955)
        ·
          refine ⟨74352018786232469817409433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49568012524154979878272955 74352018786232469817409433)
          ·
            refine ⟨55764014089674352363057075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74352018786232469817409433 55764014089674352363057075)
            ·
              refine ⟨83646021134511528544585613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55764014089674352363057075 83646021134511528544585613)
              ·
                refine ⟨31367257925441823204219605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83646021134511528544585613 31367257925441823204219605)
                ·
                  refine ⟨735170107627542731348897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31367257925441823204219605 735170107627542731348897)
                  ·
                    refine ⟨551377580720657048511673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735170107627542731348897 551377580720657048511673)
                    ·
                      refine ⟨413533185540492786383755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551377580720657048511673 413533185540492786383755)
                      ·
                        rfl

theorem cell23_805353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 2, 2].length) (baseStart_805353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805353 prefixEnd_805353 := by exact prefixLift 805353
  have htrace : WordTrace (prefixWord ++ tailWord_805353) baseStart_805353 baseEnd_805353 := by
    simpa [prefixWord, tailWord_805353, baseEnd_805353] using wordTrace_append hprefix tailTrace_805353
  have hstable : (prefixWord ++ tailWord_805353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805353).length < 2 ^ (prefixWord ++ tailWord_805353).sum := by decide
  have hdescent : baseEnd_805353 < baseStart_805353 := by decide
  rcases family_descends (prefixWord ++ tailWord_805353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805363 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 2, 4]
def baseStart_805363 : Nat := 118140960795 + 805363 * 2 ^ 59
def prefixEnd_805363 : Nat := 4983230072969 + 3 ^ 40 * 805363 * 2
def baseEnd_805363 : Nat := 137846106782345915752903

theorem tailTrace_805363 : CollatzResearch.WordTrace tailWord_805363 prefixEnd_805363 137846106782345915752903 := by
  unfold tailWord_805363
  simp only [CollatzResearch.WordTrace]
  refine ⟨29374001781314870894988743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19582667854209913929992495 29374001781314870894988743)
  ·
    refine ⟨44061002671972306342483115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29374001781314870894988743 44061002671972306342483115)
    ·
      refine ⟨66091504007958459513724673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44061002671972306342483115 66091504007958459513724673)
      ·
        refine ⟨49568628005968844635293505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66091504007958459513724673 49568628005968844635293505)
        ·
          refine ⟨37176471004476633476470129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49568628005968844635293505 37176471004476633476470129)
          ·
            refine ⟨27882353253357475107352597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37176471004476633476470129 27882353253357475107352597)
            ·
              refine ⟨1306985308751131645657153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27882353253357475107352597 1306985308751131645657153)
              ·
                refine ⟨980238981563348734242865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306985308751131645657153 980238981563348734242865)
                ·
                  refine ⟨735179236172511550682149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980238981563348734242865 735179236172511550682149)
                  ·
                    refine ⟨137846106782345915752903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735179236172511550682149 137846106782345915752903)
                    ·
                      rfl

theorem cell23_805363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 4].length) (baseStart_805363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805363 prefixEnd_805363 := by exact prefixLift 805363
  have htrace : WordTrace (prefixWord ++ tailWord_805363) baseStart_805363 baseEnd_805363 := by
    simpa [prefixWord, tailWord_805363, baseEnd_805363] using wordTrace_append hprefix tailTrace_805363
  have hstable : (prefixWord ++ tailWord_805363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805363).length < 2 ^ (prefixWord ++ tailWord_805363).sum := by decide
  have hdescent : baseEnd_805363 < baseStart_805363 := by decide
  rcases family_descends (prefixWord ++ tailWord_805363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805380 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_805380 : Nat := 118140960795 + 805380 * 2 ^ 59
def prefixEnd_805380 : Nat := 4983230072969 + 3 ^ 40 * 805380 * 2
def baseEnd_805380 : Nat := 137849016506054726915377

theorem tailTrace_805380 : CollatzResearch.WordTrace tailWord_805380 prefixEnd_805380 137849016506054726915377 := by
  unfold tailWord_805380
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687310911126641399178797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19583081214835521865571729 14687310911126641399178797)
  ·
    refine ⟨5507741591672490524692049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14687310911126641399178797 5507741591672490524692049)
    ·
      refine ⟨4130806193754367893519037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5507741591672490524692049 4130806193754367893519037)
      ·
        refine ⟨1549052322657887960069639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4130806193754367893519037 1549052322657887960069639)
        ·
          refine ⟨2323578483986831940104459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549052322657887960069639 2323578483986831940104459)
          ·
            refine ⟨3485367725980247910156689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323578483986831940104459 3485367725980247910156689)
            ·
              refine ⟨2614025794485185932617517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485367725980247910156689 2614025794485185932617517)
              ·
                refine ⟨980259672931944724731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614025794485185932617517 980259672931944724731569)
                ·
                  refine ⟨735194754698958543548677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980259672931944724731569 735194754698958543548677)
                  ·
                    refine ⟨137849016506054726915377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735194754698958543548677 137849016506054726915377)
                    ·
                      rfl

theorem cell23_805380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_805380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805380 prefixEnd_805380 := by exact prefixLift 805380
  have htrace : WordTrace (prefixWord ++ tailWord_805380) baseStart_805380 baseEnd_805380 := by
    simpa [prefixWord, tailWord_805380, baseEnd_805380] using wordTrace_append hprefix tailTrace_805380
  have hstable : (prefixWord ++ tailWord_805380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805380).length < 2 ^ (prefixWord ++ tailWord_805380).sum := by decide
  have hdescent : baseEnd_805380 < baseStart_805380 := by decide
  rcases family_descends (prefixWord ++ tailWord_805380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805404 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_805404 : Nat := 118140960795 + 805404 * 2 ^ 59
def prefixEnd_805404 : Nat := 4983230072969 + 3 ^ 40 * 805404 * 2
def baseEnd_805404 : Nat := 413559373053872086846021

theorem tailTrace_805404 : CollatzResearch.WordTrace tailWord_805404 prefixEnd_805404 413559373053872086846021 := by
  unfold tailWord_805404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687748587083167448615633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19583664782777556598154177 14687748587083167448615633)
  ·
    refine ⟨11015811440312375586461725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14687748587083167448615633 11015811440312375586461725)
    ·
      refine ⟨4130929290117140844923147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11015811440312375586461725 4130929290117140844923147)
      ·
        refine ⟨6196393935175711267384721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130929290117140844923147 6196393935175711267384721)
        ·
          refine ⟨4647295451381783450538541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6196393935175711267384721 4647295451381783450538541)
          ·
            refine ⟨1742735794268168793951953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4647295451381783450538541 1742735794268168793951953)
            ·
              refine ⟨1307051845701126595463965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742735794268168793951953 1307051845701126595463965)
              ·
                refine ⟨490144442137922473298987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307051845701126595463965 490144442137922473298987)
                ·
                  refine ⟨735216663206883709948481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490144442137922473298987 735216663206883709948481)
                  ·
                    refine ⟨551412497405162782461361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735216663206883709948481 551412497405162782461361)
                    ·
                      refine ⟨413559373053872086846021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551412497405162782461361 413559373053872086846021)
                      ·
                        rfl

theorem cell23_805404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_805404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805404 prefixEnd_805404 := by exact prefixLift 805404
  have htrace : WordTrace (prefixWord ++ tailWord_805404) baseStart_805404 baseEnd_805404 := by
    simpa [prefixWord, tailWord_805404, baseEnd_805404] using wordTrace_append hprefix tailTrace_805404
  have hstable : (prefixWord ++ tailWord_805404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805404).length < 2 ^ (prefixWord ++ tailWord_805404).sum := by decide
  have hdescent : baseEnd_805404 < baseStart_805404 := by decide
  rcases family_descends (prefixWord ++ tailWord_805404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805426 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_805426 : Nat := 118140960795 + 805426 * 2 ^ 59
def prefixEnd_805426 : Nat := 4983230072969 + 3 ^ 40 * 805426 * 2
def baseEnd_805426 : Nat := 413570669628271000770919

theorem tailTrace_805426 : CollatzResearch.WordTrace tailWord_805426 prefixEnd_805426 413570669628271000770919 := by
  unfold tailWord_805426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344074895021658163633033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19584199720057755103021421 7344074895021658163633033)
  ·
    refine ⟨5508056171266243622724775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7344074895021658163633033 5508056171266243622724775)
    ·
      refine ⟨8262084256899365434087163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508056171266243622724775 8262084256899365434087163)
      ·
        refine ⟨12393126385349048151130745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262084256899365434087163 12393126385349048151130745)
        ·
          refine ⟨9294844789011786113348059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12393126385349048151130745 9294844789011786113348059)
          ·
            refine ⟨13942267183517679170022089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9294844789011786113348059 13942267183517679170022089)
            ·
              refine ⟨10456700387638259377516567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13942267183517679170022089 10456700387638259377516567)
              ·
                refine ⟨15685050581457389066274851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456700387638259377516567 15685050581457389066274851)
                ·
                  refine ⟨23527575872186083599412277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15685050581457389066274851 23527575872186083599412277)
                  ·
                    refine ⟨2205710238017445337444901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23527575872186083599412277 2205710238017445337444901)
                    ·
                      refine ⟨413570669628271000770919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2205710238017445337444901 413570669628271000770919)
                      ·
                        rfl

theorem cell23_805426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_805426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805426 prefixEnd_805426 := by exact prefixLift 805426
  have htrace : WordTrace (prefixWord ++ tailWord_805426) baseStart_805426 baseEnd_805426 := by
    simpa [prefixWord, tailWord_805426, baseEnd_805426] using wordTrace_append hprefix tailTrace_805426
  have hstable : (prefixWord ++ tailWord_805426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805426).length < 2 ^ (prefixWord ++ tailWord_805426).sum := by decide
  have hdescent : baseEnd_805426 < baseStart_805426 := by decide
  rcases family_descends (prefixWord ++ tailWord_805426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805444 : List Nat := [2, 3, 5, 1, 1, 2, 2, 7]
def baseStart_805444 : Nat := 118140960795 + 805444 * 2 ^ 59
def prefixEnd_805444 : Nat := 4983230072969 + 3 ^ 40 * 805444 * 2
def baseEnd_805444 : Nat := 15317774528890812235031

theorem tailTrace_805444 : CollatzResearch.WordTrace tailWord_805444 prefixEnd_805444 15317774528890812235031 := by
  unfold tailWord_805444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688478047010710864343693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19584637396014281152458257 14688478047010710864343693)
  ·
    refine ⟨5508179267629016574128885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14688478047010710864343693 5508179267629016574128885)
    ·
      refine ⟨516391806340220303824583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5508179267629016574128885 516391806340220303824583)
      ·
        refine ⟨774587709510330455736875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516391806340220303824583 774587709510330455736875)
        ·
          refine ⟨1161881564265495683605313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774587709510330455736875 1161881564265495683605313)
          ·
            refine ⟨871411173199121762703985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161881564265495683605313 871411173199121762703985)
            ·
              refine ⟨653558379899341322027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871411173199121762703985 653558379899341322027989)
              ·
                refine ⟨15317774528890812235031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 653558379899341322027989 15317774528890812235031)
                ·
                  rfl

theorem cell23_805444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 7].length) (baseStart_805444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805444 prefixEnd_805444 := by exact prefixLift 805444
  have htrace : WordTrace (prefixWord ++ tailWord_805444) baseStart_805444 baseEnd_805444 := by
    simpa [prefixWord, tailWord_805444, baseEnd_805444] using wordTrace_append hprefix tailTrace_805444
  have hstable : (prefixWord ++ tailWord_805444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805444).length < 2 ^ (prefixWord ++ tailWord_805444).sum := by decide
  have hdescent : baseEnd_805444 < baseStart_805444 := by decide
  rcases family_descends (prefixWord ++ tailWord_805444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805447 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_805447 : Nat := 118140960795 + 805447 * 2 ^ 59
def prefixEnd_805447 : Nat := 4983230072969 + 3 ^ 40 * 805447 * 2
def baseEnd_805447 : Nat := 413581452722015418608323

theorem tailTrace_805447 : CollatzResearch.WordTrace tailWord_805447 prefixEnd_805447 413581452722015418608323 := by
  unfold tailWord_805447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377065513010553241046595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19584710342007035494031063 29377065513010553241046595)
  ·
    refine ⟨44065598269515829861569893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29377065513010553241046595 44065598269515829861569893)
    ·
      refine ⟨8262299675534218099044355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44065598269515829861569893 8262299675534218099044355)
      ·
        refine ⟨12393449513301327148566533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262299675534218099044355 12393449513301327148566533)
        ·
          refine ⟨2323771783743998840356225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12393449513301327148566533 2323771783743998840356225)
          ·
            refine ⟨1742828837807999130267169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323771783743998840356225 1742828837807999130267169)
            ·
              refine ⟨1307121628355999347700377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742828837807999130267169 1307121628355999347700377)
              ·
                refine ⟨980341221266999510775283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307121628355999347700377 980341221266999510775283)
                ·
                  refine ⟨1470511831900499266162925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980341221266999510775283 1470511831900499266162925)
                  ·
                    refine ⟨551441936962687224811097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470511831900499266162925 551441936962687224811097)
                    ·
                      refine ⟨413581452722015418608323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551441936962687224811097 413581452722015418608323)
                      ·
                        rfl

theorem cell23_805447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_805447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805447 prefixEnd_805447 := by exact prefixLift 805447
  have htrace : WordTrace (prefixWord ++ tailWord_805447) baseStart_805447 baseEnd_805447 := by
    simpa [prefixWord, tailWord_805447, baseEnd_805447] using wordTrace_append hprefix tailTrace_805447
  have hstable : (prefixWord ++ tailWord_805447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805447).length < 2 ^ (prefixWord ++ tailWord_805447).sum := by decide
  have hdescent : baseEnd_805447 < baseStart_805447 := by decide
  rcases family_descends (prefixWord ++ tailWord_805447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805456 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_805456 : Nat := 118140960795 + 805456 * 2 ^ 59
def prefixEnd_805456 : Nat := 4983230072969 + 3 ^ 40 * 805456 * 2
def baseEnd_805456 : Nat := 413586074047905883395781

theorem tailTrace_805456 : CollatzResearch.WordTrace tailWord_805456 prefixEnd_805456 413586074047905883395781 := by
  unfold tailWord_805456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688696884988973889062111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19584929179985298518749481 14688696884988973889062111)
  ·
    refine ⟨22033045327483460833593167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14688696884988973889062111 22033045327483460833593167)
    ·
      refine ⟨33049567991225191250389751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22033045327483460833593167 33049567991225191250389751)
      ·
        refine ⟨49574351986837786875584627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33049567991225191250389751 49574351986837786875584627)
        ·
          refine ⟨74361527980256680313376941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49574351986837786875584627 74361527980256680313376941)
          ·
            refine ⟨27885572992596255117516353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74361527980256680313376941 27885572992596255117516353)
            ·
              refine ⟨20914179744447191338137265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27885572992596255117516353 20914179744447191338137265)
              ·
                refine ⟨15685634808335393503602949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20914179744447191338137265 15685634808335393503602949)
                ·
                  refine ⟨2941056526562886281925553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15685634808335393503602949 2941056526562886281925553)
                  ·
                    refine ⟨2205792394922164711444165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941056526562886281925553 2205792394922164711444165)
                    ·
                      refine ⟨413586074047905883395781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2205792394922164711444165 413586074047905883395781)
                      ·
                        rfl

theorem cell23_805456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_805456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805456 prefixEnd_805456 := by exact prefixLift 805456
  have htrace : WordTrace (prefixWord ++ tailWord_805456) baseStart_805456 baseEnd_805456 := by
    simpa [prefixWord, tailWord_805456, baseEnd_805456] using wordTrace_append hprefix tailTrace_805456
  have hstable : (prefixWord ++ tailWord_805456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805456).length < 2 ^ (prefixWord ++ tailWord_805456).sum := by decide
  have hdescent : baseEnd_805456 < baseStart_805456 := by decide
  rcases family_descends (prefixWord ++ tailWord_805456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805476 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_805476 : Nat := 118140960795 + 805476 * 2 ^ 59
def prefixEnd_805476 : Nat := 4983230072969 + 3 ^ 40 * 805476 * 2
def baseEnd_805476 : Nat := 413596343660995805145689

theorem tailTrace_805476 : CollatzResearch.WordTrace tailWord_805476 prefixEnd_805476 413596343660995805145689 := by
  unfold tailWord_805476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689061614952745596926141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19585415486603660795901521 14689061614952745596926141)
  ·
    refine ⟨5508398105607279598847303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14689061614952745596926141 5508398105607279598847303)
    ·
      refine ⟨8262597158410919398270955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508398105607279598847303 8262597158410919398270955)
      ·
        refine ⟨12393895737616379097406433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262597158410919398270955 12393895737616379097406433)
        ·
          refine ⟨9295421803212284323054825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12393895737616379097406433 9295421803212284323054825)
          ·
            refine ⟨6971566352409213242291119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9295421803212284323054825 6971566352409213242291119)
            ·
              refine ⟨10457349528613819863436679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6971566352409213242291119 10457349528613819863436679)
              ·
                refine ⟨15686024292920729795155019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10457349528613819863436679 15686024292920729795155019)
                ·
                  refine ⟨23529036439381094692732529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15686024292920729795155019 23529036439381094692732529)
                  ·
                    refine ⟨17646777329535821019549397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23529036439381094692732529 17646777329535821019549397)
                    ·
                      refine ⟨413596343660995805145689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17646777329535821019549397 413596343660995805145689)
                      ·
                        rfl

theorem cell23_805476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_805476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805476 prefixEnd_805476 := by exact prefixLift 805476
  have htrace : WordTrace (prefixWord ++ tailWord_805476) baseStart_805476 baseEnd_805476 := by
    simpa [prefixWord, tailWord_805476, baseEnd_805476] using wordTrace_append hprefix tailTrace_805476
  have hstable : (prefixWord ++ tailWord_805476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805476).length < 2 ^ (prefixWord ++ tailWord_805476).sum := by decide
  have hdescent : baseEnd_805476 < baseStart_805476 := by decide
  rcases family_descends (prefixWord ++ tailWord_805476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805503 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 5, 2]
def baseStart_805503 : Nat := 118140960795 + 805503 * 2 ^ 59
def prefixEnd_805503 : Nat := 4983230072969 + 3 ^ 40 * 805503 * 2
def baseEnd_805503 : Nat := 413610207638667199508065

theorem tailTrace_805503 : CollatzResearch.WordTrace tailWord_805503 prefixEnd_805503 413610207638667199508065 := by
  unfold tailWord_805503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29379108000807674805085163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19586072000538449870056775 29379108000807674805085163)
  ·
    refine ⟨44068662001211512207627745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29379108000807674805085163 44068662001211512207627745)
    ·
      refine ⟨33051496500908634155720809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44068662001211512207627745 33051496500908634155720809)
      ·
        refine ⟨24788622375681475616790607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33051496500908634155720809 24788622375681475616790607)
        ·
          refine ⟨37182933563522213425185911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788622375681475616790607 37182933563522213425185911)
          ·
            refine ⟨55774400345283320137778867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37182933563522213425185911 55774400345283320137778867)
            ·
              refine ⟨83661600517924980206668301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55774400345283320137778867 83661600517924980206668301)
              ·
                refine ⟨31373100194221867577500613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83661600517924980206668301 31373100194221867577500613)
                ·
                  refine ⟨5882456286416600170781365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31373100194221867577500613 5882456286416600170781365)
                  ·
                    refine ⟨551480276851556266010753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5882456286416600170781365 551480276851556266010753)
                    ·
                      refine ⟨413610207638667199508065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551480276851556266010753 413610207638667199508065)
                      ·
                        rfl

theorem cell23_805503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_805503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805503 prefixEnd_805503 := by exact prefixLift 805503
  have htrace : WordTrace (prefixWord ++ tailWord_805503) baseStart_805503 baseEnd_805503 := by
    simpa [prefixWord, tailWord_805503, baseEnd_805503] using wordTrace_append hprefix tailTrace_805503
  have hstable : (prefixWord ++ tailWord_805503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805503).length < 2 ^ (prefixWord ++ tailWord_805503).sum := by decide
  have hdescent : baseEnd_805503 < baseStart_805503 := by decide
  rcases family_descends (prefixWord ++ tailWord_805503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805633 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_805633 : Nat := 118140960795 + 805633 * 2 ^ 59
def prefixEnd_805633 : Nat := 4983230072969 + 3 ^ 40 * 805633 * 2
def baseEnd_805633 : Nat := 137892320041250563627489

theorem tailTrace_805633 : CollatzResearch.WordTrace tailWord_805633 prefixEnd_805633 137892320041250563627489 := by
  unfold tailWord_805633
  simp only [CollatzResearch.WordTrace]
  refine ⟨29383849490336707007317553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19589232993557804671545035 29383849490336707007317553)
  ·
    refine ⟨22037887117752530255488165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29383849490336707007317553 22037887117752530255488165)
    ·
      refine ⟨4132103834578599422904031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22037887117752530255488165 4132103834578599422904031)
      ·
        refine ⟨6198155751867899134356047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132103834578599422904031 6198155751867899134356047)
        ·
          refine ⟨9297233627801848701534071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198155751867899134356047 9297233627801848701534071)
          ·
            refine ⟨13945850441702773052301107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297233627801848701534071 13945850441702773052301107)
            ·
              refine ⟨20918775662554159578451661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945850441702773052301107 20918775662554159578451661)
              ·
                refine ⟨7844540873457809841919373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20918775662554159578451661 7844540873457809841919373)
                ·
                  refine ⟨2941702827546678690719765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7844540873457809841919373 2941702827546678690719765)
                  ·
                    refine ⟨137892320041250563627489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2941702827546678690719765 137892320041250563627489)
                    ·
                      rfl

theorem cell23_805633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_805633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805633 prefixEnd_805633 := by exact prefixLift 805633
  have htrace : WordTrace (prefixWord ++ tailWord_805633) baseStart_805633 baseEnd_805633 := by
    simpa [prefixWord, tailWord_805633, baseEnd_805633] using wordTrace_append hprefix tailTrace_805633
  have hstable : (prefixWord ++ tailWord_805633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805633).length < 2 ^ (prefixWord ++ tailWord_805633).sum := by decide
  have hdescent : baseEnd_805633 < baseStart_805633 := by decide
  rcases family_descends (prefixWord ++ tailWord_805633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805653 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_805653 : Nat := 118140960795 + 805653 * 2 ^ 59
def prefixEnd_805653 : Nat := 4983230072969 + 3 ^ 40 * 805653 * 2
def baseEnd_805653 : Nat := 413687229736841612632375

theorem tailTrace_805653 : CollatzResearch.WordTrace tailWord_805653 prefixEnd_805653 413687229736841612632375 := by
  unfold tailWord_805653
  simp only [CollatzResearch.WordTrace]
  refine ⟨29384578950264250423045613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19589719300176166948697075 29384578950264250423045613)
  ·
    refine ⟨11019217106349093908642105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29384578950264250423045613 11019217106349093908642105)
    ·
      refine ⟨8264412829761820431481579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11019217106349093908642105 8264412829761820431481579)
      ·
        refine ⟨12396619244642730647222369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8264412829761820431481579 12396619244642730647222369)
        ·
          refine ⟨9297464433482047985416777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12396619244642730647222369 9297464433482047985416777)
          ·
            refine ⟨6973098325111535989062583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9297464433482047985416777 6973098325111535989062583)
            ·
              refine ⟨10459647487667303983593875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973098325111535989062583 10459647487667303983593875)
              ·
                refine ⟨15689471231500955975390813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459647487667303983593875 15689471231500955975390813)
                ·
                  refine ⟨5883551711812858490771555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689471231500955975390813 5883551711812858490771555)
                  ·
                    refine ⟨8825327567719287736157333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883551711812858490771555 8825327567719287736157333)
                    ·
                      refine ⟨413687229736841612632375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8825327567719287736157333 413687229736841612632375)
                      ·
                        rfl

theorem cell23_805653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_805653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805653 prefixEnd_805653 := by exact prefixLift 805653
  have htrace : WordTrace (prefixWord ++ tailWord_805653) baseStart_805653 baseEnd_805653 := by
    simpa [prefixWord, tailWord_805653, baseEnd_805653] using wordTrace_append hprefix tailTrace_805653
  have hstable : (prefixWord ++ tailWord_805653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805653).length < 2 ^ (prefixWord ++ tailWord_805653).sum := by decide
  have hdescent : baseEnd_805653 < baseStart_805653 := by decide
  rcases family_descends (prefixWord ++ tailWord_805653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805657 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 3, 2, 2]
def baseStart_805657 : Nat := 118140960795 + 805657 * 2 ^ 59
def prefixEnd_805657 : Nat := 4983230072969 + 3 ^ 40 * 805657 * 2
def baseEnd_805657 : Nat := 413689283659459596982357

theorem tailTrace_805657 : CollatzResearch.WordTrace tailWord_805657 prefixEnd_805657 413689283659459596982357 := by
  unfold tailWord_805657
  simp only [CollatzResearch.WordTrace]
  refine ⟨29384724842249759106191225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19589816561499839404127483 29384724842249759106191225)
  ·
    refine ⟨22038543631687319329643419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29384724842249759106191225 22038543631687319329643419)
    ·
      refine ⟨33057815447530978994465129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22038543631687319329643419 33057815447530978994465129)
      ·
        refine ⟨24793361585648234245848847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33057815447530978994465129 24793361585648234245848847)
        ·
          refine ⟨37190042378472351368773271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24793361585648234245848847 37190042378472351368773271)
          ·
            refine ⟨55785063567708527053159907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37190042378472351368773271 55785063567708527053159907)
            ·
              refine ⟨83677595351562790579739861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55785063567708527053159907 83677595351562790579739861)
              ·
                refine ⟨1961193641052252904212653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83677595351562790579739861 1961193641052252904212653)
                ·
                  refine ⟨735447615394594839079745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1961193641052252904212653 735447615394594839079745)
                  ·
                    refine ⟨551585711545946129309809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735447615394594839079745 551585711545946129309809)
                    ·
                      refine ⟨413689283659459596982357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551585711545946129309809 413689283659459596982357)
                      ·
                        rfl

theorem cell23_805657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_805657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805657 prefixEnd_805657 := by exact prefixLift 805657
  have htrace : WordTrace (prefixWord ++ tailWord_805657) baseStart_805657 baseEnd_805657 := by
    simpa [prefixWord, tailWord_805657, baseEnd_805657] using wordTrace_append hprefix tailTrace_805657
  have hstable : (prefixWord ++ tailWord_805657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805657).length < 2 ^ (prefixWord ++ tailWord_805657).sum := by decide
  have hdescent : baseEnd_805657 < baseStart_805657 := by decide
  rcases family_descends (prefixWord ++ tailWord_805657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805660 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_805660 : Nat := 118140960795 + 805660 * 2 ^ 59
def prefixEnd_805660 : Nat := 4983230072969 + 3 ^ 40 * 805660 * 2
def baseEnd_805660 : Nat := 413690824101423085244843

theorem tailTrace_805660 : CollatzResearch.WordTrace tailWord_805660 prefixEnd_805660 413690824101423085244843 := by
  unfold tailWord_805660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14692417130619445309275217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19589889507492593745700289 14692417130619445309275217)
  ·
    refine ⟨11019312847964583981956413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14692417130619445309275217 11019312847964583981956413)
    ·
      refine ⟨4132242317986718993233655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11019312847964583981956413 4132242317986718993233655)
      ·
        refine ⟨6198363476980078489850483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132242317986718993233655 6198363476980078489850483)
        ·
          refine ⟨9297545215470117734775725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198363476980078489850483 9297545215470117734775725)
          ·
            refine ⟨3486579455801294150540897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9297545215470117734775725 3486579455801294150540897)
            ·
              refine ⟨2614934591850970612905673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3486579455801294150540897 2614934591850970612905673)
              ·
                refine ⟨1961200943888227959679255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2614934591850970612905673 1961200943888227959679255)
                ·
                  refine ⟨2941801415832341939518883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961200943888227959679255 2941801415832341939518883)
                  ·
                    refine ⟨4412702123748512909278325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941801415832341939518883 4412702123748512909278325)
                    ·
                      refine ⟨413690824101423085244843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4412702123748512909278325 413690824101423085244843)
                      ·
                        rfl

theorem cell23_805660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_805660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805660 prefixEnd_805660 := by exact prefixLift 805660
  have htrace : WordTrace (prefixWord ++ tailWord_805660) baseStart_805660 baseEnd_805660 := by
    simpa [prefixWord, tailWord_805660, baseEnd_805660] using wordTrace_append hprefix tailTrace_805660
  have hstable : (prefixWord ++ tailWord_805660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805660).length < 2 ^ (prefixWord ++ tailWord_805660).sum := by decide
  have hdescent : baseEnd_805660 < baseStart_805660 := by decide
  rcases family_descends (prefixWord ++ tailWord_805660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805663 : List Nat := [1, 1, 2, 4, 2, 2, 1, 10]
def baseStart_805663 : Nat := 118140960795 + 805663 * 2 ^ 59
def prefixEnd_805663 : Nat := 4983230072969 + 3 ^ 40 * 805663 * 2
def baseEnd_805663 : Nat := 15321939427532836055827

theorem tailTrace_805663 : CollatzResearch.WordTrace tailWord_805663 prefixEnd_805663 15321939427532836055827 := by
  unfold tailWord_805663
  simp only [CollatzResearch.WordTrace]
  refine ⟨29384943680228022130909643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19589962453485348087273095 29384943680228022130909643)
  ·
    refine ⟨44077415520342033196364465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29384943680228022130909643 44077415520342033196364465)
    ·
      refine ⟨33058061640256524897273349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44077415520342033196364465 33058061640256524897273349)
      ·
        refine ⟨6198386557548098418238753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33058061640256524897273349 6198386557548098418238753)
        ·
          refine ⟨4648789918161073813679065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198386557548098418238753 4648789918161073813679065)
          ·
            refine ⟨3486592438620805360259299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4648789918161073813679065 3486592438620805360259299)
            ·
              refine ⟨5229888657931208040388949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486592438620805360259299 5229888657931208040388949)
              ·
                refine ⟨15321939427532836055827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5229888657931208040388949 15321939427532836055827)
                ·
                  rfl

theorem cell23_805663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 10].length) (baseStart_805663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805663 prefixEnd_805663 := by exact prefixLift 805663
  have htrace : WordTrace (prefixWord ++ tailWord_805663) baseStart_805663 baseEnd_805663 := by
    simpa [prefixWord, tailWord_805663, baseEnd_805663] using wordTrace_append hprefix tailTrace_805663
  have hstable : (prefixWord ++ tailWord_805663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805663).length < 2 ^ (prefixWord ++ tailWord_805663).sum := by decide
  have hdescent : baseEnd_805663 < baseStart_805663 := by decide
  rcases family_descends (prefixWord ++ tailWord_805663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805674 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_805674 : Nat := 118140960795 + 805674 * 2 ^ 59
def prefixEnd_805674 : Nat := 4983230072969 + 3 ^ 40 * 805674 * 2
def baseEnd_805674 : Nat := 413698012830586030469779

theorem tailTrace_805674 : CollatzResearch.WordTrace tailWord_805674 prefixEnd_805674 413698012830586030469779 := by
  unfold tailWord_805674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346336220797042752390019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19590229922125447339706717 7346336220797042752390019)
  ·
    refine ⟨11019504331195564128585029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7346336220797042752390019 11019504331195564128585029)
    ·
      refine ⟨2066157062099168274109693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11019504331195564128585029 2066157062099168274109693)
      ·
        refine ⟨774808898287188102791135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2066157062099168274109693 774808898287188102791135)
        ·
          refine ⟨1162213347430782154186703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774808898287188102791135 1162213347430782154186703)
          ·
            refine ⟨1743320021146173231280055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162213347430782154186703 1743320021146173231280055)
            ·
              refine ⟨2614980031719259846920083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743320021146173231280055 2614980031719259846920083)
              ·
                refine ⟨3922470047578889770380125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614980031719259846920083 3922470047578889770380125)
                ·
                  refine ⟨1470926267842083663892547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3922470047578889770380125 1470926267842083663892547)
                  ·
                    refine ⟨2206389401763125495838821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1470926267842083663892547 2206389401763125495838821)
                    ·
                      refine ⟨413698012830586030469779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2206389401763125495838821 413698012830586030469779)
                      ·
                        rfl

theorem cell23_805674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_805674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805674 prefixEnd_805674 := by exact prefixLift 805674
  have htrace : WordTrace (prefixWord ++ tailWord_805674) baseStart_805674 baseEnd_805674 := by
    simpa [prefixWord, tailWord_805674, baseEnd_805674] using wordTrace_append hprefix tailTrace_805674
  have hstable : (prefixWord ++ tailWord_805674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805674).length < 2 ^ (prefixWord ++ tailWord_805674).sum := by decide
  have hdescent : baseEnd_805674 < baseStart_805674 := by decide
  rcases family_descends (prefixWord ++ tailWord_805674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805694 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_805694 : Nat := 118140960795 + 805694 * 2 ^ 59
def prefixEnd_805694 : Nat := 4983230072969 + 3 ^ 40 * 805694 * 2
def baseEnd_805694 : Nat := 413708282443675952219687

theorem tailTrace_805694 : CollatzResearch.WordTrace tailWord_805694 prefixEnd_805694 413708282443675952219687 := by
  unfold tailWord_805694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673259292889464303161017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19590716228743809616858757 3673259292889464303161017)
  ·
    refine ⟨2754944469667098227370763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3673259292889464303161017 2754944469667098227370763)
    ·
      refine ⟨4132416704500647341056145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754944469667098227370763 4132416704500647341056145)
      ·
        refine ⟨3099312528375485505792109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4132416704500647341056145 3099312528375485505792109)
        ·
          refine ⟨1162242198140807064672041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3099312528375485505792109 1162242198140807064672041)
          ·
            refine ⟨871681648605605298504031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162242198140807064672041 871681648605605298504031)
            ·
              refine ⟨1307522472908407947756047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871681648605605298504031 1307522472908407947756047)
              ·
                refine ⟨1961283709362611921634071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307522472908407947756047 1961283709362611921634071)
                ·
                  refine ⟨2941925564043917882451107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961283709362611921634071 2941925564043917882451107)
                  ·
                    refine ⟨4412888346065876823676661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941925564043917882451107 4412888346065876823676661)
                    ·
                      refine ⟨413708282443675952219687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4412888346065876823676661 413708282443675952219687)
                      ·
                        rfl

theorem cell23_805694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_805694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805694 prefixEnd_805694 := by exact prefixLift 805694
  have htrace : WordTrace (prefixWord ++ tailWord_805694) baseStart_805694 baseEnd_805694 := by
    simpa [prefixWord, tailWord_805694, baseEnd_805694] using wordTrace_append hprefix tailTrace_805694
  have hstable : (prefixWord ++ tailWord_805694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805694).length < 2 ^ (prefixWord ++ tailWord_805694).sum := by decide
  have hdescent : baseEnd_805694 < baseStart_805694 := by decide
  rcases family_descends (prefixWord ++ tailWord_805694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805697 : List Nat := [1, 2, 5, 3, 2, 10]
def baseStart_805697 : Nat := 118140960795 + 805697 * 2 ^ 59
def prefixEnd_805697 : Nat := 4983230072969 + 3 ^ 40 * 805697 * 2
def baseEnd_805697 : Nat := 1702509559200162306511

theorem tailTrace_805697 : CollatzResearch.WordTrace tailWord_805697 prefixEnd_805697 1702509559200162306511 := by
  unfold tailWord_805697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386183762104845937647345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19590789174736563958431563 29386183762104845937647345)
  ·
    refine ⟨22039637821578634453235509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29386183762104845937647345 22039637821578634453235509)
    ·
      refine ⟨2066216045772996979990829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22039637821578634453235509 2066216045772996979990829)
      ·
        refine ⟨774831017164873867496561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2066216045772996979990829 774831017164873867496561)
        ·
          refine ⟨581123262873655400622421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774831017164873867496561 581123262873655400622421)
          ·
            refine ⟨1702509559200162306511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 581123262873655400622421 1702509559200162306511)
            ·
              rfl

theorem cell23_805697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 10].length) (baseStart_805697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805697 prefixEnd_805697 := by exact prefixLift 805697
  have htrace : WordTrace (prefixWord ++ tailWord_805697) baseStart_805697 baseEnd_805697 := by
    simpa [prefixWord, tailWord_805697, baseEnd_805697] using wordTrace_append hprefix tailTrace_805697
  have hstable : (prefixWord ++ tailWord_805697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805697).length < 2 ^ (prefixWord ++ tailWord_805697).sum := by decide
  have hdescent : baseEnd_805697 < baseStart_805697 := by decide
  rcases family_descends (prefixWord ++ tailWord_805697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805702 : List Nat := [6, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_805702 : Nat := 118140960795 + 805702 * 2 ^ 59
def prefixEnd_805702 : Nat := 4983230072969 + 3 ^ 40 * 805702 * 2
def baseEnd_805702 : Nat := 413712390288911920919651

theorem tailTrace_805702 : CollatzResearch.WordTrace tailWord_805702 prefixEnd_805702 413712390288911920919651 := by
  unfold tailWord_805702
  simp only [CollatzResearch.WordTrace]
  refine ⟨918323941471460368486855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19590910751391154527719573 918323941471460368486855)
  ·
    refine ⟨1377485912207190552730283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918323941471460368486855 1377485912207190552730283)
    ·
      refine ⟨2066228868310785829095425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377485912207190552730283 2066228868310785829095425)
      ·
        refine ⟨1549671651233089371821569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066228868310785829095425 1549671651233089371821569)
        ·
          refine ⟨1162253738424817028866177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549671651233089371821569 1162253738424817028866177)
          ·
            refine ⟨871690303818612771649633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162253738424817028866177 871690303818612771649633)
            ·
              refine ⟨653767727863959578737225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871690303818612771649633 653767727863959578737225)
              ·
                refine ⟨490325795897969684052919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653767727863959578737225 490325795897969684052919)
                ·
                  refine ⟨735488693846954526079379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490325795897969684052919 735488693846954526079379)
                  ·
                    refine ⟨1103233040770431789119069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 735488693846954526079379 1103233040770431789119069)
                    ·
                      refine ⟨413712390288911920919651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1103233040770431789119069 413712390288911920919651)
                      ·
                        rfl

theorem cell23_805702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_805702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805702 prefixEnd_805702 := by exact prefixLift 805702
  have htrace : WordTrace (prefixWord ++ tailWord_805702) baseStart_805702 baseEnd_805702 := by
    simpa [prefixWord, tailWord_805702, baseEnd_805702] using wordTrace_append hprefix tailTrace_805702
  have hstable : (prefixWord ++ tailWord_805702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805702).length < 2 ^ (prefixWord ++ tailWord_805702).sum := by decide
  have hdescent : baseEnd_805702 < baseStart_805702 := by decide
  rcases family_descends (prefixWord ++ tailWord_805702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805708 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 1, 2, 2]
def baseStart_805708 : Nat := 118140960795 + 805708 * 2 ^ 59
def prefixEnd_805708 : Nat := 4983230072969 + 3 ^ 40 * 805708 * 2
def baseEnd_805708 : Nat := 413715471172838897444623

theorem tailTrace_805708 : CollatzResearch.WordTrace tailWord_805708 prefixEnd_805708 413715471172838897444623 := by
  unfold tailWord_805708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693292482532497408148889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19591056643376663210865185 14693292482532497408148889)
  ·
    refine ⟨11019969361899373056111667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14693292482532497408148889 11019969361899373056111667)
    ·
      refine ⟨16529954042849059584167501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11019969361899373056111667 16529954042849059584167501)
      ·
        refine ⟨6198732766068397344062813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16529954042849059584167501 6198732766068397344062813)
        ·
          refine ⟨2324524787275649004023555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6198732766068397344062813 2324524787275649004023555)
          ·
            refine ⟨3486787180913473506035333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324524787275649004023555 3486787180913473506035333)
            ·
              refine ⟨653772596421276282381625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3486787180913473506035333 653772596421276282381625)
              ·
                refine ⟨490329447315957211786219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653772596421276282381625 490329447315957211786219)
                ·
                  refine ⟨735494170973935817679329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490329447315957211786219 735494170973935817679329)
                  ·
                    refine ⟨551620628230451863259497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735494170973935817679329 551620628230451863259497)
                    ·
                      refine ⟨413715471172838897444623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551620628230451863259497 413715471172838897444623)
                      ·
                        rfl

theorem cell23_805708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_805708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805708 prefixEnd_805708 := by exact prefixLift 805708
  have htrace : WordTrace (prefixWord ++ tailWord_805708) baseStart_805708 baseEnd_805708 := by
    simpa [prefixWord, tailWord_805708, baseEnd_805708] using wordTrace_append hprefix tailTrace_805708
  have hstable : (prefixWord ++ tailWord_805708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805708).length < 2 ^ (prefixWord ++ tailWord_805708).sum := by decide
  have hdescent : baseEnd_805708 < baseStart_805708 := by decide
  rcases family_descends (prefixWord ++ tailWord_805708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805717 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_805717 : Nat := 118140960795 + 805717 * 2 ^ 59
def prefixEnd_805717 : Nat := 4983230072969 + 3 ^ 40 * 805717 * 2
def baseEnd_805717 : Nat := 413720092498729362232081

theorem tailTrace_805717 : CollatzResearch.WordTrace tailWord_805717 prefixEnd_805717 413720092498729362232081 := by
  unfold tailWord_805717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386913222032389353375405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19591275481354926235583603 29386913222032389353375405)
  ·
    refine ⟨11020092458262146007515777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29386913222032389353375405 11020092458262146007515777)
    ·
      refine ⟨8265069343696609505636833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11020092458262146007515777 8265069343696609505636833)
      ·
        refine ⟨6198802007772457129227625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8265069343696609505636833 6198802007772457129227625)
        ·
          refine ⟨4649101505829342846920719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198802007772457129227625 4649101505829342846920719)
          ·
            refine ⟨6973652258744014270381079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649101505829342846920719 6973652258744014270381079)
            ·
              refine ⟨10460478388116021405571619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973652258744014270381079 10460478388116021405571619)
              ·
                refine ⟨15690717582174032108357429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460478388116021405571619 15690717582174032108357429)
                ·
                  refine ⟨1471004773328815510158509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15690717582174032108357429 1471004773328815510158509)
                  ·
                    refine ⟨551626789998305816309441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471004773328815510158509 551626789998305816309441)
                    ·
                      refine ⟨413720092498729362232081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551626789998305816309441 413720092498729362232081)
                      ·
                        rfl

theorem cell23_805717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_805717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805717 prefixEnd_805717 := by exact prefixLift 805717
  have htrace : WordTrace (prefixWord ++ tailWord_805717) baseStart_805717 baseEnd_805717 := by
    simpa [prefixWord, tailWord_805717, baseEnd_805717] using wordTrace_append hprefix tailTrace_805717
  have hstable : (prefixWord ++ tailWord_805717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805717).length < 2 ^ (prefixWord ++ tailWord_805717).sum := by decide
  have hdescent : baseEnd_805717 < baseStart_805717 := by decide
  rcases family_descends (prefixWord ++ tailWord_805717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805724 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_805724 : Nat := 118140960795 + 805724 * 2 ^ 59
def prefixEnd_805724 : Nat := 4983230072969 + 3 ^ 40 * 805724 * 2
def baseEnd_805724 : Nat := 413723686863310834844549

theorem tailTrace_805724 : CollatzResearch.WordTrace tailWord_805724 prefixEnd_805724 413723686863310834844549 := by
  unfold tailWord_805724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693584266503514774440113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19591445688671353032586817 14693584266503514774440113)
  ·
    refine ⟨11020188199877636080830085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14693584266503514774440113 11020188199877636080830085)
    ·
      refine ⟨2066285287477056765155641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11020188199877636080830085 2066285287477056765155641)
      ·
        refine ⟨1549713965607792573866731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066285287477056765155641 1549713965607792573866731)
        ·
          refine ⟨2324570948411688860800097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549713965607792573866731 2324570948411688860800097)
          ·
            refine ⟨1743428211308766645600073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324570948411688860800097 1743428211308766645600073)
            ·
              refine ⟨1307571158481574984200055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743428211308766645600073 1307571158481574984200055)
              ·
                refine ⟨1961356737722362476300083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307571158481574984200055 1961356737722362476300083)
                ·
                  refine ⟨2942035106583543714450125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961356737722362476300083 2942035106583543714450125)
                  ·
                    refine ⟨1103263164968828892918797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942035106583543714450125 1103263164968828892918797)
                    ·
                      refine ⟨413723686863310834844549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1103263164968828892918797 413723686863310834844549)
                      ·
                        rfl

theorem cell23_805724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_805724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805724 prefixEnd_805724 := by exact prefixLift 805724
  have htrace : WordTrace (prefixWord ++ tailWord_805724) baseStart_805724 baseEnd_805724 := by
    simpa [prefixWord, tailWord_805724, baseEnd_805724] using wordTrace_append hprefix tailTrace_805724
  have hstable : (prefixWord ++ tailWord_805724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805724).length < 2 ^ (prefixWord ++ tailWord_805724).sum := by decide
  have hdescent : baseEnd_805724 < baseStart_805724 := by decide
  rcases family_descends (prefixWord ++ tailWord_805724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805747 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 1, 4, 2]
def baseStart_805747 : Nat := 118140960795 + 805747 * 2 ^ 59
def prefixEnd_805747 : Nat := 4983230072969 + 3 ^ 40 * 805747 * 2
def baseEnd_805747 : Nat := 413735496918364244856943

theorem tailTrace_805747 : CollatzResearch.WordTrace tailWord_805747 prefixEnd_805747 413735496918364244856943 := by
  unfold tailWord_805747
  simp only [CollatzResearch.WordTrace]
  refine ⟨29388007411923704476967495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19592004941282469651311663 29388007411923704476967495)
  ·
    refine ⟨44082011117885556715451243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29388007411923704476967495 44082011117885556715451243)
    ·
      refine ⟨66123016676828335073176865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44082011117885556715451243 66123016676828335073176865)
      ·
        refine ⟨49592262507621251304882649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66123016676828335073176865 49592262507621251304882649)
        ·
          refine ⟨37194196880715938478661987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49592262507621251304882649 37194196880715938478661987)
          ·
            refine ⟨55791295321073907717992981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37194196880715938478661987 55791295321073907717992981)
            ·
              refine ⟨2615216968175339424280921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55791295321073907717992981 2615216968175339424280921)
              ·
                refine ⟨1961412726131504568210691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2615216968175339424280921 1961412726131504568210691)
                ·
                  refine ⟨2942119089197256852316037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961412726131504568210691 2942119089197256852316037)
                  ·
                    refine ⟨551647329224485659809257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2942119089197256852316037 551647329224485659809257)
                    ·
                      refine ⟨413735496918364244856943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551647329224485659809257 413735496918364244856943)
                      ·
                        rfl

theorem cell23_805747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 4, 2].length) (baseStart_805747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805747 prefixEnd_805747 := by exact prefixLift 805747
  have htrace : WordTrace (prefixWord ++ tailWord_805747) baseStart_805747 baseEnd_805747 := by
    simpa [prefixWord, tailWord_805747, baseEnd_805747] using wordTrace_append hprefix tailTrace_805747
  have hstable : (prefixWord ++ tailWord_805747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805747).length < 2 ^ (prefixWord ++ tailWord_805747).sum := by decide
  have hdescent : baseEnd_805747 < baseStart_805747 := by decide
  rcases family_descends (prefixWord ++ tailWord_805747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805817 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_805817 : Nat := 118140960795 + 805817 * 2 ^ 59
def prefixEnd_805817 : Nat := 4983230072969 + 3 ^ 40 * 805817 * 2
def baseEnd_805817 : Nat := 137923813521392990327207

theorem tailTrace_805817 : CollatzResearch.WordTrace tailWord_805817 prefixEnd_805817 137923813521392990327207 := by
  unfold tailWord_805817
  simp only [CollatzResearch.WordTrace]
  refine ⟨29390560521670106432015705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19593707014446737621343803 29390560521670106432015705)
  ·
    refine ⟨22042920391252579824011779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29390560521670106432015705 22042920391252579824011779)
    ·
      refine ⟨33064380586878869736017669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22042920391252579824011779 33064380586878869736017669)
      ·
        refine ⟨6199571360039788075503313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33064380586878869736017669 6199571360039788075503313)
        ·
          refine ⟨4649678520029841056627485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6199571360039788075503313 4649678520029841056627485)
          ·
            refine ⟨1743629445011190396235307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4649678520029841056627485 1743629445011190396235307)
            ·
              refine ⟨2615444167516785594352961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743629445011190396235307 2615444167516785594352961)
              ·
                refine ⟨1961583125637589195764721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2615444167516785594352961 1961583125637589195764721)
                ·
                  refine ⟨1471187344228191896823541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961583125637589195764721 1471187344228191896823541)
                  ·
                    refine ⟨137923813521392990327207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1471187344228191896823541 137923813521392990327207)
                    ·
                      rfl

theorem cell23_805817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_805817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805817 prefixEnd_805817 := by exact prefixLift 805817
  have htrace : WordTrace (prefixWord ++ tailWord_805817) baseStart_805817 baseEnd_805817 := by
    simpa [prefixWord, tailWord_805817, baseEnd_805817] using wordTrace_append hprefix tailTrace_805817
  have hstable : (prefixWord ++ tailWord_805817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805817).length < 2 ^ (prefixWord ++ tailWord_805817).sum := by decide
  have hdescent : baseEnd_805817 < baseStart_805817 := by decide
  rcases family_descends (prefixWord ++ tailWord_805817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805821 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 5]
def baseStart_805821 : Nat := 118140960795 + 805821 * 2 ^ 59
def prefixEnd_805821 : Nat := 4983230072969 + 3 ^ 40 * 805821 * 2
def baseEnd_805821 : Nat := 45974832720755217259067

theorem tailTrace_805821 : CollatzResearch.WordTrace tailWord_805821 prefixEnd_805821 45974832720755217259067 := by
  unfold tailWord_805821
  simp only [CollatzResearch.WordTrace]
  refine ⟨29390706413655615115161317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19593804275770410076774211 29390706413655615115161317)
  ·
    refine ⟨5510757452560427834092747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29390706413655615115161317 5510757452560427834092747)
    ·
      refine ⟨8266136178840641751139121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510757452560427834092747 8266136178840641751139121)
      ·
        refine ⟨6199602134130481313354341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8266136178840641751139121 6199602134130481313354341)
        ·
          refine ⟨1162425400149465246253939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6199602134130481313354341 1162425400149465246253939)
          ·
            refine ⟨1743638100224197869380909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162425400149465246253939 1743638100224197869380909)
            ·
              refine ⟨653864287584074201017841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1743638100224197869380909 653864287584074201017841)
              ·
                refine ⟨490398215688055650763381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653864287584074201017841 490398215688055650763381)
                ·
                  refine ⟨45974832720755217259067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490398215688055650763381 45974832720755217259067)
                  ·
                    rfl

theorem cell23_805821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_805821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805821 prefixEnd_805821 := by exact prefixLift 805821
  have htrace : WordTrace (prefixWord ++ tailWord_805821) baseStart_805821 baseEnd_805821 := by
    simpa [prefixWord, tailWord_805821, baseEnd_805821] using wordTrace_append hprefix tailTrace_805821
  have hstable : (prefixWord ++ tailWord_805821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805821).length < 2 ^ (prefixWord ++ tailWord_805821).sum := by decide
  have hdescent : baseEnd_805821 < baseStart_805821 := by decide
  rcases family_descends (prefixWord ++ tailWord_805821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805860 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 8]
def baseStart_805860 : Nat := 118140960795 + 805860 * 2 ^ 59
def prefixEnd_805860 : Nat := 4983230072969 + 3 ^ 40 * 805860 * 2
def baseEnd_805860 : Nat := 45977057803591366971547

theorem tailTrace_805860 : CollatzResearch.WordTrace tailWord_805860 prefixEnd_805860 45977057803591366971547 := by
  unfold tailWord_805860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696064430257162387915517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19594752573676216517220689 14696064430257162387915517)
  ·
    refine ⟨5511024161346435895468319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14696064430257162387915517 5511024161346435895468319)
    ·
      refine ⟨8266536242019653843202479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5511024161346435895468319 8266536242019653843202479)
      ·
        refine ⟨12399804363029480764803719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8266536242019653843202479 12399804363029480764803719)
        ·
          refine ⟨18599706544544221147205579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12399804363029480764803719 18599706544544221147205579)
          ·
            refine ⟨27899559816816331720808369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18599706544544221147205579 27899559816816331720808369)
            ·
              refine ⟨20924669862612248790606277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27899559816816331720808369 20924669862612248790606277)
              ·
                refine ⟨3923375599239796648238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20924669862612248790606277 3923375599239796648238677)
                ·
                  refine ⟨45977057803591366971547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3923375599239796648238677 45977057803591366971547)
                  ·
                    rfl

theorem cell23_805860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_805860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805860 prefixEnd_805860 := by exact prefixLift 805860
  have htrace : WordTrace (prefixWord ++ tailWord_805860) baseStart_805860 baseEnd_805860 := by
    simpa [prefixWord, tailWord_805860, baseEnd_805860] using wordTrace_append hprefix tailTrace_805860
  have hstable : (prefixWord ++ tailWord_805860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805860).length < 2 ^ (prefixWord ++ tailWord_805860).sum := by decide
  have hdescent : baseEnd_805860 < baseStart_805860 := by decide
  rcases family_descends (prefixWord ++ tailWord_805860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805880 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_805880 : Nat := 118140960795 + 805880 * 2 ^ 59
def prefixEnd_805880 : Nat := 4983230072969 + 3 ^ 40 * 805880 * 2
def baseEnd_805880 : Nat := 413803789845412224493831

theorem tailTrace_805880 : CollatzResearch.WordTrace tailWord_805880 prefixEnd_805880 413803789845412224493831 := by
  unfold tailWord_805880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696429160220934095779547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19595238880294578794372729 14696429160220934095779547)
  ·
    refine ⟨22044643740331401143669321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14696429160220934095779547 22044643740331401143669321)
    ·
      refine ⟨16533482805248550857751991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22044643740331401143669321 16533482805248550857751991)
      ·
        refine ⟨24800224207872826286627987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16533482805248550857751991 24800224207872826286627987)
        ·
          refine ⟨37200336311809239429941981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24800224207872826286627987 37200336311809239429941981)
          ·
            refine ⟨13950126116928464786228243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37200336311809239429941981 13950126116928464786228243)
            ·
              refine ⟨20925189175392697179342365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13950126116928464786228243 20925189175392697179342365)
              ·
                refine ⟨7846945940772261442253387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20925189175392697179342365 7846945940772261442253387)
                ·
                  refine ⟨11770418911158392163380081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846945940772261442253387 11770418911158392163380081)
                  ·
                    refine ⟨8827814183368794122535061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11770418911158392163380081 8827814183368794122535061)
                    ·
                      refine ⟨413803789845412224493831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8827814183368794122535061 413803789845412224493831)
                      ·
                        rfl

theorem cell23_805880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_805880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805880 prefixEnd_805880 := by exact prefixLift 805880
  have htrace : WordTrace (prefixWord ++ tailWord_805880) baseStart_805880 baseEnd_805880 := by
    simpa [prefixWord, tailWord_805880, baseEnd_805880] using wordTrace_append hprefix tailTrace_805880
  have hstable : (prefixWord ++ tailWord_805880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805880).length < 2 ^ (prefixWord ++ tailWord_805880).sum := by decide
  have hdescent : baseEnd_805880 < baseStart_805880 := by decide
  rcases family_descends (prefixWord ++ tailWord_805880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805907 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 1, 5]
def baseStart_805907 : Nat := 118140960795 + 805907 * 2 ^ 59
def prefixEnd_805907 : Nat := 4983230072969 + 3 ^ 40 * 805907 * 2
def baseEnd_805907 : Nat := 137939217941027872952069

theorem tailTrace_805907 : CollatzResearch.WordTrace tailWord_805907 prefixEnd_805907 137939217941027872952069 := by
  unfold tailWord_805907
  simp only [CollatzResearch.WordTrace]
  refine ⟨29393843091344051802791975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19595895394229367868527983 29393843091344051802791975)
  ·
    refine ⟨44090764637016077704187963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29393843091344051802791975 44090764637016077704187963)
    ·
      refine ⟨66136146955524116556281945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44090764637016077704187963 66136146955524116556281945)
      ·
        refine ⟨49602110216643087417211459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66136146955524116556281945 49602110216643087417211459)
        ·
          refine ⟨74403165324964631125817189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49602110216643087417211459 74403165324964631125817189)
          ·
            refine ⟨13950593498430868336090723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74403165324964631125817189 13950593498430868336090723)
            ·
              refine ⟨20925890247646302504136085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13950593498430868336090723 20925890247646302504136085)
              ·
                refine ⟨980901105358420429881379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20925890247646302504136085 980901105358420429881379)
                ·
                  refine ⟨1471351658037630644822069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980901105358420429881379 1471351658037630644822069)
                  ·
                    refine ⟨137939217941027872952069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1471351658037630644822069 137939217941027872952069)
                    ·
                      rfl

theorem cell23_805907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 5].length) (baseStart_805907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805907 prefixEnd_805907 := by exact prefixLift 805907
  have htrace : WordTrace (prefixWord ++ tailWord_805907) baseStart_805907 baseEnd_805907 := by
    simpa [prefixWord, tailWord_805907, baseEnd_805907] using wordTrace_append hprefix tailTrace_805907
  have hstable : (prefixWord ++ tailWord_805907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805907).length < 2 ^ (prefixWord ++ tailWord_805907).sum := by decide
  have hdescent : baseEnd_805907 < baseStart_805907 := by decide
  rcases family_descends (prefixWord ++ tailWord_805907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805914 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_805914 : Nat := 118140960795 + 805914 * 2 ^ 59
def prefixEnd_805914 : Nat := 4983230072969 + 3 ^ 40 * 805914 * 2
def baseEnd_805914 : Nat := 413821248187665091468675

theorem tailTrace_805914 : CollatzResearch.WordTrace tailWord_805914 prefixEnd_805914 413821248187665091468675 := by
  unfold tailWord_805914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348524600579672999574199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19596065601545794665531197 7348524600579672999574199)
  ·
    refine ⟨11022786900869509499361299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348524600579672999574199 11022786900869509499361299)
    ·
      refine ⟨16534180351304264249041949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11022786900869509499361299 16534180351304264249041949)
      ·
        refine ⟨6200317631739099093390731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16534180351304264249041949 6200317631739099093390731)
        ·
          refine ⟨9300476447608648640086097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200317631739099093390731 9300476447608648640086097)
          ·
            refine ⟨6975357335706486480064573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300476447608648640086097 6975357335706486480064573)
            ·
              refine ⟨2615759000889932430024215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6975357335706486480064573 2615759000889932430024215)
              ·
                refine ⟨3923638501334898645036323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615759000889932430024215 3923638501334898645036323)
                ·
                  refine ⟨5885457752002347967554485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923638501334898645036323 5885457752002347967554485)
                  ·
                    refine ⟨551761664250220121958233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5885457752002347967554485 551761664250220121958233)
                    ·
                      refine ⟨413821248187665091468675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551761664250220121958233 413821248187665091468675)
                      ·
                        rfl

theorem cell23_805914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_805914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805914 prefixEnd_805914 := by exact prefixLift 805914
  have htrace : WordTrace (prefixWord ++ tailWord_805914) baseStart_805914 baseEnd_805914 := by
    simpa [prefixWord, tailWord_805914, baseEnd_805914] using wordTrace_append hprefix tailTrace_805914
  have hstable : (prefixWord ++ tailWord_805914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805914).length < 2 ^ (prefixWord ++ tailWord_805914).sum := by decide
  have hdescent : baseEnd_805914 < baseStart_805914 := by decide
  rcases family_descends (prefixWord ++ tailWord_805914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805958 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_805958 : Nat := 118140960795 + 805958 * 2 ^ 59
def prefixEnd_805958 : Nat := 4983230072969 + 3 ^ 40 * 805958 * 2
def baseEnd_805958 : Nat := 137947947112154306439491

theorem tailTrace_805958 : CollatzResearch.WordTrace tailWord_805958 prefixEnd_805958 137947947112154306439491 := by
  unfold tailWord_805958
  simp only [CollatzResearch.WordTrace]
  refine ⟨918615725442477734778079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19597135476106191675265685 918615725442477734778079)
  ·
    refine ⟨1377923588163716602167119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918615725442477734778079 1377923588163716602167119)
    ·
      refine ⟨2066885382245574903250679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377923588163716602167119 2066885382245574903250679)
      ·
        refine ⟨3100328073368362354876019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066885382245574903250679 3100328073368362354876019)
        ·
          refine ⟨4650492110052543532314029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100328073368362354876019 4650492110052543532314029)
          ·
            refine ⟨1743934541269703824617761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4650492110052543532314029 1743934541269703824617761)
            ·
              refine ⟨1307950905952277868463321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743934541269703824617761 1307950905952277868463321)
              ·
                refine ⟨980963179464208401347491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307950905952277868463321 980963179464208401347491)
                ·
                  refine ⟨1471444769196312602021237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980963179464208401347491 1471444769196312602021237)
                  ·
                    refine ⟨137947947112154306439491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1471444769196312602021237 137947947112154306439491)
                    ·
                      rfl

theorem cell23_805958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_805958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805958 prefixEnd_805958 := by exact prefixLift 805958
  have htrace : WordTrace (prefixWord ++ tailWord_805958) baseStart_805958 baseEnd_805958 := by
    simpa [prefixWord, tailWord_805958, baseEnd_805958] using wordTrace_append hprefix tailTrace_805958
  have hstable : (prefixWord ++ tailWord_805958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805958).length < 2 ^ (prefixWord ++ tailWord_805958).sum := by decide
  have hdescent : baseEnd_805958 < baseStart_805958 := by decide
  rcases family_descends (prefixWord ++ tailWord_805958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805978 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2]
def baseStart_805978 : Nat := 118140960795 + 805978 * 2 ^ 59
def prefixEnd_805978 : Nat := 4983230072969 + 3 ^ 40 * 805978 * 2
def baseEnd_805978 : Nat := 413854110949552841068381

theorem tailTrace_805978 : CollatzResearch.WordTrace tailWord_805978 prefixEnd_805978 413854110949552841068381 := by
  unfold tailWord_805978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349108168521707732156647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19597621782724553952417725 7349108168521707732156647)
  ·
    refine ⟨11023662252782561598234971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7349108168521707732156647 11023662252782561598234971)
    ·
      refine ⟨16535493379173842397352457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023662252782561598234971 16535493379173842397352457)
      ·
        refine ⟨12401620034380381798014343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16535493379173842397352457 12401620034380381798014343)
        ·
          refine ⟨18602430051570572697021515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12401620034380381798014343 18602430051570572697021515)
          ·
            refine ⟨27903645077355859045532273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18602430051570572697021515 27903645077355859045532273)
            ·
              refine ⟨20927733808016894284149205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27903645077355859045532273 20927733808016894284149205)
              ·
                refine ⟨490493761125395959784747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20927733808016894284149205 490493761125395959784747)
                ·
                  refine ⟨735740641688093939677121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490493761125395959784747 735740641688093939677121)
                  ·
                    refine ⟨551805481266070454757841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735740641688093939677121 551805481266070454757841)
                    ·
                      refine ⟨413854110949552841068381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551805481266070454757841 413854110949552841068381)
                      ·
                        rfl

theorem cell23_805978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_805978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805978 prefixEnd_805978 := by exact prefixLift 805978
  have htrace : WordTrace (prefixWord ++ tailWord_805978) baseStart_805978 baseEnd_805978 := by
    simpa [prefixWord, tailWord_805978, baseEnd_805978] using wordTrace_append hprefix tailTrace_805978
  have hstable : (prefixWord ++ tailWord_805978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805978).length < 2 ^ (prefixWord ++ tailWord_805978).sum := by decide
  have hdescent : baseEnd_805978 < baseStart_805978 := by decide
  rcases family_descends (prefixWord ++ tailWord_805978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806037 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_806037 : Nat := 118140960795 + 806037 * 2 ^ 59
def prefixEnd_806037 : Nat := 4983230072969 + 3 ^ 40 * 806037 * 2
def baseEnd_806037 : Nat := 413884406308168110230609

theorem tailTrace_806037 : CollatzResearch.WordTrace tailWord_806037 prefixEnd_806037 413884406308168110230609 := by
  unfold tailWord_806037
  simp only [CollatzResearch.WordTrace]
  refine ⟨29398584580873084005024365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19599056387248722670016243 29398584580873084005024365)
  ·
    refine ⟨11024469217827406501884137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29398584580873084005024365 11024469217827406501884137)
    ·
      refine ⟨8268351913370554876413103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11024469217827406501884137 8268351913370554876413103)
      ·
        refine ⟨12402527870055832314619655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268351913370554876413103 12402527870055832314619655)
        ·
          refine ⟨18603791805083748471929483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402527870055832314619655 18603791805083748471929483)
          ·
            refine ⟨27905687707625622707894225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18603791805083748471929483 27905687707625622707894225)
            ·
              refine ⟨20929265780719217030920669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27905687707625622707894225 20929265780719217030920669)
              ·
                refine ⟨7848474667769706386595251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20929265780719217030920669 7848474667769706386595251)
                ·
                  refine ⟨11772712001654559579892877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7848474667769706386595251 11772712001654559579892877)
                  ·
                    refine ⟨4414767000620459842459829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11772712001654559579892877 4414767000620459842459829)
                    ·
                      refine ⟨413884406308168110230609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4414767000620459842459829 413884406308168110230609)
                      ·
                        rfl

theorem cell23_806037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_806037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806037 prefixEnd_806037 := by exact prefixLift 806037
  have htrace : WordTrace (prefixWord ++ tailWord_806037) baseStart_806037 baseEnd_806037 := by
    simpa [prefixWord, tailWord_806037, baseEnd_806037] using wordTrace_append hprefix tailTrace_806037
  have hstable : (prefixWord ++ tailWord_806037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806037).length < 2 ^ (prefixWord ++ tailWord_806037).sum := by decide
  have hdescent : baseEnd_806037 < baseStart_806037 := by decide
  rcases family_descends (prefixWord ++ tailWord_806037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806051 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 4, 2, 2]
def baseStart_806051 : Nat := 118140960795 + 806051 * 2 ^ 59
def prefixEnd_806051 : Nat := 4983230072969 + 3 ^ 40 * 806051 * 2
def baseEnd_806051 : Nat := 413891595037331055455545

theorem tailTrace_806051 : CollatzResearch.WordTrace tailWord_806051 prefixEnd_806051 413891595037331055455545 := by
  unfold tailWord_806051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29399095202822364396034007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19599396801881576264022671 29399095202822364396034007)
  ·
    refine ⟨44098642804233546594051011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29399095202822364396034007 44098642804233546594051011)
    ·
      refine ⟨66147964206350319891076517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44098642804233546594051011 66147964206350319891076517)
      ·
        refine ⟨12402743288690684979576847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66147964206350319891076517 12402743288690684979576847)
        ·
          refine ⟨18604114933036027469365271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402743288690684979576847 18604114933036027469365271)
          ·
            refine ⟨27906172399554041204047907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18604114933036027469365271 27906172399554041204047907)
            ·
              refine ⟨41859258599331061806071861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27906172399554041204047907 41859258599331061806071861)
              ·
                refine ⟨3924305493687287044319237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41859258599331061806071861 3924305493687287044319237)
                ·
                  refine ⟨735807280066366320809857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3924305493687287044319237 735807280066366320809857)
                  ·
                    refine ⟨551855460049774740607393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735807280066366320809857 551855460049774740607393)
                    ·
                      refine ⟨413891595037331055455545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551855460049774740607393 413891595037331055455545)
                      ·
                        rfl

theorem cell23_806051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_806051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806051 prefixEnd_806051 := by exact prefixLift 806051
  have htrace : WordTrace (prefixWord ++ tailWord_806051) baseStart_806051 baseEnd_806051 := by
    simpa [prefixWord, tailWord_806051, baseEnd_806051] using wordTrace_append hprefix tailTrace_806051
  have hstable : (prefixWord ++ tailWord_806051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806051).length < 2 ^ (prefixWord ++ tailWord_806051).sum := by decide
  have hdescent : baseEnd_806051 < baseStart_806051 := by decide
  rcases family_descends (prefixWord ++ tailWord_806051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806061 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_806061 : Nat := 118140960795 + 806061 * 2 ^ 59
def prefixEnd_806061 : Nat := 4983230072969 + 3 ^ 40 * 806061 * 2
def baseEnd_806061 : Nat := 137965576614625338776833

theorem tailTrace_806061 : CollatzResearch.WordTrace tailWord_806061 prefixEnd_806061 137965576614625338776833 := by
  unfold tailWord_806061
  simp only [CollatzResearch.WordTrace]
  refine ⟨29399459932786136103898037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19599639955190757402598691 29399459932786136103898037)
  ·
    refine ⟨2756199368698700259740441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29399459932786136103898037 2756199368698700259740441)
    ·
      refine ⟨2067149526524025194805331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2756199368698700259740441 2067149526524025194805331)
      ·
        refine ⟨3100724289786037792207997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067149526524025194805331 3100724289786037792207997)
        ·
          refine ⟨1162771608669764172077999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3100724289786037792207997 1162771608669764172077999)
          ·
            refine ⟨1744157413004646258116999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162771608669764172077999 1744157413004646258116999)
            ·
              refine ⟨2616236119506969387175499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744157413004646258116999 2616236119506969387175499)
              ·
                refine ⟨3924354179260454080763249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616236119506969387175499 3924354179260454080763249)
                ·
                  refine ⟨2943265634445340560572437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924354179260454080763249 2943265634445340560572437)
                  ·
                    refine ⟨137965576614625338776833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2943265634445340560572437 137965576614625338776833)
                    ·
                      rfl

theorem cell23_806061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_806061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806061 prefixEnd_806061 := by exact prefixLift 806061
  have htrace : WordTrace (prefixWord ++ tailWord_806061) baseStart_806061 baseEnd_806061 := by
    simpa [prefixWord, tailWord_806061, baseEnd_806061] using wordTrace_append hprefix tailTrace_806061
  have hstable : (prefixWord ++ tailWord_806061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806061).length < 2 ^ (prefixWord ++ tailWord_806061).sum := by decide
  have hdescent : baseEnd_806061 < baseStart_806061 := by decide
  rcases family_descends (prefixWord ++ tailWord_806061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806101 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_806101 : Nat := 118140960795 + 806101 * 2 ^ 59
def prefixEnd_806101 : Nat := 4983230072969 + 3 ^ 40 * 806101 * 2
def baseEnd_806101 : Nat := 413917269070055859830315

theorem tailTrace_806101 : CollatzResearch.WordTrace tailWord_806101 prefixEnd_806101 413917269070055859830315 := by
  unfold tailWord_806101
  simp only [CollatzResearch.WordTrace]
  refine ⟨29400918852641222935354157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19600612568427481956902771 29400918852641222935354157)
  ·
    refine ⟨11025344569740458600757809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29400918852641222935354157 11025344569740458600757809)
    ·
      refine ⟨8269008427305343950568357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11025344569740458600757809 8269008427305343950568357)
      ·
        refine ⟨1550439080119751990731567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8269008427305343950568357 1550439080119751990731567)
        ·
          refine ⟨2325658620179627986097351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550439080119751990731567 2325658620179627986097351)
          ·
            refine ⟨3488487930269441979146027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325658620179627986097351 3488487930269441979146027)
            ·
              refine ⟨5232731895404162968719041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488487930269441979146027 5232731895404162968719041)
              ·
                refine ⟨3924548921553122226539281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232731895404162968719041 3924548921553122226539281)
                ·
                  refine ⟨2943411691164841669904461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924548921553122226539281 2943411691164841669904461)
                  ·
                    refine ⟨1103779384186815626214173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943411691164841669904461 1103779384186815626214173)
                    ·
                      refine ⟨413917269070055859830315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1103779384186815626214173 413917269070055859830315)
                      ·
                        rfl

theorem cell23_806101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_806101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806101 prefixEnd_806101 := by exact prefixLift 806101
  have htrace : WordTrace (prefixWord ++ tailWord_806101) baseStart_806101 baseEnd_806101 := by
    simpa [prefixWord, tailWord_806101, baseEnd_806101] using wordTrace_append hprefix tailTrace_806101
  have hstable : (prefixWord ++ tailWord_806101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806101).length < 2 ^ (prefixWord ++ tailWord_806101).sum := by decide
  have hdescent : baseEnd_806101 < baseStart_806101 := by decide
  rcases family_descends (prefixWord ++ tailWord_806101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806102 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_806102 : Nat := 118140960795 + 806102 * 2 ^ 59
def prefixEnd_806102 : Nat := 4983230072969 + 3 ^ 40 * 806102 * 2
def baseEnd_806102 : Nat := 413917782550710355917811

theorem tailTrace_806102 : CollatzResearch.WordTrace tailWord_806102 prefixEnd_806102 413917782550710355917811 := by
  unfold tailWord_806102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837559707852350006633785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19600636883758400070760373 1837559707852350006633785)
  ·
    refine ⟨1378169780889262504975339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1837559707852350006633785 1378169780889262504975339)
    ·
      refine ⟨2067254671333893757463009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378169780889262504975339 2067254671333893757463009)
      ·
        refine ⟨1550441003500420318097257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067254671333893757463009 1550441003500420318097257)
        ·
          refine ⟨1162830752625315238572943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550441003500420318097257 1162830752625315238572943)
          ·
            refine ⟨1744246128937972857859415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162830752625315238572943 1744246128937972857859415)
            ·
              refine ⟨2616369193406959286789123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744246128937972857859415 2616369193406959286789123)
              ·
                refine ⟨3924553790110438930183685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616369193406959286789123 3924553790110438930183685)
                ·
                  refine ⟨735853835645707299409441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3924553790110438930183685 735853835645707299409441)
                  ·
                    refine ⟨551890376734280474557081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735853835645707299409441 551890376734280474557081)
                    ·
                      refine ⟨413917782550710355917811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551890376734280474557081 413917782550710355917811)
                      ·
                        rfl

theorem cell23_806102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_806102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806102 prefixEnd_806102 := by exact prefixLift 806102
  have htrace : WordTrace (prefixWord ++ tailWord_806102) baseStart_806102 baseEnd_806102 := by
    simpa [prefixWord, tailWord_806102, baseEnd_806102] using wordTrace_append hprefix tailTrace_806102
  have hstable : (prefixWord ++ tailWord_806102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806102).length < 2 ^ (prefixWord ++ tailWord_806102).sum := by decide
  have hdescent : baseEnd_806102 < baseStart_806102 := by decide
  rcases family_descends (prefixWord ++ tailWord_806102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806124 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_806124 : Nat := 118140960795 + 806124 * 2 ^ 59
def prefixEnd_806124 : Nat := 4983230072969 + 3 ^ 40 * 806124 * 2
def baseEnd_806124 : Nat := 413929079125109269842709

theorem tailTrace_806124 : CollatzResearch.WordTrace tailWord_806124 prefixEnd_806124 413929079125109269842709 := by
  unfold tailWord_806124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700878865778948931720713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19601171821038598575627617 14700878865778948931720713)
  ·
    refine ⟨11025659149334211698790535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14700878865778948931720713 11025659149334211698790535)
    ·
      refine ⟨16538488724001317548185803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11025659149334211698790535 16538488724001317548185803)
      ·
        refine ⟨24807733086001976322278705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16538488724001317548185803 24807733086001976322278705)
        ·
          refine ⟨18605799814501482241709029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24807733086001976322278705 18605799814501482241709029)
          ·
            refine ⟨3488587465219027920320443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18605799814501482241709029 3488587465219027920320443)
            ·
              refine ⟨5232881197828541880480665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488587465219027920320443 5232881197828541880480665)
              ·
                refine ⟨3924660898371406410360499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232881197828541880480665 3924660898371406410360499)
                ·
                  refine ⟨5886991347557109615540749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924660898371406410360499 5886991347557109615540749)
                  ·
                    refine ⟨2207621755333916105827781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5886991347557109615540749 2207621755333916105827781)
                    ·
                      refine ⟨413929079125109269842709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2207621755333916105827781 413929079125109269842709)
                      ·
                        rfl

theorem cell23_806124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_806124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806124 prefixEnd_806124 := by exact prefixLift 806124
  have htrace : WordTrace (prefixWord ++ tailWord_806124) baseStart_806124 baseEnd_806124 := by
    simpa [prefixWord, tailWord_806124, baseEnd_806124] using wordTrace_append hprefix tailTrace_806124
  have hstable : (prefixWord ++ tailWord_806124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806124).length < 2 ^ (prefixWord ++ tailWord_806124).sum := by decide
  have hdescent : baseEnd_806124 < baseStart_806124 := by decide
  rcases family_descends (prefixWord ++ tailWord_806124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806134 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_806134 : Nat := 118140960795 + 806134 * 2 ^ 59
def prefixEnd_806134 : Nat := 4983230072969 + 3 ^ 40 * 806134 * 2
def baseEnd_806134 : Nat := 137978071310551410239221

theorem tailTrace_806134 : CollatzResearch.WordTrace tailWord_806134 prefixEnd_806134 137978071310551410239221 := by
  unfold tailWord_806134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837632653845104348206591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19601414974347779714203637 1837632653845104348206591)
  ·
    refine ⟨2756448980767656522309887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1837632653845104348206591 2756448980767656522309887)
    ·
      refine ⟨4134673471151484783464831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2756448980767656522309887 4134673471151484783464831)
      ·
        refine ⟨6202010206727227175197247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4134673471151484783464831 6202010206727227175197247)
        ·
          refine ⟨9303015310090840762795871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202010206727227175197247 9303015310090840762795871)
          ·
            refine ⟨13954522965136261144193807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303015310090840762795871 13954522965136261144193807)
            ·
              refine ⟨20931784447704391716290711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954522965136261144193807 20931784447704391716290711)
              ·
                refine ⟨31397676671556587574436067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20931784447704391716290711 31397676671556587574436067)
                ·
                  refine ⟨47096515007334881361654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31397676671556587574436067 47096515007334881361654101)
                  ·
                    refine ⟨137978071310551410239221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 47096515007334881361654101 137978071310551410239221)
                    ·
                      rfl

theorem cell23_806134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_806134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806134 prefixEnd_806134 := by exact prefixLift 806134
  have htrace : WordTrace (prefixWord ++ tailWord_806134) baseStart_806134 baseEnd_806134 := by
    simpa [prefixWord, tailWord_806134, baseEnd_806134] using wordTrace_append hprefix tailTrace_806134
  have hstable : (prefixWord ++ tailWord_806134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806134).length < 2 ^ (prefixWord ++ tailWord_806134).sum := by decide
  have hdescent : baseEnd_806134 < baseStart_806134 := by decide
  rcases family_descends (prefixWord ++ tailWord_806134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806161 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_806161 : Nat := 118140960795 + 806161 * 2 ^ 59
def prefixEnd_806161 : Nat := 4983230072969 + 3 ^ 40 * 806161 * 2
def baseEnd_806161 : Nat := 413948077909325625080039

theorem tailTrace_806161 : CollatzResearch.WordTrace tailWord_806161 prefixEnd_806161 413948077909325625080039 := by
  unfold tailWord_806161
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403107232423853182538337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19602071488282568788358891 29403107232423853182538337)
  ·
    refine ⟨22052330424317889886903753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29403107232423853182538337 22052330424317889886903753)
    ·
      refine ⟨16539247818238417415177815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22052330424317889886903753 16539247818238417415177815)
      ·
        refine ⟨24808871727357626122766723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16539247818238417415177815 24808871727357626122766723)
        ·
          refine ⟨37213307591036439184150085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24808871727357626122766723 37213307591036439184150085)
          ·
            refine ⟨6977495173319332347028141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37213307591036439184150085 6977495173319332347028141)
            ·
              refine ⟨2616560689994749630135553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6977495173319332347028141 2616560689994749630135553)
              ·
                refine ⟨1962420517496062222601665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616560689994749630135553 1962420517496062222601665)
                ·
                  refine ⟨1471815388122046666951249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962420517496062222601665 1471815388122046666951249)
                  ·
                    refine ⟨1103861541091535000213437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1471815388122046666951249 1103861541091535000213437)
                    ·
                      refine ⟨413948077909325625080039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1103861541091535000213437 413948077909325625080039)
                      ·
                        rfl

theorem cell23_806161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_806161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806161 prefixEnd_806161 := by exact prefixLift 806161
  have htrace : WordTrace (prefixWord ++ tailWord_806161) baseStart_806161 baseEnd_806161 := by
    simpa [prefixWord, tailWord_806161, baseEnd_806161] using wordTrace_append hprefix tailTrace_806161
  have hstable : (prefixWord ++ tailWord_806161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806161).length < 2 ^ (prefixWord ++ tailWord_806161).sum := by decide
  have hdescent : baseEnd_806161 < baseStart_806161 := by decide
  rcases family_descends (prefixWord ++ tailWord_806161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806168 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_806168 : Nat := 118140960795 + 806168 * 2 ^ 59
def prefixEnd_806168 : Nat := 4983230072969 + 3 ^ 40 * 806168 * 2
def baseEnd_806168 : Nat := 137983890757969032564169

theorem tailTrace_806168 : CollatzResearch.WordTrace tailWord_806168 prefixEnd_806168 137983890757969032564169 := by
  unfold tailWord_806168
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701681271699246689021579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19602241695598995585362105 14701681271699246689021579)
  ·
    refine ⟨22052521907548870033532369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14701681271699246689021579 22052521907548870033532369)
    ·
      refine ⟨16539391430661652525149277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22052521907548870033532369 16539391430661652525149277)
      ·
        refine ⟨6202271786498119696930979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16539391430661652525149277 6202271786498119696930979)
        ·
          refine ⟨9303407679747179545396469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202271786498119696930979 9303407679747179545396469)
          ·
            refine ⟨872194469976298082380919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9303407679747179545396469 872194469976298082380919)
            ·
              refine ⟨1308291704964447123571379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872194469976298082380919 1308291704964447123571379)
              ·
                refine ⟨1962437557446670685357069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308291704964447123571379 1962437557446670685357069)
                ·
                  refine ⟨735914084042501507008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1962437557446670685357069 735914084042501507008901)
                  ·
                    refine ⟨137983890757969032564169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735914084042501507008901 137983890757969032564169)
                    ·
                      rfl

theorem cell23_806168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_806168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806168 prefixEnd_806168 := by exact prefixLift 806168
  have htrace : WordTrace (prefixWord ++ tailWord_806168) baseStart_806168 baseEnd_806168 := by
    simpa [prefixWord, tailWord_806168, baseEnd_806168] using wordTrace_append hprefix tailTrace_806168
  have hstable : (prefixWord ++ tailWord_806168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806168).length < 2 ^ (prefixWord ++ tailWord_806168).sum := by decide
  have hdescent : baseEnd_806168 < baseStart_806168 := by decide
  rcases family_descends (prefixWord ++ tailWord_806168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806181 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 6]
def baseStart_806181 : Nat := 118140960795 + 806181 * 2 ^ 59
def prefixEnd_806181 : Nat := 4983230072969 + 3 ^ 40 * 806181 * 2
def baseEnd_806181 : Nat := 45995371946935060758883

theorem tailTrace_806181 : CollatzResearch.WordTrace tailWord_806181 prefixEnd_806181 45995371946935060758883 := by
  unfold tailWord_806181
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403836692351396598266397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19602557794900931065510931 29403836692351396598266397)
  ·
    refine ⟨11026438759631773724349899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29403836692351396598266397 11026438759631773724349899)
    ·
      refine ⟨16539658139447660586524849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026438759631773724349899 16539658139447660586524849)
      ·
        refine ⟨12404743604585745439893637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16539658139447660586524849 12404743604585745439893637)
        ·
          refine ⟨2325889425859827269980057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12404743604585745439893637 2325889425859827269980057)
          ·
            refine ⟨1744417069394870452485043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325889425859827269980057 1744417069394870452485043)
            ·
              refine ⟨2616625604092305678727565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744417069394870452485043 2616625604092305678727565)
              ·
                refine ⟨981234601534614629522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2616625604092305678727565 981234601534614629522837)
                ·
                  refine ⟨45995371946935060758883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 981234601534614629522837 45995371946935060758883)
                  ·
                    rfl

theorem cell23_806181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_806181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806181 prefixEnd_806181 := by exact prefixLift 806181
  have htrace : WordTrace (prefixWord ++ tailWord_806181) baseStart_806181 baseEnd_806181 := by
    simpa [prefixWord, tailWord_806181, baseEnd_806181] using wordTrace_append hprefix tailTrace_806181
  have hstable : (prefixWord ++ tailWord_806181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806181).length < 2 ^ (prefixWord ++ tailWord_806181).sum := by decide
  have hdescent : baseEnd_806181 < baseStart_806181 := by decide
  rcases family_descends (prefixWord ++ tailWord_806181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806191 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 3]
def baseStart_806191 : Nat := 118140960795 + 806191 * 2 ^ 59
def prefixEnd_806191 : Nat := 4983230072969 + 3 ^ 40 * 806191 * 2
def baseEnd_806191 : Nat := 413963482328960507704901

theorem tailTrace_806191 : CollatzResearch.WordTrace tailWord_806191 prefixEnd_806191 413963482328960507704901 := by
  unfold tailWord_806191
  simp only [CollatzResearch.WordTrace]
  refine ⟨29404201422315168306130427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19602800948210112204086951 29404201422315168306130427)
  ·
    refine ⟨44106302133472752459195641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29404201422315168306130427 44106302133472752459195641)
    ·
      refine ⟨33079726600104564344396731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44106302133472752459195641 33079726600104564344396731)
      ·
        refine ⟨49619589900156846516595097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33079726600104564344396731 49619589900156846516595097)
        ·
          refine ⟨37214692425117634887446323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49619589900156846516595097 37214692425117634887446323)
          ·
            refine ⟨55822038637676452331169485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37214692425117634887446323 55822038637676452331169485)
            ·
              refine ⟨20933264489128669624188557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55822038637676452331169485 20933264489128669624188557)
              ·
                refine ⟨7849974183423251109070709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20933264489128669624188557 7849974183423251109070709)
                ·
                  refine ⟨735935079695929791475379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7849974183423251109070709 735935079695929791475379)
                  ·
                    refine ⟨1103902619543894687213069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 735935079695929791475379 1103902619543894687213069)
                    ·
                      refine ⟨413963482328960507704901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1103902619543894687213069 413963482328960507704901)
                      ·
                        rfl

theorem cell23_806191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_806191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806191 prefixEnd_806191 := by exact prefixLift 806191
  have htrace : WordTrace (prefixWord ++ tailWord_806191) baseStart_806191 baseEnd_806191 := by
    simpa [prefixWord, tailWord_806191, baseEnd_806191] using wordTrace_append hprefix tailTrace_806191
  have hstable : (prefixWord ++ tailWord_806191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806191).length < 2 ^ (prefixWord ++ tailWord_806191).sum := by decide
  have hdescent : baseEnd_806191 < baseStart_806191 := by decide
  rcases family_descends (prefixWord ++ tailWord_806191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806224 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_806224 : Nat := 118140960795 + 806224 * 2 ^ 59
def prefixEnd_806224 : Nat := 4983230072969 + 3 ^ 40 * 806224 * 2
def baseEnd_806224 : Nat := 137993475730186292864083

theorem tailTrace_806224 : CollatzResearch.WordTrace tailWord_806224 prefixEnd_806224 137993475730186292864083 := by
  unfold tailWord_806224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702702515597807471040863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19603603354130409961387817 14702702515597807471040863)
  ·
    refine ⟨22054053773396711206561295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14702702515597807471040863 22054053773396711206561295)
    ·
      refine ⟨33081080660095066809841943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22054053773396711206561295 33081080660095066809841943)
      ·
        refine ⟨49621620990142600214762915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33081080660095066809841943 49621620990142600214762915)
        ·
          refine ⟨74432431485213900322144373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49621620990142600214762915 74432431485213900322144373)
          ·
            refine ⟨6978040451738803155201035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74432431485213900322144373 6978040451738803155201035)
            ·
              refine ⟨10467060677608204732801553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978040451738803155201035 10467060677608204732801553)
              ·
                refine ⟨7850295508206153549601165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467060677608204732801553 7850295508206153549601165)
                ·
                  refine ⟨2943860815577307581100437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7850295508206153549601165 2943860815577307581100437)
                  ·
                    refine ⟨137993475730186292864083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2943860815577307581100437 137993475730186292864083)
                    ·
                      rfl

theorem cell23_806224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_806224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806224 prefixEnd_806224 := by exact prefixLift 806224
  have htrace : WordTrace (prefixWord ++ tailWord_806224) baseStart_806224 baseEnd_806224 := by
    simpa [prefixWord, tailWord_806224, baseEnd_806224] using wordTrace_append hprefix tailTrace_806224
  have hstable : (prefixWord ++ tailWord_806224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806224).length < 2 ^ (prefixWord ++ tailWord_806224).sum := by decide
  have hdescent : baseEnd_806224 < baseStart_806224 := by decide
  rcases family_descends (prefixWord ++ tailWord_806224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806225 : List Nat := [1, 2, 2, 1, 4, 1, 3, 4, 1, 1, 3]
def baseStart_806225 : Nat := 118140960795 + 806225 * 2 ^ 59
def prefixEnd_806225 : Nat := 4983230072969 + 3 ^ 40 * 806225 * 2
def baseEnd_806225 : Nat := 413980940671213374679745

theorem tailTrace_806225 : CollatzResearch.WordTrace tailWord_806225 prefixEnd_806225 413980940671213374679745 := by
  unfold tailWord_806225
  simp only [CollatzResearch.WordTrace]
  refine ⟨29405441504191992112868129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19603627669461328075245419 29405441504191992112868129)
  ·
    refine ⟨22054081128143994084651097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29405441504191992112868129 22054081128143994084651097)
    ·
      refine ⟨16540560846107995563488323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22054081128143994084651097 16540560846107995563488323)
      ·
        refine ⟨24810841269161993345232485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16540560846107995563488323 24810841269161993345232485)
        ·
          refine ⟨4652032737967873752231091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24810841269161993345232485 4652032737967873752231091)
          ·
            refine ⟨6978049106951810628346637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652032737967873752231091 6978049106951810628346637)
            ·
              refine ⟨2616768415106928985629989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6978049106951810628346637 2616768415106928985629989)
              ·
                refine ⟨490644077832549184805623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2616768415106928985629989 490644077832549184805623)
                ·
                  refine ⟨735966116748823777208435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490644077832549184805623 735966116748823777208435)
                  ·
                    refine ⟨1103949175123235665812653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 735966116748823777208435 1103949175123235665812653)
                    ·
                      refine ⟨413980940671213374679745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1103949175123235665812653 413980940671213374679745)
                      ·
                        rfl

theorem cell23_806225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_806225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806225 prefixEnd_806225 := by exact prefixLift 806225
  have htrace : WordTrace (prefixWord ++ tailWord_806225) baseStart_806225 baseEnd_806225 := by
    simpa [prefixWord, tailWord_806225, baseEnd_806225] using wordTrace_append hprefix tailTrace_806225
  have hstable : (prefixWord ++ tailWord_806225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806225).length < 2 ^ (prefixWord ++ tailWord_806225).sum := by decide
  have hdescent : baseEnd_806225 < baseStart_806225 := by decide
  rcases family_descends (prefixWord ++ tailWord_806225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806231 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_806231 : Nat := 118140960795 + 806231 * 2 ^ 59
def prefixEnd_806231 : Nat := 4983230072969 + 3 ^ 40 * 806231 * 2
def baseEnd_806231 : Nat := 413984021555140351204717

theorem tailTrace_806231 : CollatzResearch.WordTrace tailWord_806231 prefixEnd_806231 413984021555140351204717 := by
  unfold tailWord_806231
  simp only [CollatzResearch.WordTrace]
  refine ⟨29405660342170255137586547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19603773561446836758391031 29405660342170255137586547)
  ·
    refine ⟨44108490513255382706379821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29405660342170255137586547 44108490513255382706379821)
    ·
      refine ⟨16540683942470768514892433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44108490513255382706379821 16540683942470768514892433)
      ·
        refine ⟨12405512956853076386169325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16540683942470768514892433 12405512956853076386169325)
        ·
          refine ⟨4652067358819903644813497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12405512956853076386169325 4652067358819903644813497)
          ·
            refine ⟨3489050519114927733610123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652067358819903644813497 3489050519114927733610123)
            ·
              refine ⟨5233575778672391600415185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489050519114927733610123 5233575778672391600415185)
              ·
                refine ⟨3925181834004293700311389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233575778672391600415185 3925181834004293700311389)
                ·
                  refine ⟨1471943187751610137616771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3925181834004293700311389 1471943187751610137616771)
                  ·
                    refine ⟨2207914781627415206425157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1471943187751610137616771 2207914781627415206425157)
                    ·
                      refine ⟨413984021555140351204717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2207914781627415206425157 413984021555140351204717)
                      ·
                        rfl

theorem cell23_806231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_806231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806231 prefixEnd_806231 := by exact prefixLift 806231
  have htrace : WordTrace (prefixWord ++ tailWord_806231) baseStart_806231 baseEnd_806231 := by
    simpa [prefixWord, tailWord_806231, baseEnd_806231] using wordTrace_append hprefix tailTrace_806231
  have hstable : (prefixWord ++ tailWord_806231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806231).length < 2 ^ (prefixWord ++ tailWord_806231).sum := by decide
  have hdescent : baseEnd_806231 < baseStart_806231 := by decide
  rcases family_descends (prefixWord ++ tailWord_806231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806268 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_806268 : Nat := 118140960795 + 806268 * 2 ^ 59
def prefixEnd_806268 : Nat := 4983230072969 + 3 ^ 40 * 806268 * 2
def baseEnd_806268 : Nat := 414003020339356706442047

theorem tailTrace_806268 : CollatzResearch.WordTrace tailWord_806268 prefixEnd_806268 414003020339356706442047 := by
  unfold tailWord_806268
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703504921518105228341729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19604673228690806971122305 14703504921518105228341729)
  ·
    refine ⟨11027628691138578921256297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14703504921518105228341729 11027628691138578921256297)
    ·
      refine ⟨8270721518353934190942223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11027628691138578921256297 8270721518353934190942223)
      ·
        refine ⟨12406082277530901286413335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8270721518353934190942223 12406082277530901286413335)
        ·
          refine ⟨18609123416296351929620003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406082277530901286413335 18609123416296351929620003)
          ·
            refine ⟨27913685124444527894430005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18609123416296351929620003 27913685124444527894430005)
            ·
              refine ⟨2616907980416674490102813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27913685124444527894430005 2616907980416674490102813)
              ·
                refine ⟨981340492656252933788555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2616907980416674490102813 981340492656252933788555)
                ·
                  refine ⟨1472010738984379400682833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981340492656252933788555 1472010738984379400682833)
                  ·
                    refine ⟨1104008054238284550512125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472010738984379400682833 1104008054238284550512125)
                    ·
                      refine ⟨414003020339356706442047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104008054238284550512125 414003020339356706442047)
                      ·
                        rfl

theorem cell23_806268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_806268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806268 prefixEnd_806268 := by exact prefixLift 806268
  have htrace : WordTrace (prefixWord ++ tailWord_806268) baseStart_806268 baseEnd_806268 := by
    simpa [prefixWord, tailWord_806268, baseEnd_806268] using wordTrace_append hprefix tailTrace_806268
  have hstable : (prefixWord ++ tailWord_806268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806268).length < 2 ^ (prefixWord ++ tailWord_806268).sum := by decide
  have hdescent : baseEnd_806268 < baseStart_806268 := by decide
  rcases family_descends (prefixWord ++ tailWord_806268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806275 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 2, 4]
def baseStart_806275 : Nat := 118140960795 + 806275 * 2 ^ 59
def prefixEnd_806275 : Nat := 4983230072969 + 3 ^ 40 * 806275 * 2
def baseEnd_806275 : Nat := 138002204901312726351505

theorem tailTrace_806275 : CollatzResearch.WordTrace tailWord_806275 prefixEnd_806275 138002204901312726351505 := by
  unfold tailWord_806275
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407265154010850652188279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19604843436007233768125519 29407265154010850652188279)
  ·
    refine ⟨44110897731016275978282419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407265154010850652188279 44110897731016275978282419)
    ·
      refine ⟨66166346596524413967423629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44110897731016275978282419 66166346596524413967423629)
      ·
        refine ⟨24812379973696655237783861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66166346596524413967423629 24812379973696655237783861)
        ·
          refine ⟨2326160622534061428542237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24812379973696655237783861 2326160622534061428542237)
          ·
            refine ⟨872310233450273035703339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2326160622534061428542237 872310233450273035703339)
            ·
              refine ⟨1308465350175409553555009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872310233450273035703339 1308465350175409553555009)
              ·
                refine ⟨981349012631557165166257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308465350175409553555009 981349012631557165166257)
                ·
                  refine ⟨736011759473667873874693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981349012631557165166257 736011759473667873874693)
                  ·
                    refine ⟨138002204901312726351505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736011759473667873874693 138002204901312726351505)
                    ·
                      rfl

theorem cell23_806275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 4].length) (baseStart_806275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806275 prefixEnd_806275 := by exact prefixLift 806275
  have htrace : WordTrace (prefixWord ++ tailWord_806275) baseStart_806275 baseEnd_806275 := by
    simpa [prefixWord, tailWord_806275, baseEnd_806275] using wordTrace_append hprefix tailTrace_806275
  have hstable : (prefixWord ++ tailWord_806275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806275).length < 2 ^ (prefixWord ++ tailWord_806275).sum := by decide
  have hdescent : baseEnd_806275 < baseStart_806275 := by decide
  rcases family_descends (prefixWord ++ tailWord_806275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806292 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_806292 : Nat := 118140960795 + 806292 * 2 ^ 59
def prefixEnd_806292 : Nat := 4983230072969 + 3 ^ 40 * 806292 * 2
def baseEnd_806292 : Nat := 138005114625021537513979

theorem tailTrace_806292 : CollatzResearch.WordTrace tailWord_806292 prefixEnd_806292 138005114625021537513979 := by
  unfold tailWord_806292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703942597474631277778565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19605256796632841703704753 14703942597474631277778565)
  ·
    refine ⟨2756989237026493364583481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14703942597474631277778565 2756989237026493364583481)
    ·
      refine ⟨2067741927769870023437611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2756989237026493364583481 2067741927769870023437611)
      ·
        refine ⟨3101612891654805035156417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067741927769870023437611 3101612891654805035156417)
        ·
          refine ⟨2326209668741103776367313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3101612891654805035156417 2326209668741103776367313)
          ·
            refine ⟨1744657251555827832275485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326209668741103776367313 1744657251555827832275485)
            ·
              refine ⟨654246469333435437103307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1744657251555827832275485 654246469333435437103307)
              ·
                refine ⟨981369704000153155654961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654246469333435437103307 981369704000153155654961)
                ·
                  refine ⟨736027278000114866741221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981369704000153155654961 736027278000114866741221)
                  ·
                    refine ⟨138005114625021537513979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736027278000114866741221 138005114625021537513979)
                    ·
                      rfl

theorem cell23_806292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_806292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806292 prefixEnd_806292 := by exact prefixLift 806292
  have htrace : WordTrace (prefixWord ++ tailWord_806292) baseStart_806292 baseEnd_806292 := by
    simpa [prefixWord, tailWord_806292, baseEnd_806292] using wordTrace_append hprefix tailTrace_806292
  have hstable : (prefixWord ++ tailWord_806292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806292).length < 2 ^ (prefixWord ++ tailWord_806292).sum := by decide
  have hdescent : baseEnd_806292 < baseStart_806292 := by decide
  rcases family_descends (prefixWord ++ tailWord_806292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806311 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_806311 : Nat := 118140960795 + 806311 * 2 ^ 59
def prefixEnd_806311 : Nat := 4983230072969 + 3 ^ 40 * 806311 * 2
def baseEnd_806311 : Nat := 414025100007500038204349

theorem tailTrace_806311 : CollatzResearch.WordTrace tailWord_806311 prefixEnd_806311 414025100007500038204349 := by
  unfold tailWord_806311
  simp only [CollatzResearch.WordTrace]
  refine ⟨29408578181880428800498787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19605718787920285866999191 29408578181880428800498787)
  ·
    refine ⟨44112867272820643200748181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29408578181880428800498787 44112867272820643200748181)
    ·
      refine ⟨2067790653413467650035071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44112867272820643200748181 2067790653413467650035071)
      ·
        refine ⟨3101685980120201475052607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067790653413467650035071 3101685980120201475052607)
        ·
          refine ⟨4652528970180302212578911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101685980120201475052607 4652528970180302212578911)
          ·
            refine ⟨6978793455270453318868367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652528970180302212578911 6978793455270453318868367)
            ·
              refine ⟨10468190182905679978302551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978793455270453318868367 10468190182905679978302551)
              ·
                refine ⟨15702285274358519967453827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10468190182905679978302551 15702285274358519967453827)
                ·
                  refine ⟨23553427911537779951180741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15702285274358519967453827 23553427911537779951180741)
                  ·
                    refine ⟨4416267733413333740846389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23553427911537779951180741 4416267733413333740846389)
                    ·
                      refine ⟨414025100007500038204349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4416267733413333740846389 414025100007500038204349)
                      ·
                        rfl

theorem cell23_806311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_806311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806311 prefixEnd_806311 := by exact prefixLift 806311
  have htrace : WordTrace (prefixWord ++ tailWord_806311) baseStart_806311 baseEnd_806311 := by
    simpa [prefixWord, tailWord_806311, baseEnd_806311] using wordTrace_append hprefix tailTrace_806311
  have hstable : (prefixWord ++ tailWord_806311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806311).length < 2 ^ (prefixWord ++ tailWord_806311).sum := by decide
  have hdescent : baseEnd_806311 < baseStart_806311 := by decide
  rcases family_descends (prefixWord ++ tailWord_806311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806351 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_806351 : Nat := 118140960795 + 806351 * 2 ^ 59
def prefixEnd_806351 : Nat := 4983230072969 + 3 ^ 40 * 806351 * 2
def baseEnd_806351 : Nat := 414045639233679881704165

theorem tailTrace_806351 : CollatzResearch.WordTrace tailWord_806351 prefixEnd_806351 414045639233679881704165 := by
  unfold tailWord_806351
  simp only [CollatzResearch.WordTrace]
  refine ⟨29410037101735515631954907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19606691401157010421303271 29410037101735515631954907)
  ·
    refine ⟨44115055652603273447932361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29410037101735515631954907 44115055652603273447932361)
    ·
      refine ⟨33086291739452455085949271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44115055652603273447932361 33086291739452455085949271)
      ·
        refine ⟨49629437609178682628923907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33086291739452455085949271 49629437609178682628923907)
        ·
          refine ⟨74444156413768023943385861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49629437609178682628923907 74444156413768023943385861)
          ·
            refine ⟨13958279327581504489384849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74444156413768023943385861 13958279327581504489384849)
            ·
              refine ⟨10468709495686128367038637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13958279327581504489384849 10468709495686128367038637)
              ·
                refine ⟨3925766060882298137639489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10468709495686128367038637 3925766060882298137639489)
                ·
                  refine ⟨2944324545661723603229617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3925766060882298137639489 2944324545661723603229617)
                  ·
                    refine ⟨2208243409246292702422213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944324545661723603229617 2208243409246292702422213)
                    ·
                      refine ⟨414045639233679881704165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2208243409246292702422213 414045639233679881704165)
                      ·
                        rfl

theorem cell23_806351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_806351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806351 prefixEnd_806351 := by exact prefixLift 806351
  have htrace : WordTrace (prefixWord ++ tailWord_806351) baseStart_806351 baseEnd_806351 := by
    simpa [prefixWord, tailWord_806351, baseEnd_806351] using wordTrace_append hprefix tailTrace_806351
  have hstable : (prefixWord ++ tailWord_806351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806351).length < 2 ^ (prefixWord ++ tailWord_806351).sum := by decide
  have hdescent : baseEnd_806351 < baseStart_806351 := by decide
  rcases family_descends (prefixWord ++ tailWord_806351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806389 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_806389 : Nat := 118140960795 + 806389 * 2 ^ 59
def prefixEnd_806389 : Nat := 4983230072969 + 3 ^ 40 * 806389 * 2
def baseEnd_806389 : Nat := 414065151498550733028991

theorem tailTrace_806389 : CollatzResearch.WordTrace tailWord_806389 prefixEnd_806389 414065151498550733028991 := by
  unfold tailWord_806389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29411423075597848121838221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19607615383731898747892147 29411423075597848121838221)
  ·
    refine ⟨11029283653349193045689333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29411423075597848121838221 11029283653349193045689333)
    ·
      refine ⟨1033995342501486848033375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11029283653349193045689333 1033995342501486848033375)
      ·
        refine ⟨1550993013752230272050063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033995342501486848033375 1550993013752230272050063)
        ·
          refine ⟨2326489520628345408075095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550993013752230272050063 2326489520628345408075095)
          ·
            refine ⟨3489734280942518112112643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326489520628345408075095 3489734280942518112112643)
            ·
              refine ⟨5234601421413777168168965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489734280942518112112643 5234601421413777168168965)
              ·
                refine ⟨981487766515083219031681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5234601421413777168168965 981487766515083219031681)
                ·
                  refine ⟨736115824886312414273761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981487766515083219031681 736115824886312414273761)
                  ·
                    refine ⟨552086868664734310705321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736115824886312414273761 552086868664734310705321)
                    ·
                      refine ⟨414065151498550733028991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552086868664734310705321 414065151498550733028991)
                      ·
                        rfl

theorem cell23_806389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_806389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806389 prefixEnd_806389 := by exact prefixLift 806389
  have htrace : WordTrace (prefixWord ++ tailWord_806389) baseStart_806389 baseEnd_806389 := by
    simpa [prefixWord, tailWord_806389, baseEnd_806389] using wordTrace_append hprefix tailTrace_806389
  have hstable : (prefixWord ++ tailWord_806389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806389).length < 2 ^ (prefixWord ++ tailWord_806389).sum := by decide
  have hdescent : baseEnd_806389 < baseStart_806389 := by decide
  rcases family_descends (prefixWord ++ tailWord_806389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806391 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 4, 5]
def baseStart_806391 : Nat := 118140960795 + 806391 * 2 ^ 59
def prefixEnd_806391 : Nat := 4983230072969 + 3 ^ 40 * 806391 * 2
def baseEnd_806391 : Nat := 138022059486619908401327

theorem tailTrace_806391 : CollatzResearch.WordTrace tailWord_806391 prefixEnd_806391 138022059486619908401327 := by
  unfold tailWord_806391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29411496021590602463411027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19607664014393734975607351 29411496021590602463411027)
  ·
    refine ⟨44117244032385903695116541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29411496021590602463411027 44117244032385903695116541)
    ·
      refine ⟨16543966512144713885668703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44117244032385903695116541 16543966512144713885668703)
      ·
        refine ⟨24815949768217070828503055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16543966512144713885668703 24815949768217070828503055)
        ·
          refine ⟨37223924652325606242754583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24815949768217070828503055 37223924652325606242754583)
          ·
            refine ⟨55835886978488409364131875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37223924652325606242754583 55835886978488409364131875)
            ·
              refine ⟨83753830467732614046197813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55835886978488409364131875 83753830467732614046197813)
              ·
                refine ⟨7851921606349932566831045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83753830467732614046197813 7851921606349932566831045)
                ·
                  refine ⟨1472235301190612356280821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7851921606349932566831045 1472235301190612356280821)
                  ·
                    refine ⟨138022059486619908401327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1472235301190612356280821 138022059486619908401327)
                    ·
                      rfl

theorem cell23_806391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_806391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806391 prefixEnd_806391 := by exact prefixLift 806391
  have htrace : WordTrace (prefixWord ++ tailWord_806391) baseStart_806391 baseEnd_806391 := by
    simpa [prefixWord, tailWord_806391, baseEnd_806391] using wordTrace_append hprefix tailTrace_806391
  have hstable : (prefixWord ++ tailWord_806391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806391).length < 2 ^ (prefixWord ++ tailWord_806391).sum := by decide
  have hdescent : baseEnd_806391 < baseStart_806391 := by decide
  rcases family_descends (prefixWord ++ tailWord_806391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806428 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_806428 : Nat := 118140960795 + 806428 * 2 ^ 59
def prefixEnd_806428 : Nat := 4983230072969 + 3 ^ 40 * 806428 * 2
def baseEnd_806428 : Nat := 414085177244076080441311

theorem tailTrace_806428 : CollatzResearch.WordTrace tailWord_806428 prefixEnd_806428 414085177244076080441311 := by
  unfold tailWord_806428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14706422761228278891253969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19608563681637705188338625 14706422761228278891253969)
  ·
    refine ⟨11029817070921209168440477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14706422761228278891253969 11029817070921209168440477)
    ·
      refine ⟨4136181401595453438165179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11029817070921209168440477 4136181401595453438165179)
      ·
        refine ⟨6204272102393180157247769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136181401595453438165179 6204272102393180157247769)
        ·
          refine ⟨4653204076794885117935827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6204272102393180157247769 4653204076794885117935827)
          ·
            refine ⟨6979806115192327676903741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653204076794885117935827 6979806115192327676903741)
            ·
              refine ⟨2617427293197122878838903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6979806115192327676903741 2617427293197122878838903)
              ·
                refine ⟨3926140939795684318258355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617427293197122878838903 3926140939795684318258355)
                ·
                  refine ⟨5889211409693526477387533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926140939795684318258355 5889211409693526477387533)
                  ·
                    refine ⟨2208454278635072429020325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5889211409693526477387533 2208454278635072429020325)
                    ·
                      refine ⟨414085177244076080441311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2208454278635072429020325 414085177244076080441311)
                      ·
                        rfl

theorem cell23_806428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_806428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806428 prefixEnd_806428 := by exact prefixLift 806428
  have htrace : WordTrace (prefixWord ++ tailWord_806428) baseStart_806428 baseEnd_806428 := by
    simpa [prefixWord, tailWord_806428, baseEnd_806428] using wordTrace_append hprefix tailTrace_806428
  have hstable : (prefixWord ++ tailWord_806428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806428).length < 2 ^ (prefixWord ++ tailWord_806428).sum := by decide
  have hdescent : baseEnd_806428 < baseStart_806428 := by decide
  rcases family_descends (prefixWord ++ tailWord_806428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806448 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_806448 : Nat := 118140960795 + 806448 * 2 ^ 59
def prefixEnd_806448 : Nat := 4983230072969 + 3 ^ 40 * 806448 * 2
def baseEnd_806448 : Nat := 414095446857166002191219

theorem tailTrace_806448 : CollatzResearch.WordTrace tailWord_806448 prefixEnd_806448 414095446857166002191219 := by
  unfold tailWord_806448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14706787491192050599117999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19609049988256067465490665 14706787491192050599117999)
  ·
    refine ⟨22060181236788075898676999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14706787491192050599117999 22060181236788075898676999)
    ·
      refine ⟨33090271855182113848015499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22060181236788075898676999 33090271855182113848015499)
      ·
        refine ⟨49635407782773170772023249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33090271855182113848015499 49635407782773170772023249)
        ·
          refine ⟨37226555837079878079017437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49635407782773170772023249 37226555837079878079017437)
          ·
            refine ⟨13959958438904954279631539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37226555837079878079017437 13959958438904954279631539)
            ·
              refine ⟨20939937658357431419447309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13959958438904954279631539 20939937658357431419447309)
              ·
                refine ⟨7852476621884036782292741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20939937658357431419447309 7852476621884036782292741)
                ·
                  refine ⟨1472339366603256896679889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7852476621884036782292741 1472339366603256896679889)
                  ·
                    refine ⟨1104254524952442672509917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472339366603256896679889 1104254524952442672509917)
                    ·
                      refine ⟨414095446857166002191219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104254524952442672509917 414095446857166002191219)
                      ·
                        rfl

theorem cell23_806448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_806448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806448 prefixEnd_806448 := by exact prefixLift 806448
  have htrace : WordTrace (prefixWord ++ tailWord_806448) baseStart_806448 baseEnd_806448 := by
    simpa [prefixWord, tailWord_806448, baseEnd_806448] using wordTrace_append hprefix tailTrace_806448
  have hstable : (prefixWord ++ tailWord_806448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806448).length < 2 ^ (prefixWord ++ tailWord_806448).sum := by decide
  have hdescent : baseEnd_806448 < baseStart_806448 := by decide
  rcases family_descends (prefixWord ++ tailWord_806448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806455 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 3, 4]
def baseStart_806455 : Nat := 118140960795 + 806455 * 2 ^ 59
def prefixEnd_806455 : Nat := 4983230072969 + 3 ^ 40 * 806455 * 2
def baseEnd_806455 : Nat := 138033013740582491601229

theorem tailTrace_806455 : CollatzResearch.WordTrace tailWord_806455 prefixEnd_806455 138033013740582491601229 := by
  unfold tailWord_806455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29413830293358741393740819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19609220195572494262493879 29413830293358741393740819)
  ·
    refine ⟨44120745440038112090611229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29413830293358741393740819 44120745440038112090611229)
    ·
      refine ⟨16545279540014292033979211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44120745440038112090611229 16545279540014292033979211)
      ·
        refine ⟨24817919310021438050968817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16545279540014292033979211 24817919310021438050968817)
        ·
          refine ⟨18613439482516078538226613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24817919310021438050968817 18613439482516078538226613)
          ·
            refine ⟨1745009951485882362958745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18613439482516078538226613 1745009951485882362958745)
            ·
              refine ⟨1308757463614411772219059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745009951485882362958745 1308757463614411772219059)
              ·
                refine ⟨1963136195421617658328589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308757463614411772219059 1963136195421617658328589)
                ·
                  refine ⟨736176073283106621873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1963136195421617658328589 736176073283106621873221)
                  ·
                    refine ⟨138033013740582491601229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736176073283106621873221 138033013740582491601229)
                    ·
                      rfl

theorem cell23_806455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_806455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806455 prefixEnd_806455 := by exact prefixLift 806455
  have htrace : WordTrace (prefixWord ++ tailWord_806455) baseStart_806455 baseEnd_806455 := by
    simpa [prefixWord, tailWord_806455, baseEnd_806455] using wordTrace_append hprefix tailTrace_806455
  have hstable : (prefixWord ++ tailWord_806455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806455).length < 2 ^ (prefixWord ++ tailWord_806455).sum := by decide
  have hdescent : baseEnd_806455 < baseStart_806455 := by decide
  rcases family_descends (prefixWord ++ tailWord_806455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806478 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_806478 : Nat := 118140960795 + 806478 * 2 ^ 59
def prefixEnd_806478 : Nat := 4983230072969 + 3 ^ 40 * 806478 * 2
def baseEnd_806478 : Nat := 414110851276800884816081

theorem tailTrace_806478 : CollatzResearch.WordTrace tailWord_806478 prefixEnd_806478 414110851276800884816081 := by
  unfold tailWord_806478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676833646534427040228511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19609779448183610881218725 3676833646534427040228511)
  ·
    refine ⟨5515250469801640560342767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3676833646534427040228511 5515250469801640560342767)
    ·
      refine ⟨8272875704702460840514151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515250469801640560342767 8272875704702460840514151)
      ·
        refine ⟨12409313557053691260771227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272875704702460840514151 12409313557053691260771227)
        ·
          refine ⟨18613970335580536891156841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409313557053691260771227 18613970335580536891156841)
          ·
            refine ⟨13960477751685402668367631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18613970335580536891156841 13960477751685402668367631)
            ·
              refine ⟨20940716627528104002551447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13960477751685402668367631 20940716627528104002551447)
              ·
                refine ⟨31411074941292156003827171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20940716627528104002551447 31411074941292156003827171)
                ·
                  refine ⟨47116612411938234005740757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31411074941292156003827171 47116612411938234005740757)
                  ·
                    refine ⟨1104295603404802359509549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47116612411938234005740757 1104295603404802359509549)
                    ·
                      refine ⟨414110851276800884816081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104295603404802359509549 414110851276800884816081)
                      ·
                        rfl

theorem cell23_806478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_806478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806478 prefixEnd_806478 := by exact prefixLift 806478
  have htrace : WordTrace (prefixWord ++ tailWord_806478) baseStart_806478 baseEnd_806478 := by
    simpa [prefixWord, tailWord_806478, baseEnd_806478] using wordTrace_append hprefix tailTrace_806478
  have hstable : (prefixWord ++ tailWord_806478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806478).length < 2 ^ (prefixWord ++ tailWord_806478).sum := by decide
  have hdescent : baseEnd_806478 < baseStart_806478 := by decide
  rcases family_descends (prefixWord ++ tailWord_806478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806505 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 4, 3, 2]
def baseStart_806505 : Nat := 118140960795 + 806505 * 2 ^ 59
def prefixEnd_806505 : Nat := 4983230072969 + 3 ^ 40 * 806505 * 2
def baseEnd_806505 : Nat := 414124715254472279178457

theorem tailTrace_806505 : CollatzResearch.WordTrace tailWord_806505 prefixEnd_806505 414124715254472279178457 := by
  unfold tailWord_806505
  simp only [CollatzResearch.WordTrace]
  refine ⟨29415653943177599933060969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19610435962118399955373979 29415653943177599933060969)
  ·
    refine ⟨22061740457383199949795727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29415653943177599933060969 22061740457383199949795727)
    ·
      refine ⟨33092610686074799924693591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22061740457383199949795727 33092610686074799924693591)
      ·
        refine ⟨49638916029112199887040387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33092610686074799924693591 49638916029112199887040387)
        ·
          refine ⟨74458374043668299830560581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49638916029112199887040387 74458374043668299830560581)
          ·
            refine ⟨13960945133187806218230109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74458374043668299830560581 13960945133187806218230109)
            ·
              refine ⟨5235354424945427331836291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13960945133187806218230109 5235354424945427331836291)
              ·
                refine ⟨7853031637418140997754437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235354424945427331836291 7853031637418140997754437)
                ·
                  refine ⟨1472443432015901437078957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7853031637418140997754437 1472443432015901437078957)
                  ·
                    refine ⟨552166287005963038904609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472443432015901437078957 552166287005963038904609)
                    ·
                      refine ⟨414124715254472279178457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552166287005963038904609 414124715254472279178457)
                      ·
                        rfl

theorem cell23_806505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 3, 2].length) (baseStart_806505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806505 prefixEnd_806505 := by exact prefixLift 806505
  have htrace : WordTrace (prefixWord ++ tailWord_806505) baseStart_806505 baseEnd_806505 := by
    simpa [prefixWord, tailWord_806505, baseEnd_806505] using wordTrace_append hprefix tailTrace_806505
  have hstable : (prefixWord ++ tailWord_806505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806505).length < 2 ^ (prefixWord ++ tailWord_806505).sum := by decide
  have hdescent : baseEnd_806505 < baseStart_806505 := by decide
  rcases family_descends (prefixWord ++ tailWord_806505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806512 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3]
def baseStart_806512 : Nat := 118140960795 + 806512 * 2 ^ 59
def prefixEnd_806512 : Nat := 4983230072969 + 3 ^ 40 * 806512 * 2
def baseEnd_806512 : Nat := 414128309619053751790925

theorem tailTrace_806512 : CollatzResearch.WordTrace tailWord_806512 prefixEnd_806512 414128309619053751790925 := by
  unfold tailWord_806512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707954627076120064282895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19610606169434826752377193 14707954627076120064282895)
  ·
    refine ⟨22061931940614180096424343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14707954627076120064282895 22061931940614180096424343)
    ·
      refine ⟨33092897910921270144636515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22061931940614180096424343 33092897910921270144636515)
      ·
        refine ⟨49639346866381905216954773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33092897910921270144636515 49639346866381905216954773)
        ·
          refine ⟨2326844384361651807044755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49639346866381905216954773 2326844384361651807044755)
          ·
            refine ⟨3490266576542477710567133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326844384361651807044755 3490266576542477710567133)
            ·
              refine ⟨1308849966203429141462675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3490266576542477710567133 1308849966203429141462675)
              ·
                refine ⟨1963274949305143712194013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308849966203429141462675 1963274949305143712194013)
                ·
                  refine ⟨736228105989428892072755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1963274949305143712194013 736228105989428892072755)
                  ·
                    refine ⟨1104342158984143338109133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 736228105989428892072755 1104342158984143338109133)
                    ·
                      refine ⟨414128309619053751790925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104342158984143338109133 414128309619053751790925)
                      ·
                        rfl

theorem cell23_806512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_806512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806512 prefixEnd_806512 := by exact prefixLift 806512
  have htrace : WordTrace (prefixWord ++ tailWord_806512) baseStart_806512 baseEnd_806512 := by
    simpa [prefixWord, tailWord_806512, baseEnd_806512] using wordTrace_append hprefix tailTrace_806512
  have hstable : (prefixWord ++ tailWord_806512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806512).length < 2 ^ (prefixWord ++ tailWord_806512).sum := by decide
  have hdescent : baseEnd_806512 < baseStart_806512 := by decide
  rcases family_descends (prefixWord ++ tailWord_806512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806528 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_806528 : Nat := 118140960795 + 806528 * 2 ^ 59
def prefixEnd_806528 : Nat := 4983230072969 + 3 ^ 40 * 806528 * 2
def baseEnd_806528 : Nat := 138045508436508563063617

theorem tailTrace_806528 : CollatzResearch.WordTrace tailWord_806528 prefixEnd_806528 138045508436508563063617 := by
  unfold tailWord_806528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708246411047137430574119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19610995214729516574098825 14708246411047137430574119)
  ·
    refine ⟨22062369616570706145861179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14708246411047137430574119 22062369616570706145861179)
    ·
      refine ⟨33093554424856059218791769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22062369616570706145861179 33093554424856059218791769)
      ·
        refine ⟨24820165818642044414093827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33093554424856059218791769 24820165818642044414093827)
        ·
          refine ⟨37230248727963066621140741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24820165818642044414093827 37230248727963066621140741)
          ·
            refine ⟨6980671636493074991463889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37230248727963066621140741 6980671636493074991463889)
            ·
              refine ⟨5235503727369806243597917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980671636493074991463889 5235503727369806243597917)
              ·
                refine ⟨1963313897763677341349219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235503727369806243597917 1963313897763677341349219)
                ·
                  refine ⟨2944970846645516012023829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963313897763677341349219 2944970846645516012023829)
                  ·
                    refine ⟨138045508436508563063617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2944970846645516012023829 138045508436508563063617)
                    ·
                      rfl

theorem cell23_806528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_806528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806528 prefixEnd_806528 := by exact prefixLift 806528
  have htrace : WordTrace (prefixWord ++ tailWord_806528) baseStart_806528 baseEnd_806528 := by
    simpa [prefixWord, tailWord_806528, baseEnd_806528] using wordTrace_append hprefix tailTrace_806528
  have hstable : (prefixWord ++ tailWord_806528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806528).length < 2 ^ (prefixWord ++ tailWord_806528).sum := by decide
  have hdescent : baseEnd_806528 < baseStart_806528 := by decide
  rcases family_descends (prefixWord ++ tailWord_806528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806535 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_806535 : Nat := 118140960795 + 806535 * 2 ^ 59
def prefixEnd_806535 : Nat := 4983230072969 + 3 ^ 40 * 806535 * 2
def baseEnd_806535 : Nat := 414140119674107161803319

theorem tailTrace_806535 : CollatzResearch.WordTrace tailWord_806535 prefixEnd_806535 414140119674107161803319 := by
  unfold tailWord_806535
  simp only [CollatzResearch.WordTrace]
  refine ⟨29416748133068915056653059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19611165422045943371102039 29416748133068915056653059)
  ·
    refine ⟨44125122199603372584979589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29416748133068915056653059 44125122199603372584979589)
    ·
      refine ⟨8273460412425632359683673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44125122199603372584979589 8273460412425632359683673)
      ·
        refine ⟨6205095309319224269762755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8273460412425632359683673 6205095309319224269762755)
        ·
          refine ⟨9307642963978836404644133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205095309319224269762755 9307642963978836404644133)
          ·
            refine ⟨1745183055746031825870775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9307642963978836404644133 1745183055746031825870775)
            ·
              refine ⟨2617774583619047738806163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745183055746031825870775 2617774583619047738806163)
              ·
                refine ⟨3926661875428571608209245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617774583619047738806163 3926661875428571608209245)
                ·
                  refine ⟨1472498203285714353078467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3926661875428571608209245 1472498203285714353078467)
                  ·
                    refine ⟨2208747304928571529617701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1472498203285714353078467 2208747304928571529617701)
                    ·
                      refine ⟨414140119674107161803319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2208747304928571529617701 414140119674107161803319)
                      ·
                        rfl

theorem cell23_806535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_806535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806535 prefixEnd_806535 := by exact prefixLift 806535
  have htrace : WordTrace (prefixWord ++ tailWord_806535) baseStart_806535 baseEnd_806535 := by
    simpa [prefixWord, tailWord_806535, baseEnd_806535] using wordTrace_append hprefix tailTrace_806535
  have hstable : (prefixWord ++ tailWord_806535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806535).length < 2 ^ (prefixWord ++ tailWord_806535).sum := by decide
  have hdescent : baseEnd_806535 < baseStart_806535 := by decide
  rcases family_descends (prefixWord ++ tailWord_806535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806578 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_806578 : Nat := 118140960795 + 806578 * 2 ^ 59
def prefixEnd_806578 : Nat := 4983230072969 + 3 ^ 40 * 806578 * 2
def baseEnd_806578 : Nat := 414162199342250493565621

theorem tailTrace_806578 : CollatzResearch.WordTrace tailWord_806578 prefixEnd_806578 414162199342250493565621 := by
  unfold tailWord_806578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354579117978283350117097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19612210981275422266978925 7354579117978283350117097)
  ·
    refine ⟨5515934338483712512587823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7354579117978283350117097 5515934338483712512587823)
    ·
      refine ⟨8273901507725568768881735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515934338483712512587823 8273901507725568768881735)
      ·
        refine ⟨12410852261588353153322603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8273901507725568768881735 12410852261588353153322603)
        ·
          refine ⟨18616278392382529729983905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410852261588353153322603 18616278392382529729983905)
          ·
            refine ⟨13962208794286897297487929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18616278392382529729983905 13962208794286897297487929)
            ·
              refine ⟨10471656595715172973115947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13962208794286897297487929 10471656595715172973115947)
              ·
                refine ⟨15707484893572759459673921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471656595715172973115947 15707484893572759459673921)
                ·
                  refine ⟨11780613670179569594755441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15707484893572759459673921 11780613670179569594755441)
                  ·
                    refine ⟨8835460252634677196066581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11780613670179569594755441 8835460252634677196066581)
                    ·
                      refine ⟨414162199342250493565621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8835460252634677196066581 414162199342250493565621)
                      ·
                        rfl

theorem cell23_806578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_806578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806578 prefixEnd_806578 := by exact prefixLift 806578
  have htrace : WordTrace (prefixWord ++ tailWord_806578) baseStart_806578 baseEnd_806578 := by
    simpa [prefixWord, tailWord_806578, baseEnd_806578] using wordTrace_append hprefix tailTrace_806578
  have hstable : (prefixWord ++ tailWord_806578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806578).length < 2 ^ (prefixWord ++ tailWord_806578).sum := by decide
  have hdescent : baseEnd_806578 < baseStart_806578 := by decide
  rcases family_descends (prefixWord ++ tailWord_806578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806585 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_806585 : Nat := 118140960795 + 806585 * 2 ^ 59
def prefixEnd_806585 : Nat := 4983230072969 + 3 ^ 40 * 806585 * 2
def baseEnd_806585 : Nat := 414165793706831966178089

theorem tailTrace_806585 : CollatzResearch.WordTrace tailWord_806585 prefixEnd_806585 414165793706831966178089 := by
  unfold tailWord_806585
  simp only [CollatzResearch.WordTrace]
  refine ⟨29418571782887773595973209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19612381188591849063982139 29418571782887773595973209)
  ·
    refine ⟨22063928837165830196979907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29418571782887773595973209 22063928837165830196979907)
    ·
      refine ⟨33095893255748745295469861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22063928837165830196979907 33095893255748745295469861)
      ·
        refine ⟨6205479985452889742900599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33095893255748745295469861 6205479985452889742900599)
        ·
          refine ⟨9308219978179334614350899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205479985452889742900599 9308219978179334614350899)
          ·
            refine ⟨13962329967269001921526349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9308219978179334614350899 13962329967269001921526349)
            ·
              refine ⟨5235873737725875720572381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13962329967269001921526349 5235873737725875720572381)
              ·
                refine ⟨1963452651647203395214643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235873737725875720572381 1963452651647203395214643)
                ·
                  refine ⟨2945178977470805092821965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963452651647203395214643 2945178977470805092821965)
                  ·
                    refine ⟨1104442116551551909808237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945178977470805092821965 1104442116551551909808237)
                    ·
                      refine ⟨414165793706831966178089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104442116551551909808237 414165793706831966178089)
                      ·
                        rfl

theorem cell23_806585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_806585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806585 prefixEnd_806585 := by exact prefixLift 806585
  have htrace : WordTrace (prefixWord ++ tailWord_806585) baseStart_806585 baseEnd_806585 := by
    simpa [prefixWord, tailWord_806585, baseEnd_806585] using wordTrace_append hprefix tailTrace_806585
  have hstable : (prefixWord ++ tailWord_806585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806585).length < 2 ^ (prefixWord ++ tailWord_806585).sum := by decide
  have hdescent : baseEnd_806585 < baseStart_806585 := by decide
  rcases family_descends (prefixWord ++ tailWord_806585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806608 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_806608 : Nat := 118140960795 + 806608 * 2 ^ 59
def prefixEnd_806608 : Nat := 4983230072969 + 3 ^ 40 * 806608 * 2
def baseEnd_806608 : Nat := 414177603761885376190483

theorem tailTrace_806608 : CollatzResearch.WordTrace tailWord_806608 prefixEnd_806608 414177603761885376190483 := by
  unfold tailWord_806608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14709705330902224262030239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19612940441202965682706985 14709705330902224262030239)
  ·
    refine ⟨22064557996353336393045359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14709705330902224262030239 22064557996353336393045359)
    ·
      refine ⟨33096836994530004589568039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22064557996353336393045359 33096836994530004589568039)
      ·
        refine ⟨49645255491795006884352059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33096836994530004589568039 49645255491795006884352059)
        ·
          refine ⟨74467883237692510326528089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49645255491795006884352059 74467883237692510326528089)
          ·
            refine ⟨55850912428269382744896067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74467883237692510326528089 55850912428269382744896067)
            ·
              refine ⟨83776368642404074117344101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55850912428269382744896067 83776368642404074117344101)
              ·
                refine ⟨15708069120450763897002019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83776368642404074117344101 15708069120450763897002019)
                ·
                  refine ⟨23562103680676145845503029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15708069120450763897002019 23562103680676145845503029)
                  ·
                    refine ⟨2208947220063388673015909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23562103680676145845503029 2208947220063388673015909)
                    ·
                      refine ⟨414177603761885376190483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2208947220063388673015909 414177603761885376190483)
                      ·
                        rfl

theorem cell23_806608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_806608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806608 prefixEnd_806608 := by exact prefixLift 806608
  have htrace : WordTrace (prefixWord ++ tailWord_806608) baseStart_806608 baseEnd_806608 := by
    simpa [prefixWord, tailWord_806608, baseEnd_806608] using wordTrace_append hprefix tailTrace_806608
  have hstable : (prefixWord ++ tailWord_806608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806608).length < 2 ^ (prefixWord ++ tailWord_806608).sum := by decide
  have hdescent : baseEnd_806608 < baseStart_806608 := by decide
  rcases family_descends (prefixWord ++ tailWord_806608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806646 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_806646 : Nat := 118140960795 + 806646 * 2 ^ 59
def prefixEnd_806646 : Nat := 4983230072969 + 3 ^ 40 * 806646 * 2
def baseEnd_806646 : Nat := 414197116026756227515309

theorem tailTrace_806646 : CollatzResearch.WordTrace tailWord_806646 prefixEnd_806646 414197116026756227515309 := by
  unfold tailWord_806646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838799789729173813371487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19613864423777854009295861 1838799789729173813371487)
  ·
    refine ⟨2758199684593760720057231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838799789729173813371487 2758199684593760720057231)
    ·
      refine ⟨4137299526890641080085847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758199684593760720057231 4137299526890641080085847)
      ·
        refine ⟨6205949290335961620128771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137299526890641080085847 6205949290335961620128771)
        ·
          refine ⟨9308923935503942430193157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205949290335961620128771 9308923935503942430193157)
          ·
            refine ⟨1745423237906989205661217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9308923935503942430193157 1745423237906989205661217)
            ·
              refine ⟨1309067428430241904245913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745423237906989205661217 1309067428430241904245913)
              ·
                refine ⟨981800571322681428184435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309067428430241904245913 981800571322681428184435)
                ·
                  refine ⟨1472700856984022142276653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981800571322681428184435 1472700856984022142276653)
                  ·
                    refine ⟨552262821369008303353745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1472700856984022142276653 552262821369008303353745)
                    ·
                      refine ⟨414197116026756227515309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552262821369008303353745 414197116026756227515309)
                      ·
                        rfl

theorem cell23_806646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_806646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806646 prefixEnd_806646 := by exact prefixLift 806646
  have htrace : WordTrace (prefixWord ++ tailWord_806646) baseStart_806646 baseEnd_806646 := by
    simpa [prefixWord, tailWord_806646, baseEnd_806646] using wordTrace_append hprefix tailTrace_806646
  have hstable : (prefixWord ++ tailWord_806646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806646).length < 2 ^ (prefixWord ++ tailWord_806646).sum := by decide
  have hdescent : baseEnd_806646 < baseStart_806646 := by decide
  rcases family_descends (prefixWord ++ tailWord_806646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806648 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 9]
def baseStart_806648 : Nat := 118140960795 + 806648 * 2 ^ 59
def prefixEnd_806648 : Nat := 4983230072969 + 3 ^ 40 * 806648 * 2
def baseEnd_806648 : Nat := 46022015887562802187811

theorem tailTrace_806648 : CollatzResearch.WordTrace tailWord_806648 prefixEnd_806648 46022015887562802187811 := by
  unfold tailWord_806648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710434790829767677758299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19613913054439690237011065 14710434790829767677758299)
  ·
    refine ⟨22065652186244651516637449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14710434790829767677758299 22065652186244651516637449)
    ·
      refine ⟨16549239139683488637478087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22065652186244651516637449 16549239139683488637478087)
      ·
        refine ⟨24823858709525232956217131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549239139683488637478087 24823858709525232956217131)
        ·
          refine ⟨37235788064287849434325697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24823858709525232956217131 37235788064287849434325697)
          ·
            refine ⟨27926841048215887075744273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37235788064287849434325697 27926841048215887075744273)
            ·
              refine ⟨20945130786161915306808205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27926841048215887075744273 20945130786161915306808205)
              ·
                refine ⟨7854424044810718240053077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20945130786161915306808205 7854424044810718240053077)
                ·
                  refine ⟨46022015887562802187811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7854424044810718240053077 46022015887562802187811)
                  ·
                    rfl

theorem cell23_806648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_806648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806648 prefixEnd_806648 := by exact prefixLift 806648
  have htrace : WordTrace (prefixWord ++ tailWord_806648) baseStart_806648 baseEnd_806648 := by
    simpa [prefixWord, tailWord_806648, baseEnd_806648] using wordTrace_append hprefix tailTrace_806648
  have hstable : (prefixWord ++ tailWord_806648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806648).length < 2 ^ (prefixWord ++ tailWord_806648).sum := by decide
  have hdescent : baseEnd_806648 < baseStart_806648 := by decide
  rcases family_descends (prefixWord ++ tailWord_806648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806675 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3]
def baseStart_806675 : Nat := 118140960795 + 806675 * 2 ^ 59
def prefixEnd_806675 : Nat := 4983230072969 + 3 ^ 40 * 806675 * 2
def baseEnd_806675 : Nat := 414212006965736614052675

theorem tailTrace_806675 : CollatzResearch.WordTrace tailWord_806675 prefixEnd_806675 414212006965736614052675 := by
  unfold tailWord_806675
  simp only [CollatzResearch.WordTrace]
  refine ⟨29421854352561718966749479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19614569568374479311166319 29421854352561718966749479)
  ·
    refine ⟨44132781528842578450124219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29421854352561718966749479 44132781528842578450124219)
    ·
      refine ⟨66199172293263867675186329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44132781528842578450124219 66199172293263867675186329)
      ·
        refine ⟨49649379219947900756389747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66199172293263867675186329 49649379219947900756389747)
        ·
          refine ⟨74474068829921851134584621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49649379219947900756389747 74474068829921851134584621)
          ·
            refine ⟨27927775811220694175469233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74474068829921851134584621 27927775811220694175469233)
            ·
              refine ⟨20945831858415520631601925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27927775811220694175469233 20945831858415520631601925)
              ·
                refine ⟨3927343473452910118425361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20945831858415520631601925 3927343473452910118425361)
                ·
                  refine ⟨2945507605089682588819021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927343473452910118425361 2945507605089682588819021)
                  ·
                    refine ⟨1104565351908630970807133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945507605089682588819021 1104565351908630970807133)
                    ·
                      refine ⟨414212006965736614052675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104565351908630970807133 414212006965736614052675)
                      ·
                        rfl

theorem cell23_806675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_806675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806675 prefixEnd_806675 := by exact prefixLift 806675
  have htrace : WordTrace (prefixWord ++ tailWord_806675) baseStart_806675 baseEnd_806675 := by
    simpa [prefixWord, tailWord_806675, baseEnd_806675] using wordTrace_append hprefix tailTrace_806675
  have hstable : (prefixWord ++ tailWord_806675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806675).length < 2 ^ (prefixWord ++ tailWord_806675).sum := by decide
  have hdescent : baseEnd_806675 < baseStart_806675 := by decide
  rcases family_descends (prefixWord ++ tailWord_806675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806682 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_806682 : Nat := 118140960795 + 806682 * 2 ^ 59
def prefixEnd_806682 : Nat := 4983230072969 + 3 ^ 40 * 806682 * 2
def baseEnd_806682 : Nat := 46023955703368676296127

theorem tailTrace_806682 : CollatzResearch.WordTrace tailWord_806682 prefixEnd_806682 46023955703368676296127 := by
  unfold tailWord_806682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355527415884089790563575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19614739775690906108169533 7355527415884089790563575)
  ·
    refine ⟨11033291123826134685845363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7355527415884089790563575 11033291123826134685845363)
    ·
      refine ⟨16549936685739202028768045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033291123826134685845363 16549936685739202028768045)
      ·
        refine ⟨6206226257152200760788017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16549936685739202028768045 6206226257152200760788017)
        ·
          refine ⟨4654669692864150570591013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6206226257152200760788017 4654669692864150570591013)
          ·
            refine ⟨872750567412028231985815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4654669692864150570591013 872750567412028231985815)
            ·
              refine ⟨1309125851118042347978723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872750567412028231985815 1309125851118042347978723)
              ·
                refine ⟨1963688776677063521968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309125851118042347978723 1963688776677063521968085)
                ·
                  refine ⟨46023955703368676296127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1963688776677063521968085 46023955703368676296127)
                  ·
                    rfl

theorem cell23_806682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_806682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806682 prefixEnd_806682 := by exact prefixLift 806682
  have htrace : WordTrace (prefixWord ++ tailWord_806682) baseStart_806682 baseEnd_806682 := by
    simpa [prefixWord, tailWord_806682, baseEnd_806682] using wordTrace_append hprefix tailTrace_806682
  have hstable : (prefixWord ++ tailWord_806682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806682).length < 2 ^ (prefixWord ++ tailWord_806682).sum := by decide
  have hdescent : baseEnd_806682 < baseStart_806682 := by decide
  rcases family_descends (prefixWord ++ tailWord_806682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806693 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_806693 : Nat := 118140960795 + 806693 * 2 ^ 59
def prefixEnd_806693 : Nat := 4983230072969 + 3 ^ 40 * 806693 * 2
def baseEnd_806693 : Nat := 414221249617517543627593

theorem tailTrace_806693 : CollatzResearch.WordTrace tailWord_806693 prefixEnd_806693 414221249617517543627593 := by
  unfold tailWord_806693
  simp only [CollatzResearch.WordTrace]
  refine ⟨29422510866496508040904733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19615007244331005360603155 29422510866496508040904733)
  ·
    refine ⟨11033441574936190515339275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29422510866496508040904733 11033441574936190515339275)
    ·
      refine ⟨16550162362404285773008913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033441574936190515339275 16550162362404285773008913)
      ·
        refine ⟨12412621771803214329756685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16550162362404285773008913 12412621771803214329756685)
        ·
          refine ⟨4654733164426205373658757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12412621771803214329756685 4654733164426205373658757)
          ·
            refine ⟨872762468329913507561017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4654733164426205373658757 872762468329913507561017)
            ·
              refine ⟨654571851247435130670763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872762468329913507561017 654571851247435130670763)
              ·
                refine ⟨981857776871152696006145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654571851247435130670763 981857776871152696006145)
                ·
                  refine ⟨736393332653364522004609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981857776871152696006145 736393332653364522004609)
                  ·
                    refine ⟨552294999490023391503457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736393332653364522004609 552294999490023391503457)
                    ·
                      refine ⟨414221249617517543627593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552294999490023391503457 414221249617517543627593)
                      ·
                        rfl

theorem cell23_806693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_806693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806693 prefixEnd_806693 := by exact prefixLift 806693
  have htrace : WordTrace (prefixWord ++ tailWord_806693) baseStart_806693 baseEnd_806693 := by
    simpa [prefixWord, tailWord_806693, baseEnd_806693] using wordTrace_append hprefix tailTrace_806693
  have hstable : (prefixWord ++ tailWord_806693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806693).length < 2 ^ (prefixWord ++ tailWord_806693).sum := by decide
  have hdescent : baseEnd_806693 < baseStart_806693 := by decide
  rcases family_descends (prefixWord ++ tailWord_806693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806712 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_806712 : Nat := 118140960795 + 806712 * 2 ^ 59
def prefixEnd_806712 : Nat := 4983230072969 + 3 ^ 40 * 806712 * 2
def baseEnd_806712 : Nat := 138077001916650989763335

theorem tailTrace_806712 : CollatzResearch.WordTrace tailWord_806712 prefixEnd_806712 138077001916650989763335 := by
  unfold tailWord_806712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711601926713837142923195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19615469235618449523897593 14711601926713837142923195)
  ·
    refine ⟨22067402890070755714384793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14711601926713837142923195 22067402890070755714384793)
    ·
      refine ⟨16550552167553066785788595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22067402890070755714384793 16550552167553066785788595)
      ·
        refine ⟨24825828251329600178682893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16550552167553066785788595 24825828251329600178682893)
        ·
          refine ⟨9309685594248600067006085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24825828251329600178682893 9309685594248600067006085)
          ·
            refine ⟨1745566048921612512563641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9309685594248600067006085 1745566048921612512563641)
            ·
              refine ⟨1309174536691209384422731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745566048921612512563641 1309174536691209384422731)
              ·
                refine ⟨1963761805036814076634097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309174536691209384422731 1963761805036814076634097)
                ·
                  refine ⟨1472821353777610557475573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963761805036814076634097 1472821353777610557475573)
                  ·
                    refine ⟨138077001916650989763335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1472821353777610557475573 138077001916650989763335)
                    ·
                      rfl

theorem cell23_806712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_806712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806712 prefixEnd_806712 := by exact prefixLift 806712
  have htrace : WordTrace (prefixWord ++ tailWord_806712) baseStart_806712 baseEnd_806712 := by
    simpa [prefixWord, tailWord_806712, baseEnd_806712] using wordTrace_append hprefix tailTrace_806712
  have hstable : (prefixWord ++ tailWord_806712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806712).length < 2 ^ (prefixWord ++ tailWord_806712).sum := by decide
  have hdescent : baseEnd_806712 < baseStart_806712 := by decide
  rcases family_descends (prefixWord ++ tailWord_806712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806733 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 5]
def baseStart_806733 : Nat := 118140960795 + 806733 * 2 ^ 59
def prefixEnd_806733 : Nat := 4983230072969 + 3 ^ 40 * 806733 * 2
def baseEnd_806733 : Nat := 46026865427077487458601

theorem tailTrace_806733 : CollatzResearch.WordTrace tailWord_806733 prefixEnd_806733 46026865427077487458601 := by
  unfold tailWord_806733
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423969786351594872360853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19615979857567729914907235 29423969786351594872360853)
  ·
    refine ⟨1379248583735231009641915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29423969786351594872360853 1379248583735231009641915)
    ·
      refine ⟨2068872875602846514462873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379248583735231009641915 2068872875602846514462873)
      ·
        refine ⟨1551654656702134885847155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2068872875602846514462873 1551654656702134885847155)
        ·
          refine ⟨2327481985053202328770733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551654656702134885847155 2327481985053202328770733)
          ·
            refine ⟨872805744394950873289025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2327481985053202328770733 872805744394950873289025)
            ·
              refine ⟨654604308296213154966769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872805744394950873289025 654604308296213154966769)
              ·
                refine ⟨490953231222159866225077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654604308296213154966769 490953231222159866225077)
                ·
                  refine ⟨46026865427077487458601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490953231222159866225077 46026865427077487458601)
                  ·
                    rfl

theorem cell23_806733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_806733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806733 prefixEnd_806733 := by exact prefixLift 806733
  have htrace : WordTrace (prefixWord ++ tailWord_806733) baseStart_806733 baseEnd_806733 := by
    simpa [prefixWord, tailWord_806733, baseEnd_806733] using wordTrace_append hprefix tailTrace_806733
  have hstable : (prefixWord ++ tailWord_806733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806733).length < 2 ^ (prefixWord ++ tailWord_806733).sum := by decide
  have hdescent : baseEnd_806733 < baseStart_806733 := by decide
  rcases family_descends (prefixWord ++ tailWord_806733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806766 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_806766 : Nat := 118140960795 + 806766 * 2 ^ 59
def prefixEnd_806766 : Nat := 4983230072969 + 3 ^ 40 * 806766 * 2
def baseEnd_806766 : Nat := 414258733705295758014757

theorem tailTrace_806766 : CollatzResearch.WordTrace tailWord_806766 prefixEnd_806766 414258733705295758014757 := by
  unfold tailWord_806766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3678146674404005188539019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19616782263488027672208101 3678146674404005188539019)
  ·
    refine ⟨5517220011606007782808529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3678146674404005188539019 5517220011606007782808529)
    ·
      refine ⟨4137915008704505837106397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5517220011606007782808529 4137915008704505837106397)
      ·
        refine ⟨1551718128264189688914899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4137915008704505837106397 1551718128264189688914899)
        ·
          refine ⟨2327577192396284533372349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551718128264189688914899 2327577192396284533372349)
          ·
            refine ⟨872841447148606700014631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2327577192396284533372349 872841447148606700014631)
            ·
              refine ⟨1309262170722910050021947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872841447148606700014631 1309262170722910050021947)
              ·
                refine ⟨1963893256084365075032921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309262170722910050021947 1963893256084365075032921)
                ·
                  refine ⟨1472919942063273806274691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963893256084365075032921 1472919942063273806274691)
                  ·
                    refine ⟨2209379913094910709412037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1472919942063273806274691 2209379913094910709412037)
                    ·
                      refine ⟨414258733705295758014757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2209379913094910709412037 414258733705295758014757)
                      ·
                        rfl

theorem cell23_806766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_806766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806766 prefixEnd_806766 := by exact prefixLift 806766
  have htrace : WordTrace (prefixWord ++ tailWord_806766) baseStart_806766 baseEnd_806766 := by
    simpa [prefixWord, tailWord_806766, baseEnd_806766] using wordTrace_append hprefix tailTrace_806766
  have hstable : (prefixWord ++ tailWord_806766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806766).length < 2 ^ (prefixWord ++ tailWord_806766).sum := by decide
  have hdescent : baseEnd_806766 < baseStart_806766 := by decide
  rcases family_descends (prefixWord ++ tailWord_806766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806833 : List Nat := [1, 2, 2, 4, 2, 1, 3, 3, 1, 1, 3]
def baseStart_806833 : Nat := 118140960795 + 806833 * 2 ^ 59
def prefixEnd_806833 : Nat := 4983230072969 + 3 ^ 40 * 806833 * 2
def baseEnd_806833 : Nat := 414293136909146995876949

theorem tailTrace_806833 : CollatzResearch.WordTrace tailWord_806833 prefixEnd_806833 414293136909146995876949 := by
  unfold tailWord_806833
  simp only [CollatzResearch.WordTrace]
  refine ⟨29427617085989311951001153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19618411390659541300667435 29427617085989311951001153)
  ·
    refine ⟨22070712814491983963250865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29427617085989311951001153 22070712814491983963250865)
    ·
      refine ⟨16553034610868987972438149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22070712814491983963250865 16553034610868987972438149)
      ·
        refine ⟨3103693989537935244832153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16553034610868987972438149 3103693989537935244832153)
        ·
          refine ⟨2327770492153451433624115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3103693989537935244832153 2327770492153451433624115)
          ·
            refine ⟨3491655738230177150436173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327770492153451433624115 3491655738230177150436173)
            ·
              refine ⟨1309370901836316431413565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3491655738230177150436173 1309370901836316431413565)
              ·
                refine ⟨491014088188618661780087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309370901836316431413565 491014088188618661780087)
                ·
                  refine ⟨736521132282927992670131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491014088188618661780087 736521132282927992670131)
                  ·
                    refine ⟨1104781698424391989005197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 736521132282927992670131 1104781698424391989005197)
                    ·
                      refine ⟨414293136909146995876949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1104781698424391989005197 414293136909146995876949)
                      ·
                        rfl

theorem cell23_806833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_806833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806833 prefixEnd_806833 := by exact prefixLift 806833
  have htrace : WordTrace (prefixWord ++ tailWord_806833) baseStart_806833 baseEnd_806833 := by
    simpa [prefixWord, tailWord_806833, baseEnd_806833] using wordTrace_append hprefix tailTrace_806833
  have hstable : (prefixWord ++ tailWord_806833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806833).length < 2 ^ (prefixWord ++ tailWord_806833).sum := by decide
  have hdescent : baseEnd_806833 < baseStart_806833 := by decide
  rcases family_descends (prefixWord ++ tailWord_806833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806862 : List Nat := [4, 1, 1, 1, 2, 2, 4, 8]
def baseStart_806862 : Nat := 118140960795 + 806862 * 2 ^ 59
def prefixEnd_806862 : Nat := 4983230072969 + 3 ^ 40 * 806862 * 2
def baseEnd_806862 : Nat := 15344741772152866015345

theorem tailTrace_806862 : CollatzResearch.WordTrace tailWord_806862 prefixEnd_806862 15344741772152866015345 := by
  unfold tailWord_806862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3678584350360531237975855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19619116535256166602537893 3678584350360531237975855)
  ·
    refine ⟨5517876525540796856963783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3678584350360531237975855 5517876525540796856963783)
    ·
      refine ⟨8276814788311195285445675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517876525540796856963783 8276814788311195285445675)
      ·
        refine ⟨12415222182466792928168513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8276814788311195285445675 12415222182466792928168513)
        ·
          refine ⟨9311416636850094696126385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12415222182466792928168513 9311416636850094696126385)
          ·
            refine ⟨6983562477637571022094789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9311416636850094696126385 6983562477637571022094789)
            ·
              refine ⟨1309417964557044566642773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6983562477637571022094789 1309417964557044566642773)
              ·
                refine ⟨15344741772152866015345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1309417964557044566642773 15344741772152866015345)
                ·
                  rfl

theorem cell23_806862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_806862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806862 prefixEnd_806862 := by exact prefixLift 806862
  have htrace : WordTrace (prefixWord ++ tailWord_806862) baseStart_806862 baseEnd_806862 := by
    simpa [prefixWord, tailWord_806862, baseEnd_806862] using wordTrace_append hprefix tailTrace_806862
  have hstable : (prefixWord ++ tailWord_806862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806862).length < 2 ^ (prefixWord ++ tailWord_806862).sum := by decide
  have hdescent : baseEnd_806862 < baseStart_806862 := by decide
  rcases family_descends (prefixWord ++ tailWord_806862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806870 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_806870 : Nat := 118140960795 + 806870 * 2 ^ 59
def prefixEnd_806870 : Nat := 4983230072969 + 3 ^ 40 * 806870 * 2
def baseEnd_806870 : Nat := 138104045231121117038093

theorem tailTrace_806870 : CollatzResearch.WordTrace tailWord_806870 prefixEnd_806870 138104045231121117038093 := by
  unfold tailWord_806870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839310411678454204381129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19619311057903511513398709 1839310411678454204381129)
  ·
    refine ⟨1379482808758840653285847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839310411678454204381129 1379482808758840653285847)
    ·
      refine ⟨2069224213138260979928771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379482808758840653285847 2069224213138260979928771)
      ·
        refine ⟨3103836319707391469893157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069224213138260979928771 3103836319707391469893157)
        ·
          refine ⟨581969309945135900604967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3103836319707391469893157 581969309945135900604967)
          ·
            refine ⟨872953964917703850907451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581969309945135900604967 872953964917703850907451)
            ·
              refine ⟨1309430947376555776361177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872953964917703850907451 1309430947376555776361177)
              ·
                refine ⟨982073210532416832270883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309430947376555776361177 982073210532416832270883)
                ·
                  refine ⟨1473109815798625248406325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982073210532416832270883 1473109815798625248406325)
                  ·
                    refine ⟨138104045231121117038093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1473109815798625248406325 138104045231121117038093)
                    ·
                      rfl

theorem cell23_806870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_806870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806870 prefixEnd_806870 := by exact prefixLift 806870
  have htrace : WordTrace (prefixWord ++ tailWord_806870) baseStart_806870 baseEnd_806870 := by
    simpa [prefixWord, tailWord_806870, baseEnd_806870] using wordTrace_append hprefix tailTrace_806870
  have hstable : (prefixWord ++ tailWord_806870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806870).length < 2 ^ (prefixWord ++ tailWord_806870).sum := by decide
  have hdescent : baseEnd_806870 < baseStart_806870 := by decide
  rcases family_descends (prefixWord ++ tailWord_806870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806873 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 1, 1, 4]
def baseStart_806873 : Nat := 118140960795 + 806873 * 2 ^ 59
def prefixEnd_806873 : Nat := 4983230072969 + 3 ^ 40 * 806873 * 2
def baseEnd_806873 : Nat := 414313676135326839376765

theorem tailTrace_806873 : CollatzResearch.WordTrace tailWord_806873 prefixEnd_806873 414313676135326839376765 := by
  unfold tailWord_806873
  simp only [CollatzResearch.WordTrace]
  refine ⟨29429076005844398782457273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19619384003896265854971515 29429076005844398782457273)
  ·
    refine ⟨22071807004383299086842955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29429076005844398782457273 22071807004383299086842955)
    ·
      refine ⟨33107710506574948630264433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071807004383299086842955 33107710506574948630264433)
      ·
        refine ⟨24830782879931211472698325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33107710506574948630264433 24830782879931211472698325)
        ·
          refine ⟨581971473748387768891367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24830782879931211472698325 581971473748387768891367)
          ·
            refine ⟨872957210622581653337051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581971473748387768891367 872957210622581653337051)
            ·
              refine ⟨1309435815933872480005577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872957210622581653337051 1309435815933872480005577)
              ·
                refine ⟨982076861950404360004183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309435815933872480005577 982076861950404360004183)
                ·
                  refine ⟨1473115292925606540006275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982076861950404360004183 1473115292925606540006275)
                  ·
                    refine ⟨2209672939388409810009413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1473115292925606540006275 2209672939388409810009413)
                    ·
                      refine ⟨414313676135326839376765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2209672939388409810009413 414313676135326839376765)
                      ·
                        rfl

theorem cell23_806873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_806873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806873 prefixEnd_806873 := by exact prefixLift 806873
  have htrace : WordTrace (prefixWord ++ tailWord_806873) baseStart_806873 baseEnd_806873 := by
    simpa [prefixWord, tailWord_806873, baseEnd_806873] using wordTrace_append hprefix tailTrace_806873
  have hstable : (prefixWord ++ tailWord_806873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806873).length < 2 ^ (prefixWord ++ tailWord_806873).sum := by decide
  have hdescent : baseEnd_806873 < baseStart_806873 := by decide
  rcases family_descends (prefixWord ++ tailWord_806873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806893 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_806893 : Nat := 118140960795 + 806893 * 2 ^ 59
def prefixEnd_806893 : Nat := 4983230072969 + 3 ^ 40 * 806893 * 2
def baseEnd_806893 : Nat := 414323945748416761126673

theorem tailTrace_806893 : CollatzResearch.WordTrace tailWord_806893 prefixEnd_806893 414323945748416761126673 := by
  unfold tailWord_806893
  simp only [CollatzResearch.WordTrace]
  refine ⟨29429805465771942198185333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19619870310514628132123555 29429805465771942198185333)
  ·
    refine ⟨2759044262416119581079875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29429805465771942198185333 2759044262416119581079875)
    ·
      refine ⟨4138566393624179371619813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759044262416119581079875 4138566393624179371619813)
      ·
        refine ⟨775981198804533632178715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4138566393624179371619813 775981198804533632178715)
        ·
          refine ⟨1163971798206800448268073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775981198804533632178715 1163971798206800448268073)
          ·
            refine ⟨872978848655100336201055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163971798206800448268073 872978848655100336201055)
            ·
              refine ⟨1309468272982650504301583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872978848655100336201055 1309468272982650504301583)
              ·
                refine ⟨1964202409473975756452375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309468272982650504301583 1964202409473975756452375)
                ·
                  refine ⟨2946303614210963634678563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964202409473975756452375 2946303614210963634678563)
                  ·
                    refine ⟨4419455421316445452017845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946303614210963634678563 4419455421316445452017845)
                    ·
                      refine ⟨414323945748416761126673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4419455421316445452017845 414323945748416761126673)
                      ·
                        rfl

theorem cell23_806893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_806893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806893 prefixEnd_806893 := by exact prefixLift 806893
  have htrace : WordTrace (prefixWord ++ tailWord_806893) baseStart_806893 baseEnd_806893 := by
    simpa [prefixWord, tailWord_806893, baseEnd_806893] using wordTrace_append hprefix tailTrace_806893
  have hstable : (prefixWord ++ tailWord_806893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806893).length < 2 ^ (prefixWord ++ tailWord_806893).sum := by decide
  have hdescent : baseEnd_806893 < baseStart_806893 := by decide
  rcases family_descends (prefixWord ++ tailWord_806893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806946 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_806946 : Nat := 118140960795 + 806946 * 2 ^ 59
def prefixEnd_806946 : Nat := 4983230072969 + 3 ^ 40 * 806946 * 2
def baseEnd_806946 : Nat := 414351160223105053763929

theorem tailTrace_806946 : CollatzResearch.WordTrace tailWord_806946 prefixEnd_806946 414351160223105053763929 := by
  unfold tailWord_806946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7357934633644983062466173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19621159023053288166576461 7357934633644983062466173)
  ·
    refine ⟨2759225487616868648424815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7357934633644983062466173 2759225487616868648424815)
    ·
      refine ⟨4138838231425302972637223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759225487616868648424815 4138838231425302972637223)
      ·
        refine ⟨6208257347137954458955835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4138838231425302972637223 6208257347137954458955835)
        ·
          refine ⟨9312386020706931688433753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6208257347137954458955835 9312386020706931688433753)
          ·
            refine ⟨6984289515530198766325315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9312386020706931688433753 6984289515530198766325315)
            ·
              refine ⟨10476434273295298149487973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984289515530198766325315 10476434273295298149487973)
              ·
                refine ⟨1964331426242868403028995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10476434273295298149487973 1964331426242868403028995)
                ·
                  refine ⟨2946497139364302604543493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964331426242868403028995 2946497139364302604543493)
                  ·
                    refine ⟨552468213630806738351905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946497139364302604543493 552468213630806738351905)
                    ·
                      refine ⟨414351160223105053763929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552468213630806738351905 414351160223105053763929)
                      ·
                        rfl

theorem cell23_806946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_806946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806946 prefixEnd_806946 := by exact prefixLift 806946
  have htrace : WordTrace (prefixWord ++ tailWord_806946) baseStart_806946 baseEnd_806946 := by
    simpa [prefixWord, tailWord_806946, baseEnd_806946] using wordTrace_append hprefix tailTrace_806946
  have hstable : (prefixWord ++ tailWord_806946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806946).length < 2 ^ (prefixWord ++ tailWord_806946).sum := by decide
  have hdescent : baseEnd_806946 < baseStart_806946 := by decide
  rcases family_descends (prefixWord ++ tailWord_806946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806963 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 2, 2, 2]
def baseStart_806963 : Nat := 118140960795 + 806963 * 2 ^ 59
def prefixEnd_806963 : Nat := 4983230072969 + 3 ^ 40 * 806963 * 2
def baseEnd_806963 : Nat := 414359889394231487251351

theorem tailTrace_806963 : CollatzResearch.WordTrace tailWord_806963 prefixEnd_806963 414359889394231487251351 := by
  unfold tailWord_806963
  simp only [CollatzResearch.WordTrace]
  refine ⟨29432358575518344153233543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19621572383678896102155695 29432358575518344153233543)
  ·
    refine ⟨44148537863277516229850315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29432358575518344153233543 44148537863277516229850315)
    ·
      refine ⟨66222806794916274344775473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44148537863277516229850315 66222806794916274344775473)
      ·
        refine ⟨49667105096187205758581605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66222806794916274344775473 49667105096187205758581605)
        ·
          refine ⟨9312582205535101079734051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49667105096187205758581605 9312582205535101079734051)
          ·
            refine ⟨13968873308302651619601077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312582205535101079734051 13968873308302651619601077)
            ·
              refine ⟨1309581872653373589337601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13968873308302651619601077 1309581872653373589337601)
              ·
                refine ⟨982186404490030192003201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309581872653373589337601 982186404490030192003201)
                ·
                  refine ⟨736639803367522644002401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982186404490030192003201 736639803367522644002401)
                  ·
                    refine ⟨552479852525641983001801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736639803367522644002401 552479852525641983001801)
                    ·
                      refine ⟨414359889394231487251351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552479852525641983001801 414359889394231487251351)
                      ·
                        rfl

theorem cell23_806963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 2, 2].length) (baseStart_806963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806963 prefixEnd_806963 := by exact prefixLift 806963
  have htrace : WordTrace (prefixWord ++ tailWord_806963) baseStart_806963 baseEnd_806963 := by
    simpa [prefixWord, tailWord_806963, baseEnd_806963] using wordTrace_append hprefix tailTrace_806963
  have hstable : (prefixWord ++ tailWord_806963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806963).length < 2 ^ (prefixWord ++ tailWord_806963).sum := by decide
  have hdescent : baseEnd_806963 < baseStart_806963 := by decide
  rcases family_descends (prefixWord ++ tailWord_806963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806992 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_806992 : Nat := 118140960795 + 806992 * 2 ^ 59
def prefixEnd_806992 : Nat := 4983230072969 + 3 ^ 40 * 806992 * 2
def baseEnd_806992 : Nat := 414374780333211873788717

theorem tailTrace_806992 : CollatzResearch.WordTrace tailWord_806992 prefixEnd_806992 414374780333211873788717 := by
  unfold tailWord_806992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716708146206641053019615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19622277528275521404026153 14716708146206641053019615)
  ·
    refine ⟨22075062219309961579529423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14716708146206641053019615 22075062219309961579529423)
    ·
      refine ⟨33112593328964942369294135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22075062219309961579529423 33112593328964942369294135)
      ·
        refine ⟨49668889993447413553941203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33112593328964942369294135 49668889993447413553941203)
        ·
          refine ⟨74503334990171120330911805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49668889993447413553941203 74503334990171120330911805)
          ·
            refine ⟨27938750621314170124091927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74503334990171120330911805 27938750621314170124091927)
            ·
              refine ⟨41908125931971255186137891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27938750621314170124091927 41908125931971255186137891)
              ·
                refine ⟨62862188897956882779206837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41908125931971255186137891 62862188897956882779206837)
                ·
                  refine ⟨5893330209183457760550641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62862188897956882779206837 5893330209183457760550641)
                  ·
                    refine ⟨4419997656887593320412981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5893330209183457760550641 4419997656887593320412981)
                    ·
                      refine ⟨414374780333211873788717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4419997656887593320412981 414374780333211873788717)
                      ·
                        rfl

theorem cell23_806992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_806992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_806992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_806992 prefixEnd_806992 := by exact prefixLift 806992
  have htrace : WordTrace (prefixWord ++ tailWord_806992) baseStart_806992 baseEnd_806992 := by
    simpa [prefixWord, tailWord_806992, baseEnd_806992] using wordTrace_append hprefix tailTrace_806992
  have hstable : (prefixWord ++ tailWord_806992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806992).length < 2 ^ (prefixWord ++ tailWord_806992).sum := by decide
  have hdescent : baseEnd_806992 < baseStart_806992 := by decide
  rcases family_descends (prefixWord ++ tailWord_806992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807056 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_807056 : Nat := 118140960795 + 807056 * 2 ^ 59
def prefixEnd_807056 : Nat := 4983230072969 + 3 ^ 40 * 807056 * 2
def baseEnd_807056 : Nat := 414407643095099623388423

theorem tailTrace_807056 : CollatzResearch.WordTrace tailWord_807056 prefixEnd_807056 414407643095099623388423 := by
  unfold tailWord_807056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14717875282090710518184511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19623833709454280690912681 14717875282090710518184511)
  ·
    refine ⟨22076812923136065777276767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14717875282090710518184511 22076812923136065777276767)
    ·
      refine ⟨33115219384704098665915151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22076812923136065777276767 33115219384704098665915151)
      ·
        refine ⟨49672829077056147998872727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33115219384704098665915151 49672829077056147998872727)
        ·
          refine ⟨74509243615584221998309091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49672829077056147998872727 74509243615584221998309091)
          ·
            refine ⟨111763865423376332997463637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74509243615584221998309091 111763865423376332997463637)
            ·
              refine ⟨1309732797930191402314027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 111763865423376332997463637 1309732797930191402314027)
              ·
                refine ⟨1964599196895287103471041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309732797930191402314027 1964599196895287103471041)
                ·
                  refine ⟨1473449397671465327603281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964599196895287103471041 1473449397671465327603281)
                  ·
                    refine ⟨1105087048253598995702461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473449397671465327603281 1105087048253598995702461)
                    ·
                      refine ⟨414407643095099623388423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1105087048253598995702461 414407643095099623388423)
                      ·
                        rfl

theorem cell23_807056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_807056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807056 prefixEnd_807056 := by exact prefixLift 807056
  have htrace : WordTrace (prefixWord ++ tailWord_807056) baseStart_807056 baseEnd_807056 := by
    simpa [prefixWord, tailWord_807056, baseEnd_807056] using wordTrace_append hprefix tailTrace_807056
  have hstable : (prefixWord ++ tailWord_807056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807056).length < 2 ^ (prefixWord ++ tailWord_807056).sum := by decide
  have hdescent : baseEnd_807056 < baseStart_807056 := by decide
  rcases family_descends (prefixWord ++ tailWord_807056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807096 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_807096 : Nat := 118140960795 + 807096 * 2 ^ 59
def prefixEnd_807096 : Nat := 4983230072969 + 3 ^ 40 * 807096 * 2
def baseEnd_807096 : Nat := 414428182321279466888239

theorem tailTrace_807096 : CollatzResearch.WordTrace tailWord_807096 prefixEnd_807096 414428182321279466888239 := by
  unfold tailWord_807096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718604742018253933912571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19624806322691005245216761 14718604742018253933912571)
  ·
    refine ⟨22077907113027380900868857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14718604742018253933912571 22077907113027380900868857)
    ·
      refine ⟨16558430334770535675651643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22077907113027380900868857 16558430334770535675651643)
      ·
        refine ⟨24837645502155803513477465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558430334770535675651643 24837645502155803513477465)
        ·
          refine ⟨18628234126616852635108099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24837645502155803513477465 18628234126616852635108099)
          ·
            refine ⟨27942351189925278952662149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628234126616852635108099 27942351189925278952662149)
            ·
              refine ⟨5239190848110989803624153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27942351189925278952662149 5239190848110989803624153)
              ·
                refine ⟨3929393136083242352718115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239190848110989803624153 3929393136083242352718115)
                ·
                  refine ⟨5894089704124863529077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929393136083242352718115 5894089704124863529077173)
                  ·
                    refine ⟨552570909761705955850985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5894089704124863529077173 552570909761705955850985)
                    ·
                      refine ⟨414428182321279466888239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552570909761705955850985 414428182321279466888239)
                      ·
                        rfl

theorem cell23_807096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_807096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807096 prefixEnd_807096 := by exact prefixLift 807096
  have htrace : WordTrace (prefixWord ++ tailWord_807096) baseStart_807096 baseEnd_807096 := by
    simpa [prefixWord, tailWord_807096, baseEnd_807096] using wordTrace_append hprefix tailTrace_807096
  have hstable : (prefixWord ++ tailWord_807096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807096).length < 2 ^ (prefixWord ++ tailWord_807096).sum := by decide
  have hdescent : baseEnd_807096 < baseStart_807096 := by decide
  rcases family_descends (prefixWord ++ tailWord_807096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807119 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 1, 6]
def baseStart_807119 : Nat := 118140960795 + 807119 * 2 ^ 59
def prefixEnd_807119 : Nat := 4983230072969 + 3 ^ 40 * 807119 * 2
def baseEnd_807119 : Nat := 138146664125444292300211

theorem tailTrace_807119 : CollatzResearch.WordTrace tailWord_807119 prefixEnd_807119 138146664125444292300211 := by
  unfold tailWord_807119
  simp only [CollatzResearch.WordTrace]
  refine ⟨29438048362953182795912411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19625365575302121863941607 29438048362953182795912411)
  ·
    refine ⟨44157072544429774193868617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29438048362953182795912411 44157072544429774193868617)
    ·
      refine ⟨33117804408322330645401463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44157072544429774193868617 33117804408322330645401463)
      ·
        refine ⟨49676706612483495968102195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33117804408322330645401463 49676706612483495968102195)
        ·
          refine ⟨74515059918725243952153293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49676706612483495968102195 74515059918725243952153293)
          ·
            refine ⟨27943147469521966482057485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74515059918725243952153293 27943147469521966482057485)
            ·
              refine ⟨10478680301070737430771557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27943147469521966482057485 10478680301070737430771557)
              ·
                refine ⟨1964752556450763268269667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10478680301070737430771557 1964752556450763268269667)
                ·
                  refine ⟨2947128834676144902404501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964752556450763268269667 2947128834676144902404501)
                  ·
                    refine ⟨138146664125444292300211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2947128834676144902404501 138146664125444292300211)
                    ·
                      rfl

theorem cell23_807119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_807119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807119 prefixEnd_807119 := by exact prefixLift 807119
  have htrace : WordTrace (prefixWord ++ tailWord_807119) baseStart_807119 baseEnd_807119 := by
    simpa [prefixWord, tailWord_807119, baseEnd_807119] using wordTrace_append hprefix tailTrace_807119
  have hstable : (prefixWord ++ tailWord_807119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807119).length < 2 ^ (prefixWord ++ tailWord_807119).sum := by decide
  have hdescent : baseEnd_807119 < baseStart_807119 := by decide
  rcases family_descends (prefixWord ++ tailWord_807119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807136 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_807136 : Nat := 118140960795 + 807136 * 2 ^ 59
def prefixEnd_807136 : Nat := 4983230072969 + 3 ^ 40 * 807136 * 2
def baseEnd_807136 : Nat := 138149573849153103462685

theorem tailTrace_807136 : CollatzResearch.WordTrace tailWord_807136 prefixEnd_807136 138149573849153103462685 := by
  unfold tailWord_807136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719334201945797349640631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19625778935927729799520841 14719334201945797349640631)
  ·
    refine ⟨22079001302918696024460947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14719334201945797349640631 22079001302918696024460947)
    ·
      refine ⟨33118501954378044036691421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22079001302918696024460947 33118501954378044036691421)
      ·
        refine ⟨12419438232891766513759283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33118501954378044036691421 12419438232891766513759283)
        ·
          refine ⟨18629157349337649770638925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419438232891766513759283 18629157349337649770638925)
          ·
            refine ⟨6985934006001618663989597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18629157349337649770638925 6985934006001618663989597)
            ·
              refine ⟨2619725252250606998996099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6985934006001618663989597 2619725252250606998996099)
              ·
                refine ⟨3929587878375910498494149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619725252250606998996099 3929587878375910498494149)
                ·
                  refine ⟨736797727195483218467653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3929587878375910498494149 736797727195483218467653)
                  ·
                    refine ⟨138149573849153103462685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736797727195483218467653 138149573849153103462685)
                    ·
                      rfl

theorem cell23_807136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_807136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807136 prefixEnd_807136 := by exact prefixLift 807136
  have htrace : WordTrace (prefixWord ++ tailWord_807136) baseStart_807136 baseEnd_807136 := by
    simpa [prefixWord, tailWord_807136, baseEnd_807136] using wordTrace_append hprefix tailTrace_807136
  have hstable : (prefixWord ++ tailWord_807136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807136).length < 2 ^ (prefixWord ++ tailWord_807136).sum := by decide
  have hdescent : baseEnd_807136 < baseStart_807136 := by decide
  rcases family_descends (prefixWord ++ tailWord_807136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807146 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_807146 : Nat := 118140960795 + 807146 * 2 ^ 59
def prefixEnd_807146 : Nat := 4983230072969 + 3 ^ 40 * 807146 * 2
def baseEnd_807146 : Nat := 414453856354004271263009

theorem tailTrace_807146 : CollatzResearch.WordTrace tailWord_807146 prefixEnd_807146 414453856354004271263009 := by
  unfold tailWord_807146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7359758283463841601786323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19626022089236910938096861 7359758283463841601786323)
  ·
    refine ⟨11039637425195762402679485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7359758283463841601786323 11039637425195762402679485)
    ·
      refine ⟨4139864034448410901004807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11039637425195762402679485 4139864034448410901004807)
      ·
        refine ⟨6209796051672616351507211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139864034448410901004807 6209796051672616351507211)
        ·
          refine ⟨9314694077508924527260817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209796051672616351507211 9314694077508924527260817)
          ·
            refine ⟨6986020558131693395445613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9314694077508924527260817 6986020558131693395445613)
            ·
              refine ⟨2619757709299385023292105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6986020558131693395445613 2619757709299385023292105)
              ·
                refine ⟨1964818281974538767469079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619757709299385023292105 1964818281974538767469079)
                ·
                  refine ⟨2947227422961808151203619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964818281974538767469079 2947227422961808151203619)
                  ·
                    refine ⟨4420841134442712226805429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947227422961808151203619 4420841134442712226805429)
                    ·
                      refine ⟨414453856354004271263009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4420841134442712226805429 414453856354004271263009)
                      ·
                        rfl

theorem cell23_807146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_807146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807146 prefixEnd_807146 := by exact prefixLift 807146
  have htrace : WordTrace (prefixWord ++ tailWord_807146) baseStart_807146 baseEnd_807146 := by
    simpa [prefixWord, tailWord_807146, baseEnd_807146] using wordTrace_append hprefix tailTrace_807146
  have hstable : (prefixWord ++ tailWord_807146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807146).length < 2 ^ (prefixWord ++ tailWord_807146).sum := by decide
  have hdescent : baseEnd_807146 < baseStart_807146 := by decide
  rcases family_descends (prefixWord ++ tailWord_807146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807166 : List Nat := [4, 2, 2, 1, 1, 1, 3, 9]
def baseStart_807166 : Nat := 118140960795 + 807166 * 2 ^ 59
def prefixEnd_807166 : Nat := 4983230072969 + 3 ^ 40 * 807166 * 2
def baseEnd_807166 : Nat := 15350523183966451593071

theorem tailTrace_807166 : CollatzResearch.WordTrace tailWord_807166 prefixEnd_807166 15350523183966451593071 := by
  unfold tailWord_807166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679970324222863727859169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19626508395855273215248901 3679970324222863727859169)
  ·
    refine ⟨2759977743167147795894377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3679970324222863727859169 2759977743167147795894377)
    ·
      refine ⟨2069983307375360846920783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2759977743167147795894377 2069983307375360846920783)
      ·
        refine ⟨3104974961063041270381175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069983307375360846920783 3104974961063041270381175)
        ·
          refine ⟨4657462441594561905571763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104974961063041270381175 4657462441594561905571763)
          ·
            refine ⟨6986193662391842858357645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657462441594561905571763 6986193662391842858357645)
            ·
              refine ⟨2619822623396941071884117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6986193662391842858357645 2619822623396941071884117)
              ·
                refine ⟨15350523183966451593071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2619822623396941071884117 15350523183966451593071)
                ·
                  rfl

theorem cell23_807166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_807166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807166 prefixEnd_807166 := by exact prefixLift 807166
  have htrace : WordTrace (prefixWord ++ tailWord_807166) baseStart_807166 baseEnd_807166 := by
    simpa [prefixWord, tailWord_807166, baseEnd_807166] using wordTrace_append hprefix tailTrace_807166
  have hstable : (prefixWord ++ tailWord_807166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807166).length < 2 ^ (prefixWord ++ tailWord_807166).sum := by decide
  have hdescent : baseEnd_807166 < baseStart_807166 := by decide
  rcases family_descends (prefixWord ++ tailWord_807166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807177 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 1, 2, 2]
def baseStart_807177 : Nat := 118140960795 + 807177 * 2 ^ 59
def prefixEnd_807177 : Nat := 4983230072969 + 3 ^ 40 * 807177 * 2
def baseEnd_807177 : Nat := 414469774254293649975367

theorem tailTrace_807177 : CollatzResearch.WordTrace tailWord_807177 prefixEnd_807177 414469774254293649975367 := by
  unfold tailWord_807177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440163796743058701523785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19626775864495372467682523 29440163796743058701523785)
  ·
    refine ⟨22080122847557294026142839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29440163796743058701523785 22080122847557294026142839)
    ·
      refine ⟨33120184271335941039214259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22080122847557294026142839 33120184271335941039214259)
      ·
        refine ⟨49680276407003911558821389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33120184271335941039214259 49680276407003911558821389)
        ·
          refine ⟨18630103652626466834558021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49680276407003911558821389 18630103652626466834558021)
          ·
            refine ⟨3493144434867462531479629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18630103652626466834558021 3493144434867462531479629)
            ·
              refine ⟨1309929163075298449304861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3493144434867462531479629 1309929163075298449304861)
              ·
                refine ⟨491223436153236918489323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309929163075298449304861 491223436153236918489323)
                ·
                  refine ⟨736835154229855377733985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491223436153236918489323 736835154229855377733985)
                  ·
                    refine ⟨552626365672391533300489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736835154229855377733985 552626365672391533300489)
                    ·
                      refine ⟨414469774254293649975367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552626365672391533300489 414469774254293649975367)
                      ·
                        rfl

theorem cell23_807177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 2, 2].length) (baseStart_807177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807177 prefixEnd_807177 := by exact prefixLift 807177
  have htrace : WordTrace (prefixWord ++ tailWord_807177) baseStart_807177 baseEnd_807177 := by
    simpa [prefixWord, tailWord_807177, baseEnd_807177] using wordTrace_append hprefix tailTrace_807177
  have hstable : (prefixWord ++ tailWord_807177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807177).length < 2 ^ (prefixWord ++ tailWord_807177).sum := by decide
  have hdescent : baseEnd_807177 < baseStart_807177 := by decide
  rcases family_descends (prefixWord ++ tailWord_807177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807194 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_807194 : Nat := 118140960795 + 807194 * 2 ^ 59
def prefixEnd_807194 : Nat := 4983230072969 + 3 ^ 40 * 807194 * 2
def baseEnd_807194 : Nat := 414478503425420083462789

theorem tailTrace_807194 : CollatzResearch.WordTrace tailWord_807194 prefixEnd_807194 414478503425420083462789 := by
  unfold tailWord_807194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360195959420367651223159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19627189225120980403261757 7360195959420367651223159)
  ·
    refine ⟨11040293939130551476834739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360195959420367651223159 11040293939130551476834739)
    ·
      refine ⟨16560440908695827215252109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040293939130551476834739 16560440908695827215252109)
      ·
        refine ⟨6210165340760935205719541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16560440908695827215252109 6210165340760935205719541)
        ·
          refine ⟨582203000696337675536207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6210165340760935205719541 582203000696337675536207)
          ·
            refine ⟨873304501044506513304311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582203000696337675536207 873304501044506513304311)
            ·
              refine ⟨1309956751566759769956467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873304501044506513304311 1309956751566759769956467)
              ·
                refine ⟨1964935127350139654934701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309956751566759769956467 1964935127350139654934701)
                ·
                  refine ⟨736850672756302370600513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1964935127350139654934701 736850672756302370600513)
                  ·
                    refine ⟨552638004567226777950385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736850672756302370600513 552638004567226777950385)
                    ·
                      refine ⟨414478503425420083462789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552638004567226777950385 414478503425420083462789)
                      ·
                        rfl

theorem cell23_807194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_807194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807194 prefixEnd_807194 := by exact prefixLift 807194
  have htrace : WordTrace (prefixWord ++ tailWord_807194) baseStart_807194 baseEnd_807194 := by
    simpa [prefixWord, tailWord_807194, baseEnd_807194] using wordTrace_append hprefix tailTrace_807194
  have hstable : (prefixWord ++ tailWord_807194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807194).length < 2 ^ (prefixWord ++ tailWord_807194).sum := by decide
  have hdescent : baseEnd_807194 < baseStart_807194 := by decide
  rcases family_descends (prefixWord ++ tailWord_807194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807203 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 3, 3, 2]
def baseStart_807203 : Nat := 118140960795 + 807203 * 2 ^ 59
def prefixEnd_807203 : Nat := 4983230072969 + 3 ^ 40 * 807203 * 2
def baseEnd_807203 : Nat := 414483124751310548250247

theorem tailTrace_807203 : CollatzResearch.WordTrace tailWord_807203 prefixEnd_807203 414483124751310548250247 := by
  unfold tailWord_807203
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441112094648865141970263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19627408063099243427980175 29441112094648865141970263)
  ·
    refine ⟨44161668141973297712955395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29441112094648865141970263 44161668141973297712955395)
    ·
      refine ⟨66242502212959946569433093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44161668141973297712955395 66242502212959946569433093)
      ·
        refine ⟨12420469164929989981768705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66242502212959946569433093 12420469164929989981768705)
        ·
          refine ⟨9315351873697492486326529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12420469164929989981768705 9315351873697492486326529)
          ·
            refine ⟨6986513905273119364744897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9315351873697492486326529 6986513905273119364744897)
            ·
              refine ⟨5239885428954839523558673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6986513905273119364744897 5239885428954839523558673)
              ·
                refine ⟨3929914071716129642669005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239885428954839523558673 3929914071716129642669005)
                ·
                  refine ⟨1473717776893548616000877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3929914071716129642669005 1473717776893548616000877)
                  ·
                    refine ⟨552644166335080731000329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1473717776893548616000877 552644166335080731000329)
                    ·
                      refine ⟨414483124751310548250247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552644166335080731000329 414483124751310548250247)
                      ·
                        rfl

theorem cell23_807203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_807203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807203 prefixEnd_807203 := by exact prefixLift 807203
  have htrace : WordTrace (prefixWord ++ tailWord_807203) baseStart_807203 baseEnd_807203 := by
    simpa [prefixWord, tailWord_807203, baseEnd_807203] using wordTrace_append hprefix tailTrace_807203
  have hstable : (prefixWord ++ tailWord_807203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807203).length < 2 ^ (prefixWord ++ tailWord_807203).sum := by decide
  have hdescent : baseEnd_807203 < baseStart_807203 := by decide
  rcases family_descends (prefixWord ++ tailWord_807203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807214 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_807214 : Nat := 118140960795 + 807214 * 2 ^ 59
def prefixEnd_807214 : Nat := 4983230072969 + 3 ^ 40 * 807214 * 2
def baseEnd_807214 : Nat := 414488773038510005212697

theorem tailTrace_807214 : CollatzResearch.WordTrace tailWord_807214 prefixEnd_807214 414488773038510005212697 := by
  unfold tailWord_807214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680189162201126752577587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19627675531739342680413797 3680189162201126752577587)
  ·
    refine ⟨5520283743301690128866381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680189162201126752577587 5520283743301690128866381)
    ·
      refine ⟨2070106403738133798324893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5520283743301690128866381 2070106403738133798324893)
      ·
        refine ⟨776289901401800174371835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2070106403738133798324893 776289901401800174371835)
        ·
          refine ⟨1164434852102700261557753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776289901401800174371835 1164434852102700261557753)
          ·
            refine ⟨873326139077025196168315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164434852102700261557753 873326139077025196168315)
            ·
              refine ⟨1309989208615537794252473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873326139077025196168315 1309989208615537794252473)
              ·
                refine ⟨982491906461653345689355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309989208615537794252473 982491906461653345689355)
                ·
                  refine ⟨1473737859692480018534033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982491906461653345689355 1473737859692480018534033)
                  ·
                    refine ⟨1105303394769360013900525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473737859692480018534033 1105303394769360013900525)
                    ·
                      refine ⟨414488773038510005212697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1105303394769360013900525 414488773038510005212697)
                      ·
                        rfl

theorem cell23_807214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_807214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807214 prefixEnd_807214 := by exact prefixLift 807214
  have htrace : WordTrace (prefixWord ++ tailWord_807214) baseStart_807214 baseEnd_807214 := by
    simpa [prefixWord, tailWord_807214, baseEnd_807214] using wordTrace_append hprefix tailTrace_807214
  have hstable : (prefixWord ++ tailWord_807214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807214).length < 2 ^ (prefixWord ++ tailWord_807214).sum := by decide
  have hdescent : baseEnd_807214 < baseStart_807214 := by decide
  rcases family_descends (prefixWord ++ tailWord_807214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807250 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_807250 : Nat := 118140960795 + 807250 * 2 ^ 59
def prefixEnd_807250 : Nat := 4983230072969 + 3 ^ 40 * 807250 * 2
def baseEnd_807250 : Nat := 414507258342071864362531

theorem tailTrace_807250 : CollatzResearch.WordTrace tailWord_807250 prefixEnd_807250 414507258342071864362531 := by
  unfold tailWord_807250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360706581369648042232801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19628550883652394779287469 7360706581369648042232801)
  ·
    refine ⟨5520529936027236031674601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7360706581369648042232801 5520529936027236031674601)
    ·
      refine ⟨4140397452020427023755951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5520529936027236031674601 4140397452020427023755951)
      ·
        refine ⟨6210596178030640535633927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140397452020427023755951 6210596178030640535633927)
        ·
          refine ⟨9315894267045960803450891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210596178030640535633927 9315894267045960803450891)
          ·
            refine ⟨13973841400568941205176337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315894267045960803450891 13973841400568941205176337)
            ·
              refine ⟨10480381050426705903882253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973841400568941205176337 10480381050426705903882253)
              ·
                refine ⟨3930142893910014713955845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10480381050426705903882253 3930142893910014713955845)
                ·
                  refine ⟨736901792608127758866721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3930142893910014713955845 736901792608127758866721)
                  ·
                    refine ⟨552676344456095819150041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736901792608127758866721 552676344456095819150041)
                    ·
                      refine ⟨414507258342071864362531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552676344456095819150041 414507258342071864362531)
                      ·
                        rfl

theorem cell23_807250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_807250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807250 prefixEnd_807250 := by exact prefixLift 807250
  have htrace : WordTrace (prefixWord ++ tailWord_807250) baseStart_807250 baseEnd_807250 := by
    simpa [prefixWord, tailWord_807250, baseEnd_807250] using wordTrace_append hprefix tailTrace_807250
  have hstable : (prefixWord ++ tailWord_807250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807250).length < 2 ^ (prefixWord ++ tailWord_807250).sum := by decide
  have hdescent : baseEnd_807250 < baseStart_807250 := by decide
  rcases family_descends (prefixWord ++ tailWord_807250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807260 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_807260 : Nat := 118140960795 + 807260 * 2 ^ 59
def prefixEnd_807260 : Nat := 4983230072969 + 3 ^ 40 * 807260 * 2
def baseEnd_807260 : Nat := 138170797716205608412495

theorem tailTrace_807260 : CollatzResearch.WordTrace tailWord_807260 prefixEnd_807260 138170797716205608412495 := by
  unfold tailWord_807260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721595527721181938397617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19628794036961575917863489 14721595527721181938397617)
  ·
    refine ⟨11041196645790886453798213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14721595527721181938397617 11041196645790886453798213)
    ·
      refine ⟨2070224371085791210087165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11041196645790886453798213 2070224371085791210087165)
      ·
        refine ⟨776334139157171703782687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2070224371085791210087165 776334139157171703782687)
        ·
          refine ⟨1164501208735757555674031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776334139157171703782687 1164501208735757555674031)
          ·
            refine ⟨1746751813103636333511047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164501208735757555674031 1746751813103636333511047)
            ·
              refine ⟨2620127719655454500266571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746751813103636333511047 2620127719655454500266571)
              ·
                refine ⟨3930191579483181750399857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620127719655454500266571 3930191579483181750399857)
                ·
                  refine ⟨2947643684612386312799893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3930191579483181750399857 2947643684612386312799893)
                  ·
                    refine ⟨138170797716205608412495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2947643684612386312799893 138170797716205608412495)
                    ·
                      rfl

theorem cell23_807260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_807260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807260 prefixEnd_807260 := by exact prefixLift 807260
  have htrace : WordTrace (prefixWord ++ tailWord_807260) baseStart_807260 baseEnd_807260 := by
    simpa [prefixWord, tailWord_807260, baseEnd_807260] using wordTrace_append hprefix tailTrace_807260
  have hstable : (prefixWord ++ tailWord_807260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807260).length < 2 ^ (prefixWord ++ tailWord_807260).sum := by decide
  have hdescent : baseEnd_807260 < baseStart_807260 := by decide
  rcases family_descends (prefixWord ++ tailWord_807260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807318 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_807318 : Nat := 118140960795 + 807318 * 2 ^ 59
def prefixEnd_807318 : Nat := 4983230072969 + 3 ^ 40 * 807318 * 2
def baseEnd_807318 : Nat := 414542175026577598312219

theorem tailTrace_807318 : CollatzResearch.WordTrace tailWord_807318 prefixEnd_807318 414542175026577598312219 := by
  unfold tailWord_807318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840331655577014986400413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19630204326154826521604405 1840331655577014986400413)
  ·
    refine ⟨690124370841380619900155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1840331655577014986400413 690124370841380619900155)
    ·
      refine ⟨1035186556262070929850233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690124370841380619900155 1035186556262070929850233)
      ·
        refine ⟨776389917196553197387675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035186556262070929850233 776389917196553197387675)
        ·
          refine ⟨1164584875794829796081513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776389917196553197387675 1164584875794829796081513)
          ·
            refine ⟨873438656846122347061135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164584875794829796081513 873438656846122347061135)
            ·
              refine ⟨1310157985269183520591703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873438656846122347061135 1310157985269183520591703)
              ·
                refine ⟨1965236977903775280887555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310157985269183520591703 1965236977903775280887555)
                ·
                  refine ⟨2947855466855662921331333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965236977903775280887555 2947855466855662921331333)
                  ·
                    refine ⟨552722900035436797749625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947855466855662921331333 552722900035436797749625)
                    ·
                      refine ⟨414542175026577598312219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 552722900035436797749625 414542175026577598312219)
                      ·
                        rfl

theorem cell23_807318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_807318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807318 prefixEnd_807318 := by exact prefixLift 807318
  have htrace : WordTrace (prefixWord ++ tailWord_807318) baseStart_807318 baseEnd_807318 := by
    simpa [prefixWord, tailWord_807318, baseEnd_807318] using wordTrace_append hprefix tailTrace_807318
  have hstable : (prefixWord ++ tailWord_807318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807318).length < 2 ^ (prefixWord ++ tailWord_807318).sum := by decide
  have hdescent : baseEnd_807318 < baseStart_807318 := by decide
  rcases family_descends (prefixWord ++ tailWord_807318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807333 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_807333 : Nat := 118140960795 + 807333 * 2 ^ 59
def prefixEnd_807333 : Nat := 4983230072969 + 3 ^ 40 * 807333 * 2
def baseEnd_807333 : Nat := 138183292412131679874883

theorem tailTrace_807333 : CollatzResearch.WordTrace tailWord_807333 prefixEnd_807333 138183292412131679874883 := by
  unfold tailWord_807333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29445853584177897344202653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19630569056118598229468435 29445853584177897344202653)
  ·
    refine ⟨11042195094066711504075995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29445853584177897344202653 11042195094066711504075995)
    ·
      refine ⟨16563292641100067256113993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11042195094066711504075995 16563292641100067256113993)
      ·
        refine ⟨12422469480825050442085495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16563292641100067256113993 12422469480825050442085495)
        ·
          refine ⟨18633704221237575663128243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12422469480825050442085495 18633704221237575663128243)
          ·
            refine ⟨27950556331856363494692365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18633704221237575663128243 27950556331856363494692365)
            ·
              refine ⟨10481458624446136310509637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27950556331856363494692365 10481458624446136310509637)
              ·
                refine ⟨1965273492083650558220557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10481458624446136310509637 1965273492083650558220557)
                ·
                  refine ⟨736977559531368959332709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1965273492083650558220557 736977559531368959332709)
                  ·
                    refine ⟨138183292412131679874883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736977559531368959332709 138183292412131679874883)
                    ·
                      rfl

theorem cell23_807333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_807333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807333 prefixEnd_807333 := by exact prefixLift 807333
  have htrace : WordTrace (prefixWord ++ tailWord_807333) baseStart_807333 baseEnd_807333 := by
    simpa [prefixWord, tailWord_807333, baseEnd_807333] using wordTrace_append hprefix tailTrace_807333
  have hstable : (prefixWord ++ tailWord_807333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807333).length < 2 ^ (prefixWord ++ tailWord_807333).sum := by decide
  have hdescent : baseEnd_807333 < baseStart_807333 := by decide
  rcases family_descends (prefixWord ++ tailWord_807333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807346 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_807346 : Nat := 118140960795 + 807346 * 2 ^ 59
def prefixEnd_807346 : Nat := 4983230072969 + 3 ^ 40 * 807346 * 2
def baseEnd_807346 : Nat := 46061839164989276529121

theorem tailTrace_807346 : CollatzResearch.WordTrace tailWord_807346 prefixEnd_807346 46061839164989276529121 := by
  unfold tailWord_807346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361581933282700141106473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19630885155420533709617261 7361581933282700141106473)
  ·
    refine ⟨5521186449962025105829855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7361581933282700141106473 5521186449962025105829855)
    ·
      refine ⟨8281779674943037658744783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521186449962025105829855 8281779674943037658744783)
      ·
        refine ⟨12422669512414556488117175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8281779674943037658744783 12422669512414556488117175)
        ·
          refine ⟨18634004268621834732175763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12422669512414556488117175 18634004268621834732175763)
          ·
            refine ⟨27951006402932752098263645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18634004268621834732175763 27951006402932752098263645)
            ·
              refine ⟨10481627401099782036848867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27951006402932752098263645 10481627401099782036848867)
              ·
                refine ⟨15722441101649673055273301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10481627401099782036848867 15722441101649673055273301)
                ·
                  refine ⟨46061839164989276529121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15722441101649673055273301 46061839164989276529121)
                  ·
                    rfl

theorem cell23_807346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_807346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807346 prefixEnd_807346 := by exact prefixLift 807346
  have htrace : WordTrace (prefixWord ++ tailWord_807346) baseStart_807346 baseEnd_807346 := by
    simpa [prefixWord, tailWord_807346, baseEnd_807346] using wordTrace_append hprefix tailTrace_807346
  have hstable : (prefixWord ++ tailWord_807346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807346).length < 2 ^ (prefixWord ++ tailWord_807346).sum := by decide
  have hdescent : baseEnd_807346 < baseStart_807346 := by decide
  rcases family_descends (prefixWord ++ tailWord_807346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807380 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 6]
def baseStart_807380 : Nat := 118140960795 + 807380 * 2 ^ 59
def prefixEnd_807380 : Nat := 4983230072969 + 3 ^ 40 * 807380 * 2
def baseEnd_807380 : Nat := 46063778980795150637437

theorem tailTrace_807380 : CollatzResearch.WordTrace tailWord_807380 prefixEnd_807380 46063778980795150637437 := by
  unfold tailWord_807380
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723783907503812185581797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19631711876671749580775729 14723783907503812185581797)
  ·
    refine ⟨2760709482656964784796587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14723783907503812185581797 2760709482656964784796587)
    ·
      refine ⟨4141064223985447177194881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760709482656964784796587 4141064223985447177194881)
      ·
        refine ⟨3105798167989085382896161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4141064223985447177194881 3105798167989085382896161)
        ·
          refine ⟨2329348625991814037172121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3105798167989085382896161 2329348625991814037172121)
          ·
            refine ⟨1747011469493860527879091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329348625991814037172121 1747011469493860527879091)
            ·
              refine ⟨2620517204240790791818637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747011469493860527879091 2620517204240790791818637)
              ·
                refine ⟨982693951590296546931989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2620517204240790791818637 982693951590296546931989)
                ·
                  refine ⟨46063778980795150637437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 982693951590296546931989 46063778980795150637437)
                  ·
                    rfl

theorem cell23_807380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_807380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807380 prefixEnd_807380 := by exact prefixLift 807380
  have htrace : WordTrace (prefixWord ++ tailWord_807380) baseStart_807380 baseEnd_807380 := by
    simpa [prefixWord, tailWord_807380, baseEnd_807380] using wordTrace_append hprefix tailTrace_807380
  have hstable : (prefixWord ++ tailWord_807380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807380).length < 2 ^ (prefixWord ++ tailWord_807380).sum := by decide
  have hdescent : baseEnd_807380 < baseStart_807380 := by decide
  rcases family_descends (prefixWord ++ tailWord_807380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807393 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_807393 : Nat := 118140960795 + 807393 * 2 ^ 59
def prefixEnd_807393 : Nat := 4983230072969 + 3 ^ 40 * 807393 * 2
def baseEnd_807393 : Nat := 138193562025221601624791

theorem tailTrace_807393 : CollatzResearch.WordTrace tailWord_807393 prefixEnd_807393 138193562025221601624791 := by
  unfold tailWord_807393
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448041963960527591386833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19632027975973685060924555 29448041963960527591386833)
  ·
    refine ⟨22086031472970395693540125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29448041963960527591386833 22086031472970395693540125)
    ·
      refine ⟨8282261802363898385077547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22086031472970395693540125 8282261802363898385077547)
      ·
        refine ⟨12423392703545847577616321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282261802363898385077547 12423392703545847577616321)
        ·
          refine ⟨9317544527659385683212241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12423392703545847577616321 9317544527659385683212241)
          ·
            refine ⟨6988158395744539262409181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9317544527659385683212241 6988158395744539262409181)
            ·
              refine ⟨2620559398404202223403443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988158395744539262409181 2620559398404202223403443)
              ·
                refine ⟨3930839097606303335105165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620559398404202223403443 3930839097606303335105165)
                ·
                  refine ⟨1474064661602363750664437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3930839097606303335105165 1474064661602363750664437)
                  ·
                    refine ⟨138193562025221601624791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1474064661602363750664437 138193562025221601624791)
                    ·
                      rfl

theorem cell23_807393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_807393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807393 prefixEnd_807393 := by exact prefixLift 807393
  have htrace : WordTrace (prefixWord ++ tailWord_807393) baseStart_807393 baseEnd_807393 := by
    simpa [prefixWord, tailWord_807393, baseEnd_807393] using wordTrace_append hprefix tailTrace_807393
  have hstable : (prefixWord ++ tailWord_807393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807393).length < 2 ^ (prefixWord ++ tailWord_807393).sum := by decide
  have hdescent : baseEnd_807393 < baseStart_807393 := by decide
  rcases family_descends (prefixWord ++ tailWord_807393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807407 : List Nat := [1, 1, 2, 1, 4, 1, 1, 7, 1, 1, 3]
def baseStart_807407 : Nat := 118140960795 + 807407 * 2 ^ 59
def prefixEnd_807407 : Nat := 4983230072969 + 3 ^ 40 * 807407 * 2
def baseEnd_807407 : Nat := 414587874804827750099309

theorem tailTrace_807407 : CollatzResearch.WordTrace tailWord_807407 prefixEnd_807407 414587874804827750099309 := by
  unfold tailWord_807407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448552585909807982396475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19632368390606538654930983 29448552585909807982396475)
  ·
    refine ⟨44172828878864711973594713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29448552585909807982396475 44172828878864711973594713)
    ·
      refine ⟨33129621659148533980196035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44172828878864711973594713 33129621659148533980196035)
      ·
        refine ⟨49694432488722800970294053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33129621659148533980196035 49694432488722800970294053)
        ·
          refine ⟨9317706091635525181930135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49694432488722800970294053 9317706091635525181930135)
          ·
            refine ⟨13976559137453287772895203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9317706091635525181930135 13976559137453287772895203)
            ·
              refine ⟨20964838706179931659342805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13976559137453287772895203 20964838706179931659342805)
              ·
                refine ⟨491363407176092148265847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20964838706179931659342805 491363407176092148265847)
                ·
                  refine ⟨737045110764138222398771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491363407176092148265847 737045110764138222398771)
                  ·
                    refine ⟨1105567666146207333598157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737045110764138222398771 1105567666146207333598157)
                    ·
                      refine ⟨414587874804827750099309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1105567666146207333598157 414587874804827750099309)
                      ·
                        rfl

theorem cell23_807407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 1, 3].length) (baseStart_807407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807407 prefixEnd_807407 := by exact prefixLift 807407
  have htrace : WordTrace (prefixWord ++ tailWord_807407) baseStart_807407 baseEnd_807407 := by
    simpa [prefixWord, tailWord_807407, baseEnd_807407] using wordTrace_append hprefix tailTrace_807407
  have hstable : (prefixWord ++ tailWord_807407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807407).length < 2 ^ (prefixWord ++ tailWord_807407).sum := by decide
  have hdescent : baseEnd_807407 < baseStart_807407 := by decide
  rcases family_descends (prefixWord ++ tailWord_807407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807450 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_807450 : Nat := 118140960795 + 807450 * 2 ^ 59
def prefixEnd_807450 : Nat := 4983230072969 + 3 ^ 40 * 807450 * 2
def baseEnd_807450 : Nat := 414609954472971081861611

theorem tailTrace_807450 : CollatzResearch.WordTrace tailWord_807450 prefixEnd_807450 414609954472971081861611 := by
  unfold tailWord_807450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362530231188506581552951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19633413949836017550807869 7362530231188506581552951)
  ·
    refine ⟨11043795346782759872329427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7362530231188506581552951 11043795346782759872329427)
    ·
      refine ⟨16565693020174139808494141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043795346782759872329427 16565693020174139808494141)
      ·
        refine ⟨6212134882565302428185303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16565693020174139808494141 6212134882565302428185303)
        ·
          refine ⟨9318202323847953642277955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212134882565302428185303 9318202323847953642277955)
          ·
            refine ⟨13977303485771930463416933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318202323847953642277955 13977303485771930463416933)
            ·
              refine ⟨2620744403582236961890675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13977303485771930463416933 2620744403582236961890675)
              ·
                refine ⟨3931116605373355442836013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620744403582236961890675 3931116605373355442836013)
                ·
                  refine ⟨1474168727015008291063505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3931116605373355442836013 1474168727015008291063505)
                  ·
                    refine ⟨1105626545261256218297629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1474168727015008291063505 1105626545261256218297629)
                    ·
                      refine ⟨414609954472971081861611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1105626545261256218297629 414609954472971081861611)
                      ·
                        rfl

theorem cell23_807450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_807450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807450 prefixEnd_807450 := by exact prefixLift 807450
  have htrace : WordTrace (prefixWord ++ tailWord_807450) baseStart_807450 baseEnd_807450 := by
    simpa [prefixWord, tailWord_807450, baseEnd_807450] using wordTrace_append hprefix tailTrace_807450
  have hstable : (prefixWord ++ tailWord_807450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807450).length < 2 ^ (prefixWord ++ tailWord_807450).sum := by decide
  have hdescent : baseEnd_807450 < baseStart_807450 := by decide
  rcases family_descends (prefixWord ++ tailWord_807450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807464 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_807464 : Nat := 118140960795 + 807464 * 2 ^ 59
def prefixEnd_807464 : Nat := 4983230072969 + 3 ^ 40 * 807464 * 2
def baseEnd_807464 : Nat := 414617143202134027086547

theorem tailTrace_807464 : CollatzResearch.WordTrace tailWord_807464 prefixEnd_807464 414617143202134027086547 := by
  unfold tailWord_807464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725315773351653358610723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19633754364468871144814297 14725315773351653358610723)
  ·
    refine ⟨22087973660027480037916085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725315773351653358610723 22087973660027480037916085)
    ·
      refine ⟨2070747530627576253554633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22087973660027480037916085 2070747530627576253554633)
      ·
        refine ⟨1553060647970682190165975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070747530627576253554633 1553060647970682190165975)
        ·
          refine ⟨2329590971956023285248963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553060647970682190165975 2329590971956023285248963)
          ·
            refine ⟨3494386457934034927873445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329590971956023285248963 3494386457934034927873445)
            ·
              refine ⟨655197460862631548976271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3494386457934034927873445 655197460862631548976271)
              ·
                refine ⟨982796191293947323464407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655197460862631548976271 982796191293947323464407)
                ·
                  refine ⟨1474194286940920985196611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982796191293947323464407 1474194286940920985196611)
                  ·
                    refine ⟨2211291430411381477794917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474194286940920985196611 2211291430411381477794917)
                    ·
                      refine ⟨414617143202134027086547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2211291430411381477794917 414617143202134027086547)
                      ·
                        rfl

theorem cell23_807464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_807464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807464 prefixEnd_807464 := by exact prefixLift 807464
  have htrace : WordTrace (prefixWord ++ tailWord_807464) baseStart_807464 baseEnd_807464 := by
    simpa [prefixWord, tailWord_807464, baseEnd_807464] using wordTrace_append hprefix tailTrace_807464
  have hstable : (prefixWord ++ tailWord_807464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807464).length < 2 ^ (prefixWord ++ tailWord_807464).sum := by decide
  have hdescent : baseEnd_807464 < baseStart_807464 := by decide
  rcases family_descends (prefixWord ++ tailWord_807464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807470 : List Nat := [4, 1, 3, 1, 3, 1, 10]
def baseStart_807470 : Nat := 118140960795 + 807470 * 2 ^ 59
def prefixEnd_807470 : Nat := 4983230072969 + 3 ^ 40 * 807470 * 2
def baseEnd_807470 : Nat := 5118768198593345723599

theorem tailTrace_807470 : CollatzResearch.WordTrace tailWord_807470 prefixEnd_807470 5118768198593345723599 := by
  unfold tailWord_807470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681356298085196217742483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19633900256454379827959909 3681356298085196217742483)
  ·
    refine ⟨5522034447127794326613725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3681356298085196217742483 5522034447127794326613725)
    ·
      refine ⟨2070762917672922872480147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5522034447127794326613725 2070762917672922872480147)
      ·
        refine ⟨3106144376509384308720221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070762917672922872480147 3106144376509384308720221)
        ·
          refine ⟨1164804141191019115770083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3106144376509384308720221 1164804141191019115770083)
          ·
            refine ⟨1747206211786528673655125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164804141191019115770083 1747206211786528673655125)
            ·
              refine ⟨5118768198593345723599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1747206211786528673655125 5118768198593345723599)
              ·
                rfl

theorem cell23_807470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 10].length) (baseStart_807470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807470 prefixEnd_807470 := by exact prefixLift 807470
  have htrace : WordTrace (prefixWord ++ tailWord_807470) baseStart_807470 baseEnd_807470 := by
    simpa [prefixWord, tailWord_807470, baseEnd_807470] using wordTrace_append hprefix tailTrace_807470
  have hstable : (prefixWord ++ tailWord_807470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807470).length < 2 ^ (prefixWord ++ tailWord_807470).sum := by decide
  have hdescent : baseEnd_807470 < baseStart_807470 := by decide
  rcases family_descends (prefixWord ++ tailWord_807470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807494 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_807494 : Nat := 118140960795 + 807494 * 2 ^ 59
def prefixEnd_807494 : Nat := 4983230072969 + 3 ^ 40 * 807494 * 2
def baseEnd_807494 : Nat := 414632547621768909711409

theorem tailTrace_807494 : CollatzResearch.WordTrace tailWord_807494 prefixEnd_807494 414632547621768909711409 := by
  unfold tailWord_807494
  simp only [CollatzResearch.WordTrace]
  refine ⟨920366429268581932525423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19634483824396414560542357 920366429268581932525423)
  ·
    refine ⟨1380549643902872898788135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920366429268581932525423 1380549643902872898788135)
    ·
      refine ⟨2070824465854309348182203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380549643902872898788135 2070824465854309348182203)
      ·
        refine ⟨3106236698781464022273305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070824465854309348182203 3106236698781464022273305)
        ·
          refine ⟨2329677524086098016704979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3106236698781464022273305 2329677524086098016704979)
          ·
            refine ⟨3494516286129147025057469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329677524086098016704979 3494516286129147025057469)
            ·
              refine ⟨1310443607298430134396551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3494516286129147025057469 1310443607298430134396551)
              ·
                refine ⟨1965665410947645201594827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310443607298430134396551 1965665410947645201594827)
                ·
                  refine ⟨2948498116421467802392241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965665410947645201594827 2948498116421467802392241)
                  ·
                    refine ⟨2211373587316100851794181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2948498116421467802392241 2211373587316100851794181)
                    ·
                      refine ⟨414632547621768909711409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2211373587316100851794181 414632547621768909711409)
                      ·
                        rfl

theorem cell23_807494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_807494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807494 prefixEnd_807494 := by exact prefixLift 807494
  have htrace : WordTrace (prefixWord ++ tailWord_807494) baseStart_807494 baseEnd_807494 := by
    simpa [prefixWord, tailWord_807494, baseEnd_807494] using wordTrace_append hprefix tailTrace_807494
  have hstable : (prefixWord ++ tailWord_807494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807494).length < 2 ^ (prefixWord ++ tailWord_807494).sum := by decide
  have hdescent : baseEnd_807494 < baseStart_807494 := by decide
  rcases family_descends (prefixWord ++ tailWord_807494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807503 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_807503 : Nat := 118140960795 + 807503 * 2 ^ 59
def prefixEnd_807503 : Nat := 4983230072969 + 3 ^ 40 * 807503 * 2
def baseEnd_807503 : Nat := 414637168947659374498867

theorem tailTrace_807503 : CollatzResearch.WordTrace tailWord_807503 prefixEnd_807503 414637168947659374498867 := by
  unfold tailWord_807503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29452053993562016377891163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19634702662374677585260775 29452053993562016377891163)
  ·
    refine ⟨44178080990343024566836745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29452053993562016377891163 44178080990343024566836745)
    ·
      refine ⟨33133560742757268425127559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44178080990343024566836745 33133560742757268425127559)
      ·
        refine ⟨49700341114135902637691339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33133560742757268425127559 49700341114135902637691339)
        ·
          refine ⟨74550511671203853956537009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49700341114135902637691339 74550511671203853956537009)
          ·
            refine ⟨55912883753402890467402757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74550511671203853956537009 55912883753402890467402757)
            ·
              refine ⟨10483665703763041962638017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55912883753402890467402757 10483665703763041962638017)
              ·
                refine ⟨7862749277822281471978513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10483665703763041962638017 7862749277822281471978513)
                ·
                  refine ⟨5897061958366711103983885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862749277822281471978513 5897061958366711103983885)
                  ·
                    refine ⟨2211398234387516663993957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5897061958366711103983885 2211398234387516663993957)
                    ·
                      refine ⟨414637168947659374498867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2211398234387516663993957 414637168947659374498867)
                      ·
                        rfl

theorem cell23_807503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_807503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807503 prefixEnd_807503 := by exact prefixLift 807503
  have htrace : WordTrace (prefixWord ++ tailWord_807503) baseStart_807503 baseEnd_807503 := by
    simpa [prefixWord, tailWord_807503, baseEnd_807503] using wordTrace_append hprefix tailTrace_807503
  have hstable : (prefixWord ++ tailWord_807503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807503).length < 2 ^ (prefixWord ++ tailWord_807503).sum := by decide
  have hdescent : baseEnd_807503 < baseStart_807503 := by decide
  rcases family_descends (prefixWord ++ tailWord_807503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807610 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_807610 : Nat := 118140960795 + 807610 * 2 ^ 59
def prefixEnd_807610 : Nat := 4983230072969 + 3 ^ 40 * 807610 * 2
def baseEnd_807610 : Nat := 414692111377690455860875

theorem tailTrace_807610 : CollatzResearch.WordTrace tailWord_807610 prefixEnd_807610 414692111377690455860875 := by
  unfold tailWord_807610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363989151043593413009071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19637304402782915768024189 7363989151043593413009071)
  ·
    refine ⟨11045983726565390119513607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7363989151043593413009071 11045983726565390119513607)
    ·
      refine ⟨16568975589848085179270411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11045983726565390119513607 16568975589848085179270411)
      ·
        refine ⟨24853463384772127768905617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16568975589848085179270411 24853463384772127768905617)
        ·
          refine ⟨18640097538579095826679213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24853463384772127768905617 18640097538579095826679213)
          ·
            refine ⟨6990036576967160935004705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18640097538579095826679213 6990036576967160935004705)
            ·
              refine ⟨5242527432725370701253529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6990036576967160935004705 5242527432725370701253529)
              ·
                refine ⟨3931895574544028025940147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242527432725370701253529 3931895574544028025940147)
                ·
                  refine ⟨5897843361816042038910221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931895574544028025940147 5897843361816042038910221)
                  ·
                    refine ⟨2211691260681015764591333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5897843361816042038910221 2211691260681015764591333)
                    ·
                      refine ⟨414692111377690455860875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2211691260681015764591333 414692111377690455860875)
                      ·
                        rfl

theorem cell23_807610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_807610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807610 prefixEnd_807610 := by exact prefixLift 807610
  have htrace : WordTrace (prefixWord ++ tailWord_807610) baseStart_807610 baseEnd_807610 := by
    simpa [prefixWord, tailWord_807610, baseEnd_807610] using wordTrace_append hprefix tailTrace_807610
  have hstable : (prefixWord ++ tailWord_807610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807610).length < 2 ^ (prefixWord ++ tailWord_807610).sum := by decide
  have hdescent : baseEnd_807610 < baseStart_807610 := by decide
  rcases family_descends (prefixWord ++ tailWord_807610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807640 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_807640 : Nat := 118140960795 + 807640 * 2 ^ 59
def prefixEnd_807640 : Nat := 4983230072969 + 3 ^ 40 * 807640 * 2
def baseEnd_807640 : Nat := 414707515797325338485737

theorem tailTrace_807640 : CollatzResearch.WordTrace tailWord_807640 prefixEnd_807640 414707515797325338485737 := by
  unfold tailWord_807640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728525397032844387814187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19638033862710459183752249 14728525397032844387814187)
  ·
    refine ⟨22092788095549266581721281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14728525397032844387814187 22092788095549266581721281)
    ·
      refine ⟨16569591071661949936290961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22092788095549266581721281 16569591071661949936290961)
      ·
        refine ⟨12427193303746462452218221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16569591071661949936290961 12427193303746462452218221)
        ·
          refine ⟨4660197488904923419581833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12427193303746462452218221 4660197488904923419581833)
          ·
            refine ⟨3495148116678692564686375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660197488904923419581833 3495148116678692564686375)
            ·
              refine ⟨5242722175018038847029563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495148116678692564686375 5242722175018038847029563)
              ·
                refine ⟨7864083262527058270544345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5242722175018038847029563 7864083262527058270544345)
                ·
                  refine ⟨5898062446895293702908259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7864083262527058270544345 5898062446895293702908259)
                  ·
                    refine ⟨8847093670342940554362389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5898062446895293702908259 8847093670342940554362389)
                    ·
                      refine ⟨414707515797325338485737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8847093670342940554362389 414707515797325338485737)
                      ·
                        rfl

theorem cell23_807640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_807640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807640 prefixEnd_807640 := by exact prefixLift 807640
  have htrace : WordTrace (prefixWord ++ tailWord_807640) baseStart_807640 baseEnd_807640 := by
    simpa [prefixWord, tailWord_807640, baseEnd_807640] using wordTrace_append hprefix tailTrace_807640
  have hstable : (prefixWord ++ tailWord_807640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807640).length < 2 ^ (prefixWord ++ tailWord_807640).sum := by decide
  have hdescent : baseEnd_807640 < baseStart_807640 := by decide
  rcases family_descends (prefixWord ++ tailWord_807640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807697 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_807697 : Nat := 118140960795 + 807697 * 2 ^ 59
def prefixEnd_807697 : Nat := 4983230072969 + 3 ^ 40 * 807697 * 2
def baseEnd_807697 : Nat := 138245594731543871824325

theorem tailTrace_807697 : CollatzResearch.WordTrace tailWord_807697 prefixEnd_807697 138245594731543871824325 := by
  unfold tailWord_807697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29459129754859187510453345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19639419836572791673635563 29459129754859187510453345)
  ·
    refine ⟨22094347316144390632840009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29459129754859187510453345 22094347316144390632840009)
    ·
      refine ⟨16570760487108292974630007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22094347316144390632840009 16570760487108292974630007)
      ·
        refine ⟨24856140730662439461945011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16570760487108292974630007 24856140730662439461945011)
        ·
          refine ⟨37284211095993659192917517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24856140730662439461945011 37284211095993659192917517)
          ·
            refine ⟨13981579160997622197344069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37284211095993659192917517 13981579160997622197344069)
            ·
              refine ⟨2621546092687054162002013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13981579160997622197344069 2621546092687054162002013)
              ·
                refine ⟨983079784757645310750755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2621546092687054162002013 983079784757645310750755)
                ·
                  refine ⟨1474619677136467966126133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983079784757645310750755 1474619677136467966126133)
                  ·
                    refine ⟨138245594731543871824325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1474619677136467966126133 138245594731543871824325)
                    ·
                      rfl

theorem cell23_807697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_807697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807697 prefixEnd_807697 := by exact prefixLift 807697
  have htrace : WordTrace (prefixWord ++ tailWord_807697) baseStart_807697 baseEnd_807697 := by
    simpa [prefixWord, tailWord_807697, baseEnd_807697] using wordTrace_append hprefix tailTrace_807697
  have hstable : (prefixWord ++ tailWord_807697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807697).length < 2 ^ (prefixWord ++ tailWord_807697).sum := by decide
  have hdescent : baseEnd_807697 < baseStart_807697 := by decide
  rcases family_descends (prefixWord ++ tailWord_807697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807711 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 3]
def baseStart_807711 : Nat := 118140960795 + 807711 * 2 ^ 59
def prefixEnd_807711 : Nat := 4983230072969 + 3 ^ 40 * 807711 * 2
def baseEnd_807711 : Nat := 414743972923794560697911

theorem tailTrace_807711 : CollatzResearch.WordTrace tailWord_807711 prefixEnd_807711 414743972923794560697911 := by
  unfold tailWord_807711
  simp only [CollatzResearch.WordTrace]
  refine ⟨29459640376808467901462987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19639760251205645267641991 29459640376808467901462987)
  ·
    refine ⟨44189460565212701852194481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29459640376808467901462987 44189460565212701852194481)
    ·
      refine ⟨33142095423909526389145861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44189460565212701852194481 33142095423909526389145861)
      ·
        refine ⟨6214142891983036197964849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33142095423909526389145861 6214142891983036197964849)
        ·
          refine ⟨4660607168987277148473637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6214142891983036197964849 4660607168987277148473637)
          ·
            refine ⟨873863844185114465338807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4660607168987277148473637 873863844185114465338807)
            ·
              refine ⟨1310795766277671698008211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873863844185114465338807 1310795766277671698008211)
              ·
                refine ⟨1966193649416507547012317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310795766277671698008211 1966193649416507547012317)
                ·
                  refine ⟨737322618531190330129619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1966193649416507547012317 737322618531190330129619)
                  ·
                    refine ⟨1105983927796785495194429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737322618531190330129619 1105983927796785495194429)
                    ·
                      refine ⟨414743972923794560697911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1105983927796785495194429 414743972923794560697911)
                      ·
                        rfl

theorem cell23_807711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_807711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807711 prefixEnd_807711 := by exact prefixLift 807711
  have htrace : WordTrace (prefixWord ++ tailWord_807711) baseStart_807711 baseEnd_807711 := by
    simpa [prefixWord, tailWord_807711, baseEnd_807711] using wordTrace_append hprefix tailTrace_807711
  have hstable : (prefixWord ++ tailWord_807711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807711).length < 2 ^ (prefixWord ++ tailWord_807711).sum := by decide
  have hdescent : baseEnd_807711 < baseStart_807711 := by decide
  rcases family_descends (prefixWord ++ tailWord_807711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807717 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_807717 : Nat := 118140960795 + 807717 * 2 ^ 59
def prefixEnd_807717 : Nat := 4983230072969 + 3 ^ 40 * 807717 * 2
def baseEnd_807717 : Nat := 414747053807721537222883

theorem tailTrace_807717 : CollatzResearch.WordTrace tailWord_807717 prefixEnd_807717 414747053807721537222883 := by
  unfold tailWord_807717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29459859214786730926181405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19639906143191153950787603 29459859214786730926181405)
  ·
    refine ⟨11047447205545024097318027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29459859214786730926181405 11047447205545024097318027)
    ·
      refine ⟨16571170808317536145977041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11047447205545024097318027 16571170808317536145977041)
      ·
        refine ⟨12428378106238152109482781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16571170808317536145977041 12428378106238152109482781)
        ·
          refine ⟨4660641789839307041056043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12428378106238152109482781 4660641789839307041056043)
          ·
            refine ⟨6990962684758960561584065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660641789839307041056043 6990962684758960561584065)
            ·
              refine ⟨5243222013569220421188049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6990962684758960561584065 5243222013569220421188049)
              ·
                refine ⟨3932416510176915315891037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243222013569220421188049 3932416510176915315891037)
                ·
                  refine ⟨1474656191316343243459139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3932416510176915315891037 1474656191316343243459139)
                  ·
                    refine ⟨2211984286974514865188709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474656191316343243459139 2211984286974514865188709)
                    ·
                      refine ⟨414747053807721537222883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2211984286974514865188709 414747053807721537222883)
                      ·
                        rfl

theorem cell23_807717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_807717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807717 prefixEnd_807717 := by exact prefixLift 807717
  have htrace : WordTrace (prefixWord ++ tailWord_807717) baseStart_807717 baseEnd_807717 := by
    simpa [prefixWord, tailWord_807717, baseEnd_807717] using wordTrace_append hprefix tailTrace_807717
  have hstable : (prefixWord ++ tailWord_807717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807717).length < 2 ^ (prefixWord ++ tailWord_807717).sum := by decide
  have hdescent : baseEnd_807717 < baseStart_807717 := by decide
  rcases family_descends (prefixWord ++ tailWord_807717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807747 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4]
def baseStart_807747 : Nat := 118140960795 + 807747 * 2 ^ 59
def prefixEnd_807747 : Nat := 4983230072969 + 3 ^ 40 * 807747 * 2
def baseEnd_807747 : Nat := 414762458227356419847745

theorem tailTrace_807747 : CollatzResearch.WordTrace tailWord_807747 prefixEnd_807747 414762458227356419847745 := by
  unfold tailWord_807747
  simp only [CollatzResearch.WordTrace]
  refine ⟨29460953404678046049773495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19640635603118697366515663 29460953404678046049773495)
  ·
    refine ⟨44191430107017069074660243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29460953404678046049773495 44191430107017069074660243)
    ·
      refine ⟨66287145160525603611990365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44191430107017069074660243 66287145160525603611990365)
      ·
        refine ⟨24857679435197101354496387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66287145160525603611990365 24857679435197101354496387)
        ·
          refine ⟨37286519152795652031744581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24857679435197101354496387 37286519152795652031744581)
          ·
            refine ⟨6991222341149184755952109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37286519152795652031744581 6991222341149184755952109)
            ·
              refine ⟨2621708377930944283482041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6991222341149184755952109 2621708377930944283482041)
              ·
                refine ⟨1966281283448208212611531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621708377930944283482041 1966281283448208212611531)
                ·
                  refine ⟨2949421925172312318917297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966281283448208212611531 2949421925172312318917297)
                  ·
                    refine ⟨2212066443879234239187973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949421925172312318917297 2212066443879234239187973)
                    ·
                      refine ⟨414762458227356419847745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2212066443879234239187973 414762458227356419847745)
                      ·
                        rfl

theorem cell23_807747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_807747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807747 prefixEnd_807747 := by exact prefixLift 807747
  have htrace : WordTrace (prefixWord ++ tailWord_807747) baseStart_807747 baseEnd_807747 := by
    simpa [prefixWord, tailWord_807747, baseEnd_807747] using wordTrace_append hprefix tailTrace_807747
  have hstable : (prefixWord ++ tailWord_807747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807747).length < 2 ^ (prefixWord ++ tailWord_807747).sum := by decide
  have hdescent : baseEnd_807747 < baseStart_807747 := by decide
  rcases family_descends (prefixWord ++ tailWord_807747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807757 : List Nat := [1, 6, 1, 2, 13]
def baseStart_807757 : Nat := 118140960795 + 807757 * 2 ^ 59
def prefixEnd_807757 : Nat := 4983230072969 + 3 ^ 40 * 807757 * 2
def baseEnd_807757 : Nat := 568954174257752236931

theorem tailTrace_807757 : CollatzResearch.WordTrace tailWord_807757 prefixEnd_807757 568954174257752236931 := by
  unfold tailWord_807757
  simp only [CollatzResearch.WordTrace]
  refine ⟨29461318134641817757637525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19640878756427878505091683 29461318134641817757637525)
  ·
    refine ⟨1380999287561335207389259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29461318134641817757637525 1380999287561335207389259)
    ·
      refine ⟨2071498931342002811083889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380999287561335207389259 2071498931342002811083889)
      ·
        refine ⟨1553624198506502108312917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2071498931342002811083889 1553624198506502108312917)
        ·
          refine ⟨568954174257752236931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1553624198506502108312917 568954174257752236931)
          ·
            rfl

theorem cell23_807757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 13].length) (baseStart_807757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807757 prefixEnd_807757 := by exact prefixLift 807757
  have htrace : WordTrace (prefixWord ++ tailWord_807757) baseStart_807757 baseEnd_807757 := by
    simpa [prefixWord, tailWord_807757, baseEnd_807757] using wordTrace_append hprefix tailTrace_807757
  have hstable : (prefixWord ++ tailWord_807757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807757).length < 2 ^ (prefixWord ++ tailWord_807757).sum := by decide
  have hdescent : baseEnd_807757 < baseStart_807757 := by decide
  rcases family_descends (prefixWord ++ tailWord_807757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807761 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_807761 : Nat := 118140960795 + 807761 * 2 ^ 59
def prefixEnd_807761 : Nat := 4983230072969 + 3 ^ 40 * 807761 * 2
def baseEnd_807761 : Nat := 138256548985506455024227

theorem tailTrace_807761 : CollatzResearch.WordTrace tailWord_807761 prefixEnd_807761 138256548985506455024227 := by
  unfold tailWord_807761
  simp only [CollatzResearch.WordTrace]
  refine ⟨29461464026627326440783137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19640976017751550960522091 29461464026627326440783137)
  ·
    refine ⟨22096098019970494830587353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29461464026627326440783137 22096098019970494830587353)
    ·
      refine ⟨16572073514977871122940515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22096098019970494830587353 16572073514977871122940515)
      ·
        refine ⟨24858110272466806684410773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16572073514977871122940515 24858110272466806684410773)
        ·
          refine ⟨1165223919021881563331755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24858110272466806684410773 1165223919021881563331755)
          ·
            refine ⟨1747835878532822344997633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165223919021881563331755 1747835878532822344997633)
            ·
              refine ⟨1310876908899616758748225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747835878532822344997633 1310876908899616758748225)
              ·
                refine ⟨983157681674712569061169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310876908899616758748225 983157681674712569061169)
                ·
                  refine ⟨737368261256034426795877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983157681674712569061169 737368261256034426795877)
                  ·
                    refine ⟨138256548985506455024227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737368261256034426795877 138256548985506455024227)
                    ·
                      rfl

theorem cell23_807761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_807761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807761 prefixEnd_807761 := by exact prefixLift 807761
  have htrace : WordTrace (prefixWord ++ tailWord_807761) baseStart_807761 baseEnd_807761 := by
    simpa [prefixWord, tailWord_807761, baseEnd_807761] using wordTrace_append hprefix tailTrace_807761
  have hstable : (prefixWord ++ tailWord_807761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807761).length < 2 ^ (prefixWord ++ tailWord_807761).sum := by decide
  have hdescent : baseEnd_807761 < baseStart_807761 := by decide
  rcases family_descends (prefixWord ++ tailWord_807761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807784 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_807784 : Nat := 118140960795 + 807784 * 2 ^ 59
def prefixEnd_807784 : Nat := 4983230072969 + 3 ^ 40 * 807784 * 2
def baseEnd_807784 : Nat := 414781457011572775085075

theorem tailTrace_807784 : CollatzResearch.WordTrace tailWord_807784 prefixEnd_807784 414781457011572775085075 := by
  unfold tailWord_807784
  simp only [CollatzResearch.WordTrace]
  refine ⟨14731151452772000684435203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19641535270362667579246937 14731151452772000684435203)
  ·
    refine ⟨22096727179158001026652805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14731151452772000684435203 22096727179158001026652805)
    ·
      refine ⟨4143136346092125192497401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22096727179158001026652805 4143136346092125192497401)
      ·
        refine ⟨3107352259569093894373051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4143136346092125192497401 3107352259569093894373051)
        ·
          refine ⟨4661028389353640841559577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107352259569093894373051 4661028389353640841559577)
          ·
            refine ⟨3495771292015230631169683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4661028389353640841559577 3495771292015230631169683)
            ·
              refine ⟨5243656938022845946754525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495771292015230631169683 5243656938022845946754525)
              ·
                refine ⟨1966371351758567230032947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5243656938022845946754525 1966371351758567230032947)
                ·
                  refine ⟨2949557027637850845049421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966371351758567230032947 2949557027637850845049421)
                  ·
                    refine ⟨1106083885364194066893533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949557027637850845049421 1106083885364194066893533)
                    ·
                      refine ⟨414781457011572775085075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106083885364194066893533 414781457011572775085075)
                      ·
                        rfl

theorem cell23_807784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_807784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807784 prefixEnd_807784 := by exact prefixLift 807784
  have htrace : WordTrace (prefixWord ++ tailWord_807784) baseStart_807784 baseEnd_807784 := by
    simpa [prefixWord, tailWord_807784, baseEnd_807784] using wordTrace_append hprefix tailTrace_807784
  have hstable : (prefixWord ++ tailWord_807784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807784).length < 2 ^ (prefixWord ++ tailWord_807784).sum := by decide
  have hdescent : baseEnd_807784 < baseStart_807784 := by decide
  rcases family_descends (prefixWord ++ tailWord_807784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807811 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 1, 3, 2]
def baseStart_807811 : Nat := 118140960795 + 807811 * 2 ^ 59
def prefixEnd_807811 : Nat := 4983230072969 + 3 ^ 40 * 807811 * 2
def baseEnd_807811 : Nat := 414795320989244169447451

theorem tailTrace_807811 : CollatzResearch.WordTrace tailWord_807811 prefixEnd_807811 414795320989244169447451 := by
  unfold tailWord_807811
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463287676446184980103287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19642191784297456653402191 29463287676446184980103287)
  ·
    refine ⟨44194931514669277470154931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29463287676446184980103287 44194931514669277470154931)
    ·
      refine ⟨66292397272003916205232397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44194931514669277470154931 66292397272003916205232397)
      ·
        refine ⟨24859648977001468576962149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66292397272003916205232397 24859648977001468576962149)
        ·
          refine ⟨4661184183187775358180403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24859648977001468576962149 4661184183187775358180403)
          ·
            refine ⟨6991776274781663037270605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661184183187775358180403 6991776274781663037270605)
            ·
              refine ⟨2621916103043123638976477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6991776274781663037270605 2621916103043123638976477)
              ·
                refine ⟨983218538641171364616179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2621916103043123638976477 983218538641171364616179)
                ·
                  refine ⟨1474827807961757046924269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983218538641171364616179 1474827807961757046924269)
                  ·
                    refine ⟨553060427985658892596601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474827807961757046924269 553060427985658892596601)
                    ·
                      refine ⟨414795320989244169447451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553060427985658892596601 414795320989244169447451)
                      ·
                        rfl

theorem cell23_807811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_807811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807811 prefixEnd_807811 := by exact prefixLift 807811
  have htrace : WordTrace (prefixWord ++ tailWord_807811) baseStart_807811 baseEnd_807811 := by
    simpa [prefixWord, tailWord_807811, baseEnd_807811] using wordTrace_append hprefix tailTrace_807811
  have hstable : (prefixWord ++ tailWord_807811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807811).length < 2 ^ (prefixWord ++ tailWord_807811).sum := by decide
  have hdescent : baseEnd_807811 < baseStart_807811 := by decide
  rcases family_descends (prefixWord ++ tailWord_807811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807817 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_807817 : Nat := 118140960795 + 807817 * 2 ^ 59
def prefixEnd_807817 : Nat := 4983230072969 + 3 ^ 40 * 807817 * 2
def baseEnd_807817 : Nat := 138266133957723715324141

theorem tailTrace_807817 : CollatzResearch.WordTrace tailWord_807817 prefixEnd_807817 138266133957723715324141 := by
  unfold tailWord_807817
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463506514424448004821705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19642337676282965336547803 29463506514424448004821705)
  ·
    refine ⟨22097629885818336003616279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29463506514424448004821705 22097629885818336003616279)
    ·
      refine ⟨33146444828727504005424419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22097629885818336003616279 33146444828727504005424419)
      ·
        refine ⟨49719667243091256008136629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33146444828727504005424419 49719667243091256008136629)
        ·
          refine ⟨4661218804039805250762809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49719667243091256008136629 4661218804039805250762809)
          ·
            refine ⟨3495914103029853938072107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4661218804039805250762809 3495914103029853938072107)
            ·
              refine ⟨5243871154544780907108161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495914103029853938072107 5243871154544780907108161)
              ·
                refine ⟨3932903365908585680331121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243871154544780907108161 3932903365908585680331121)
                ·
                  refine ⟨2949677524431439260248341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932903365908585680331121 2949677524431439260248341)
                  ·
                    refine ⟨138266133957723715324141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2949677524431439260248341 138266133957723715324141)
                    ·
                      rfl

theorem cell23_807817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_807817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807817 prefixEnd_807817 := by exact prefixLift 807817
  have htrace : WordTrace (prefixWord ++ tailWord_807817) baseStart_807817 baseEnd_807817 := by
    simpa [prefixWord, tailWord_807817, baseEnd_807817] using wordTrace_append hprefix tailTrace_807817
  have hstable : (prefixWord ++ tailWord_807817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807817).length < 2 ^ (prefixWord ++ tailWord_807817).sum := by decide
  have hdescent : baseEnd_807817 < baseStart_807817 := by decide
  rcases family_descends (prefixWord ++ tailWord_807817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807818 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_807818 : Nat := 118140960795 + 807818 * 2 ^ 59
def prefixEnd_807818 : Nat := 4983230072969 + 3 ^ 40 * 807818 * 2
def baseEnd_807818 : Nat := 414798915353825642059919

theorem tailTrace_807818 : CollatzResearch.WordTrace tailWord_807818 prefixEnd_807818 414798915353825642059919 := by
  unfold tailWord_807818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365885746855206293902027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19642361991613883450405405 7365885746855206293902027)
  ·
    refine ⟨11048828620282809440853041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7365885746855206293902027 11048828620282809440853041)
    ·
      refine ⟨8286621465212107080639781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11048828620282809440853041 8286621465212107080639781)
      ·
        refine ⟨1553741524727270077619959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8286621465212107080639781 1553741524727270077619959)
        ·
          refine ⟨2330612287090905116429939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553741524727270077619959 2330612287090905116429939)
          ·
            refine ⟨3495918430636357674644909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330612287090905116429939 3495918430636357674644909)
            ·
              refine ⟨1310969411488634127991841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3495918430636357674644909 1310969411488634127991841)
              ·
                refine ⟨983227058616475595993881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310969411488634127991841 983227058616475595993881)
                ·
                  refine ⟨737420293962356696995411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983227058616475595993881 737420293962356696995411)
                  ·
                    refine ⟨1106130440943535045493117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737420293962356696995411 1106130440943535045493117)
                    ·
                      refine ⟨414798915353825642059919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106130440943535045493117 414798915353825642059919)
                      ·
                        rfl

theorem cell23_807818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_807818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807818 prefixEnd_807818 := by exact prefixLift 807818
  have htrace : WordTrace (prefixWord ++ tailWord_807818) baseStart_807818 baseEnd_807818 := by
    simpa [prefixWord, tailWord_807818, baseEnd_807818] using wordTrace_append hprefix tailTrace_807818
  have hstable : (prefixWord ++ tailWord_807818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807818).length < 2 ^ (prefixWord ++ tailWord_807818).sum := by decide
  have hdescent : baseEnd_807818 < baseStart_807818 := by decide
  rcases family_descends (prefixWord ++ tailWord_807818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807827 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3]
def baseStart_807827 : Nat := 118140960795 + 807827 * 2 ^ 59
def prefixEnd_807827 : Nat := 4983230072969 + 3 ^ 40 * 807827 * 2
def baseEnd_807827 : Nat := 414803536679716106847377

theorem tailTrace_807827 : CollatzResearch.WordTrace tailWord_807827 prefixEnd_807827 414803536679716106847377 := by
  unfold tailWord_807827
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463871244388219712685735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19642580829592146475123823 29463871244388219712685735)
  ·
    refine ⟨44195806866582329569028603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29463871244388219712685735 44195806866582329569028603)
    ·
      refine ⟨66293710299873494353542905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44195806866582329569028603 66293710299873494353542905)
      ·
        refine ⟨49720282724905120765157179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66293710299873494353542905 49720282724905120765157179)
        ·
          refine ⟨74580424087357681147735769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49720282724905120765157179 74580424087357681147735769)
          ·
            refine ⟨55935318065518260860801827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74580424087357681147735769 55935318065518260860801827)
            ·
              refine ⟨83902977098277391291202741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55935318065518260860801827 83902977098277391291202741)
              ·
                refine ⟨7865904102963505433550257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83902977098277391291202741 7865904102963505433550257)
                ·
                  refine ⟨5899428077222629075162693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865904102963505433550257 5899428077222629075162693)
                  ·
                    refine ⟨1106142764479242951593005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899428077222629075162693 1106142764479242951593005)
                    ·
                      refine ⟨414803536679716106847377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106142764479242951593005 414803536679716106847377)
                      ·
                        rfl

theorem cell23_807827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_807827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807827 prefixEnd_807827 := by exact prefixLift 807827
  have htrace : WordTrace (prefixWord ++ tailWord_807827) baseStart_807827 baseEnd_807827 := by
    simpa [prefixWord, tailWord_807827, baseEnd_807827] using wordTrace_append hprefix tailTrace_807827
  have hstable : (prefixWord ++ tailWord_807827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807827).length < 2 ^ (prefixWord ++ tailWord_807827).sum := by decide
  have hdescent : baseEnd_807827 < baseStart_807827 := by decide
  rcases family_descends (prefixWord ++ tailWord_807827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807887 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_807887 : Nat := 118140960795 + 807887 * 2 ^ 59
def prefixEnd_807887 : Nat := 4983230072969 + 3 ^ 40 * 807887 * 2
def baseEnd_807887 : Nat := 414834345518985872097101

theorem tailTrace_807887 : CollatzResearch.WordTrace tailWord_807887 prefixEnd_807887 414834345518985872097101 := by
  unfold tailWord_807887
  simp only [CollatzResearch.WordTrace]
  refine ⟨29466059624170849959869915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19644039749447233306579943 29466059624170849959869915)
  ·
    refine ⟨44199089436256274939804873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29466059624170849959869915 44199089436256274939804873)
    ·
      refine ⟨33149317077192206204853655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44199089436256274939804873 33149317077192206204853655)
      ·
        refine ⟨49723975615788309307280483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33149317077192206204853655 49723975615788309307280483)
        ·
          refine ⟨74585963423682463960920725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49723975615788309307280483 74585963423682463960920725)
          ·
            refine ⟨3496217035485115498168159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74585963423682463960920725 3496217035485115498168159)
            ·
              refine ⟨5244325553227673247252239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496217035485115498168159 5244325553227673247252239)
              ·
                refine ⟨7866488329841509870878359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244325553227673247252239 7866488329841509870878359)
                ·
                  refine ⟨11799732494762264806317539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866488329841509870878359 11799732494762264806317539)
                  ·
                    refine ⟨17699598742143397209476309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11799732494762264806317539 17699598742143397209476309)
                    ·
                      refine ⟨414834345518985872097101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17699598742143397209476309 414834345518985872097101)
                      ·
                        rfl

theorem cell23_807887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_807887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807887 prefixEnd_807887 := by exact prefixLift 807887
  have htrace : WordTrace (prefixWord ++ tailWord_807887) baseStart_807887 baseEnd_807887 := by
    simpa [prefixWord, tailWord_807887, baseEnd_807887] using wordTrace_append hprefix tailTrace_807887
  have hstable : (prefixWord ++ tailWord_807887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807887).length < 2 ^ (prefixWord ++ tailWord_807887).sum := by decide
  have hdescent : baseEnd_807887 < baseStart_807887 := by decide
  rcases family_descends (prefixWord ++ tailWord_807887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807892 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_807892 : Nat := 118140960795 + 807892 * 2 ^ 59
def prefixEnd_807892 : Nat := 4983230072969 + 3 ^ 40 * 807892 * 2
def baseEnd_807892 : Nat := 414836912922258352534579

theorem tailTrace_807892 : CollatzResearch.WordTrace tailWord_807892 prefixEnd_807892 414836912922258352534579 := by
  unfold tailWord_807892
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733120994576367906900965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19644161326101823875867953 14733120994576367906900965)
  ·
    refine ⟨2762460186483068982543931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14733120994576367906900965 2762460186483068982543931)
    ·
      refine ⟨4143690279724603473815897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762460186483068982543931 4143690279724603473815897)
      ·
        refine ⟨3107767709793452605361923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4143690279724603473815897 3107767709793452605361923)
        ·
          refine ⟨4661651564690178908042885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107767709793452605361923 4661651564690178908042885)
          ·
            refine ⟨874059668379408545258041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4661651564690178908042885 874059668379408545258041)
            ·
              refine ⟨655544751284556408943531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874059668379408545258041 655544751284556408943531)
              ·
                refine ⟨983317126926834613415297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655544751284556408943531 983317126926834613415297)
                ·
                  refine ⟨737487845195125960061473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983317126926834613415297 737487845195125960061473)
                  ·
                    refine ⟨553115883896344470046105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 737487845195125960061473 553115883896344470046105)
                    ·
                      refine ⟨414836912922258352534579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553115883896344470046105 414836912922258352534579)
                      ·
                        rfl

theorem cell23_807892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_807892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807892 prefixEnd_807892 := by exact prefixLift 807892
  have htrace : WordTrace (prefixWord ++ tailWord_807892) baseStart_807892 baseEnd_807892 := by
    simpa [prefixWord, tailWord_807892, baseEnd_807892] using wordTrace_append hprefix tailTrace_807892
  have hstable : (prefixWord ++ tailWord_807892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807892).length < 2 ^ (prefixWord ++ tailWord_807892).sum := by decide
  have hdescent : baseEnd_807892 < baseStart_807892 := by decide
  rcases family_descends (prefixWord ++ tailWord_807892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807911 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 2, 5]
def baseStart_807911 : Nat := 118140960795 + 807911 * 2 ^ 59
def prefixEnd_807911 : Nat := 4983230072969 + 3 ^ 40 * 807911 * 2
def baseEnd_807911 : Nat := 138282223018231259398997

theorem tailTrace_807911 : CollatzResearch.WordTrace tailWord_807911 prefixEnd_807911 138282223018231259398997 := by
  unfold tailWord_807911
  simp only [CollatzResearch.WordTrace]
  refine ⟨29466934976083902058743587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19644623317389268039162391 29466934976083902058743587)
  ·
    refine ⟨44200402464125853088115381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29466934976083902058743587 44200402464125853088115381)
    ·
      refine ⟨4143787731011798727010817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44200402464125853088115381 4143787731011798727010817)
      ·
        refine ⟨3107840798258849045258113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4143787731011798727010817 3107840798258849045258113)
        ·
          refine ⟨2330880598694136783943585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3107840798258849045258113 2330880598694136783943585)
          ·
            refine ⟨1748160449020602587957689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2330880598694136783943585 1748160449020602587957689)
            ·
              refine ⟨1311120336765451940968267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748160449020602587957689 1311120336765451940968267)
              ·
                refine ⟨1966680505148177911452401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311120336765451940968267 1966680505148177911452401)
                ·
                  refine ⟨1475010378861133433589301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1966680505148177911452401 1475010378861133433589301)
                  ·
                    refine ⟨138282223018231259398997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1475010378861133433589301 138282223018231259398997)
                    ·
                      rfl

theorem cell23_807911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_807911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807911 prefixEnd_807911 := by exact prefixLift 807911
  have htrace : WordTrace (prefixWord ++ tailWord_807911) baseStart_807911 baseEnd_807911 := by
    simpa [prefixWord, tailWord_807911, baseEnd_807911] using wordTrace_append hprefix tailTrace_807911
  have hstable : (prefixWord ++ tailWord_807911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807911).length < 2 ^ (prefixWord ++ tailWord_807911).sum := by decide
  have hdescent : baseEnd_807911 < baseStart_807911 := by decide
  rcases family_descends (prefixWord ++ tailWord_807911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807965 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_807965 : Nat := 118140960795 + 807965 * 2 ^ 59
def prefixEnd_807965 : Nat := 4983230072969 + 3 ^ 40 * 807965 * 2
def baseEnd_807965 : Nat := 414874397010036566921743

theorem tailTrace_807965 : CollatzResearch.WordTrace tailWord_807965 prefixEnd_807965 414874397010036566921743 := by
  unfold tailWord_807965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468904517888269281209349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19645936345258846187472899 29468904517888269281209349)
  ·
    refine ⟨5525419597104050490226753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29468904517888269281209349 5525419597104050490226753)
    ·
      refine ⟨4144064697828037867670065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5525419597104050490226753 4144064697828037867670065)
      ·
        refine ⟨3108048523371028400752549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4144064697828037867670065 3108048523371028400752549)
        ·
          refine ⟨582759098132067825141103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3108048523371028400752549 582759098132067825141103)
          ·
            refine ⟨874138647198101737711655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582759098132067825141103 874138647198101737711655)
            ·
              refine ⟨1311207970797152606567483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874138647198101737711655 1311207970797152606567483)
              ·
                refine ⟨1966811956195728909851225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311207970797152606567483 1966811956195728909851225)
                ·
                  refine ⟨1475108967146796682388419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1966811956195728909851225 1475108967146796682388419)
                  ·
                    refine ⟨2212663450720195023582629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475108967146796682388419 2212663450720195023582629)
                    ·
                      refine ⟨414874397010036566921743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2212663450720195023582629 414874397010036566921743)
                      ·
                        rfl

theorem cell23_807965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_807965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807965 prefixEnd_807965 := by exact prefixLift 807965
  have htrace : WordTrace (prefixWord ++ tailWord_807965) baseStart_807965 baseEnd_807965 := by
    simpa [prefixWord, tailWord_807965, baseEnd_807965] using wordTrace_append hprefix tailTrace_807965
  have hstable : (prefixWord ++ tailWord_807965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807965).length < 2 ^ (prefixWord ++ tailWord_807965).sum := by decide
  have hdescent : baseEnd_807965 < baseStart_807965 := by decide
  rcases family_descends (prefixWord ++ tailWord_807965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807968 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3]
def baseStart_807968 : Nat := 118140960795 + 807968 * 2 ^ 59
def prefixEnd_807968 : Nat := 4983230072969 + 3 ^ 40 * 807968 * 2
def baseEnd_807968 : Nat := 414875937452000055184229

theorem tailTrace_807968 : CollatzResearch.WordTrace tailWord_807968 prefixEnd_807968 414875937452000055184229 := by
  unfold tailWord_807968
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734506968438700396784279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19646009291251600529045705 14734506968438700396784279)
  ·
    refine ⟨22101760452658050595176419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14734506968438700396784279 22101760452658050595176419)
    ·
      refine ⟨33152640678987075892764629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22101760452658050595176419 33152640678987075892764629)
      ·
        refine ⟨777015015913759591236671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33152640678987075892764629 777015015913759591236671)
        ·
          refine ⟨1165522523870639386855007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777015015913759591236671 1165522523870639386855007)
          ·
            refine ⟨1748283785805959080282511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165522523870639386855007 1748283785805959080282511)
            ·
              refine ⟨2622425678708938620423767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748283785805959080282511 2622425678708938620423767)
              ·
                refine ⟨3933638518063407930635651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622425678708938620423767 3933638518063407930635651)
                ·
                  refine ⟨5900457777095111895953477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933638518063407930635651 5900457777095111895953477)
                  ·
                    refine ⟨1106335833205333480491277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900457777095111895953477 1106335833205333480491277)
                    ·
                      refine ⟨414875937452000055184229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106335833205333480491277 414875937452000055184229)
                      ·
                        rfl

theorem cell23_807968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_807968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807968 prefixEnd_807968 := by exact prefixLift 807968
  have htrace : WordTrace (prefixWord ++ tailWord_807968) baseStart_807968 baseEnd_807968 := by
    simpa [prefixWord, tailWord_807968, baseEnd_807968] using wordTrace_append hprefix tailTrace_807968
  have hstable : (prefixWord ++ tailWord_807968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807968).length < 2 ^ (prefixWord ++ tailWord_807968).sum := by decide
  have hdescent : baseEnd_807968 < baseStart_807968 := by decide
  rcases family_descends (prefixWord ++ tailWord_807968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807975 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 1, 4]
def baseStart_807975 : Nat := 118140960795 + 807975 * 2 ^ 59
def prefixEnd_807975 : Nat := 4983230072969 + 3 ^ 40 * 807975 * 2
def baseEnd_807975 : Nat := 138293177272193842598899

theorem tailTrace_807975 : CollatzResearch.WordTrace tailWord_807975 prefixEnd_807975 138293177272193842598899 := by
  unfold tailWord_807975
  simp only [CollatzResearch.WordTrace]
  refine ⟨29469269247852040989073379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19646179498568027326048919 29469269247852040989073379)
  ·
    refine ⟨44203903871778061483610069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29469269247852040989073379 44203903871778061483610069)
    ·
      refine ⟨1036028996994798316022111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44203903871778061483610069 1036028996994798316022111)
      ·
        refine ⟨1554043495492197474033167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036028996994798316022111 1554043495492197474033167)
        ·
          refine ⟨2331065243238296211049751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554043495492197474033167 2331065243238296211049751)
          ·
            refine ⟨3496597864857444316574627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331065243238296211049751 3496597864857444316574627)
            ·
              refine ⟨5244896797286166474861941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496597864857444316574627 5244896797286166474861941)
              ·
                refine ⟨491709074745578107018307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5244896797286166474861941 491709074745578107018307)
                ·
                  refine ⟨737563612118367160527461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491709074745578107018307 737563612118367160527461)
                  ·
                    refine ⟨138293177272193842598899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737563612118367160527461 138293177272193842598899)
                    ·
                      rfl

theorem cell23_807975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_807975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807975 prefixEnd_807975 := by exact prefixLift 807975
  have htrace : WordTrace (prefixWord ++ tailWord_807975) baseStart_807975 baseEnd_807975 := by
    simpa [prefixWord, tailWord_807975, baseEnd_807975] using wordTrace_append hprefix tailTrace_807975
  have hstable : (prefixWord ++ tailWord_807975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807975).length < 2 ^ (prefixWord ++ tailWord_807975).sum := by decide
  have hdescent : baseEnd_807975 < baseStart_807975 := by decide
  rcases family_descends (prefixWord ++ tailWord_807975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807988 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 6]
def baseStart_807988 : Nat := 118140960795 + 807988 * 2 ^ 59
def prefixEnd_807988 : Nat := 4983230072969 + 3 ^ 40 * 807988 * 2
def baseEnd_807988 : Nat := 46098467451676664103793

theorem tailTrace_807988 : CollatzResearch.WordTrace tailWord_807988 prefixEnd_807988 46098467451676664103793 := by
  unfold tailWord_807988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734871698402472104648309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19646495597869962806197745 14734871698402472104648309)
  ·
    refine ⟨1381394221725231759810779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14734871698402472104648309 1381394221725231759810779)
    ·
      refine ⟨2072091332587847639716169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381394221725231759810779 2072091332587847639716169)
      ·
        refine ⟨1554068499440885729787127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2072091332587847639716169 1554068499440885729787127)
        ·
          refine ⟨2331102749161328594680691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554068499440885729787127 2331102749161328594680691)
          ·
            refine ⟨3496654123741992892021037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331102749161328594680691 3496654123741992892021037)
            ·
              refine ⟨1311245296403247334507889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3496654123741992892021037 1311245296403247334507889)
              ·
                refine ⟨983433972302435500880917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311245296403247334507889 983433972302435500880917)
                ·
                  refine ⟨46098467451676664103793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 983433972302435500880917 46098467451676664103793)
                  ·
                    rfl

theorem cell23_807988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_807988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807988 prefixEnd_807988 := by exact prefixLift 807988
  have htrace : WordTrace (prefixWord ++ tailWord_807988) baseStart_807988 baseEnd_807988 := by
    simpa [prefixWord, tailWord_807988, baseEnd_807988] using wordTrace_append hprefix tailTrace_807988
  have hstable : (prefixWord ++ tailWord_807988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807988).length < 2 ^ (prefixWord ++ tailWord_807988).sum := by decide
  have hdescent : baseEnd_807988 < baseStart_807988 := by decide
  rcases family_descends (prefixWord ++ tailWord_807988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807991 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_807991 : Nat := 118140960795 + 807991 * 2 ^ 59
def prefixEnd_807991 : Nat := 4983230072969 + 3 ^ 40 * 807991 * 2
def baseEnd_807991 : Nat := 414887747507053465196623

theorem tailTrace_807991 : CollatzResearch.WordTrace tailWord_807991 prefixEnd_807991 414887747507053465196623 := by
  unfold tailWord_807991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29469852815794075721655827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19646568543862717147770551 29469852815794075721655827)
  ·
    refine ⟨44204779223691113582483741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29469852815794075721655827 44204779223691113582483741)
    ·
      refine ⟨16576792208884167593431403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44204779223691113582483741 16576792208884167593431403)
      ·
        refine ⟨24865188313326251390147105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576792208884167593431403 24865188313326251390147105)
        ·
          refine ⟨18648891234994688542610329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24865188313326251390147105 18648891234994688542610329)
          ·
            refine ⟨13986668426246016406957747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18648891234994688542610329 13986668426246016406957747)
            ·
              refine ⟨20980002639369024610436621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13986668426246016406957747 20980002639369024610436621)
              ·
                refine ⟨7867500989763384228913733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20980002639369024610436621 7867500989763384228913733)
                ·
                  refine ⟨1475156435580634542921325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7867500989763384228913733 1475156435580634542921325)
                  ·
                    refine ⟨553183663342737953595497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475156435580634542921325 553183663342737953595497)
                    ·
                      refine ⟨414887747507053465196623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553183663342737953595497 414887747507053465196623)
                      ·
                        rfl

theorem cell23_807991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_807991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_807991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_807991 prefixEnd_807991 := by exact prefixLift 807991
  have htrace : WordTrace (prefixWord ++ tailWord_807991) baseStart_807991 baseEnd_807991 := by
    simpa [prefixWord, tailWord_807991, baseEnd_807991] using wordTrace_append hprefix tailTrace_807991
  have hstable : (prefixWord ++ tailWord_807991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807991).length < 2 ^ (prefixWord ++ tailWord_807991).sum := by decide
  have hdescent : baseEnd_807991 < baseStart_807991 := by decide
  rcases family_descends (prefixWord ++ tailWord_807991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808018 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_808018 : Nat := 118140960795 + 808018 * 2 ^ 59
def prefixEnd_808018 : Nat := 4983230072969 + 3 ^ 40 * 808018 * 2
def baseEnd_808018 : Nat := 138300537161574953186333

theorem tailTrace_808018 : CollatzResearch.WordTrace tailWord_808018 prefixEnd_808018 138300537161574953186333 := by
  unfold tailWord_808018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367709396674064833222177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19647225057797506221925805 7367709396674064833222177)
  ·
    refine ⟨5525782047505548624916633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7367709396674064833222177 5525782047505548624916633)
    ·
      refine ⟨4144336535629161468687475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5525782047505548624916633 4144336535629161468687475)
      ·
        refine ⟨6216504803443742203031213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144336535629161468687475 6216504803443742203031213)
        ·
          refine ⟨2331189301291403326136705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6216504803443742203031213 2331189301291403326136705)
          ·
            refine ⟨1748391975968552494602529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331189301291403326136705 1748391975968552494602529)
            ·
              refine ⟨1311293981976414370951897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748391975968552494602529 1311293981976414370951897)
              ·
                refine ⟨983470486482310778213923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311293981976414370951897 983470486482310778213923)
                ·
                  refine ⟨1475205729723466167320885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983470486482310778213923 1475205729723466167320885)
                  ·
                    refine ⟨138300537161574953186333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1475205729723466167320885 138300537161574953186333)
                    ·
                      rfl

theorem cell23_808018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_808018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808018 prefixEnd_808018 := by exact prefixLift 808018
  have htrace : WordTrace (prefixWord ++ tailWord_808018) baseStart_808018 baseEnd_808018 := by
    simpa [prefixWord, tailWord_808018, baseEnd_808018] using wordTrace_append hprefix tailTrace_808018
  have hstable : (prefixWord ++ tailWord_808018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808018).length < 2 ^ (prefixWord ++ tailWord_808018).sum := by decide
  have hdescent : baseEnd_808018 < baseStart_808018 := by decide
  rcases family_descends (prefixWord ++ tailWord_808018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808021 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_808021 : Nat := 118140960795 + 808021 * 2 ^ 59
def prefixEnd_808021 : Nat := 4983230072969 + 3 ^ 40 * 808021 * 2
def baseEnd_808021 : Nat := 414903151926688347821485

theorem tailTrace_808021 : CollatzResearch.WordTrace tailWord_808021 prefixEnd_808021 414903151926688347821485 := by
  unfold tailWord_808021
  simp only [CollatzResearch.WordTrace]
  refine ⟨29470947005685390845247917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19647298003790260563498611 29470947005685390845247917)
  ·
    refine ⟨11051605127132021566967969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29470947005685390845247917 11051605127132021566967969)
    ·
      refine ⟨8288703845349016175225977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11051605127132021566967969 8288703845349016175225977)
      ·
        refine ⟨6216527884011762131419483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8288703845349016175225977 6216527884011762131419483)
        ·
          refine ⟨9324791826017643197129225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216527884011762131419483 9324791826017643197129225)
          ·
            refine ⟨6993593869513232397846919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9324791826017643197129225 6993593869513232397846919)
            ·
              refine ⟨10490390804269848596770379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993593869513232397846919 10490390804269848596770379)
              ·
                refine ⟨15735586206404772895155569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10490390804269848596770379 15735586206404772895155569)
                ·
                  refine ⟨11801689654803579671366677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15735586206404772895155569 11801689654803579671366677)
                  ·
                    refine ⟨553204202568917797095313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11801689654803579671366677 553204202568917797095313)
                    ·
                      refine ⟨414903151926688347821485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553204202568917797095313 414903151926688347821485)
                      ·
                        rfl

theorem cell23_808021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_808021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808021 prefixEnd_808021 := by exact prefixLift 808021
  have htrace : WordTrace (prefixWord ++ tailWord_808021) baseStart_808021 baseEnd_808021 := by
    simpa [prefixWord, tailWord_808021, baseEnd_808021] using wordTrace_append hprefix tailTrace_808021
  have hstable : (prefixWord ++ tailWord_808021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808021).length < 2 ^ (prefixWord ++ tailWord_808021).sum := by decide
  have hdescent : baseEnd_808021 < baseStart_808021 := by decide
  rcases family_descends (prefixWord ++ tailWord_808021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808024 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_808024 : Nat := 118140960795 + 808024 * 2 ^ 59
def prefixEnd_808024 : Nat := 4983230072969 + 3 ^ 40 * 808024 * 2
def baseEnd_808024 : Nat := 414904692368651836083971

theorem tailTrace_808024 : CollatzResearch.WordTrace tailWord_808024 prefixEnd_808024 414904692368651836083971 := by
  unfold tailWord_808024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735528212337261178803563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19647370949783014905071417 14735528212337261178803563)
  ·
    refine ⟨22103292318505891768205345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14735528212337261178803563 22103292318505891768205345)
    ·
      refine ⟨16577469238879418826154009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22103292318505891768205345 16577469238879418826154009)
      ·
        refine ⟨12433101929159564119615507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16577469238879418826154009 12433101929159564119615507)
        ·
          refine ⟨18649652893739346179423261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433101929159564119615507 18649652893739346179423261)
          ·
            refine ⟨6993619835152254817283723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18649652893739346179423261 6993619835152254817283723)
            ·
              refine ⟨10490429752728382225925585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993619835152254817283723 10490429752728382225925585)
              ·
                refine ⟨7867822314546286669444189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10490429752728382225925585 7867822314546286669444189)
                ·
                  refine ⟨2950433367954857501041571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7867822314546286669444189 2950433367954857501041571)
                  ·
                    refine ⟨4425650051932286251562357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950433367954857501041571 4425650051932286251562357)
                    ·
                      refine ⟨414904692368651836083971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4425650051932286251562357 414904692368651836083971)
                      ·
                        rfl

theorem cell23_808024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_808024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808024 prefixEnd_808024 := by exact prefixLift 808024
  have htrace : WordTrace (prefixWord ++ tailWord_808024) baseStart_808024 baseEnd_808024 := by
    simpa [prefixWord, tailWord_808024, baseEnd_808024] using wordTrace_append hprefix tailTrace_808024
  have hstable : (prefixWord ++ tailWord_808024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808024).length < 2 ^ (prefixWord ++ tailWord_808024).sum := by decide
  have hdescent : baseEnd_808024 < baseStart_808024 := by decide
  rcases family_descends (prefixWord ++ tailWord_808024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808041 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_808041 : Nat := 118140960795 + 808041 * 2 ^ 59
def prefixEnd_808041 : Nat := 4983230072969 + 3 ^ 40 * 808041 * 2
def baseEnd_808041 : Nat := 414913421539778269571393

theorem tailTrace_808041 : CollatzResearch.WordTrace tailWord_808041 prefixEnd_808041 414913421539778269571393 := by
  unfold tailWord_808041
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471676465612934260975977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19647784310408622840650651 29471676465612934260975977)
  ·
    refine ⟨22103757349209700695731983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29471676465612934260975977 22103757349209700695731983)
    ·
      refine ⟨33155636023814551043597975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22103757349209700695731983 33155636023814551043597975)
      ·
        refine ⟨49733454035721826565396963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33155636023814551043597975 49733454035721826565396963)
        ·
          refine ⟨74600181053582739848095445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49733454035721826565396963 74600181053582739848095445)
          ·
            refine ⟨1748441743443345465189737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74600181053582739848095445 1748441743443345465189737)
            ·
              refine ⟨1311331307582509098892303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748441743443345465189737 1311331307582509098892303)
              ·
                refine ⟨1966996961373763648338455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311331307582509098892303 1966996961373763648338455)
                ·
                  refine ⟨2950495442060645472507683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966996961373763648338455 2950495442060645472507683)
                  ·
                    refine ⟨4425743163090968208761525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950495442060645472507683 4425743163090968208761525)
                    ·
                      refine ⟨414913421539778269571393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4425743163090968208761525 414913421539778269571393)
                      ·
                        rfl

theorem cell23_808041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_808041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808041 prefixEnd_808041 := by exact prefixLift 808041
  have htrace : WordTrace (prefixWord ++ tailWord_808041) baseStart_808041 baseEnd_808041 := by
    simpa [prefixWord, tailWord_808041, baseEnd_808041] using wordTrace_append hprefix tailTrace_808041
  have hstable : (prefixWord ++ tailWord_808041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808041).length < 2 ^ (prefixWord ++ tailWord_808041).sum := by decide
  have hdescent : baseEnd_808041 < baseStart_808041 := by decide
  rcases family_descends (prefixWord ++ tailWord_808041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808065 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 2, 4]
def baseStart_808065 : Nat := 118140960795 + 808065 * 2 ^ 59
def prefixEnd_808065 : Nat := 4983230072969 + 3 ^ 40 * 808065 * 2
def baseEnd_808065 : Nat := 138308581691828725223761

theorem tailTrace_808065 : CollatzResearch.WordTrace tailWord_808065 prefixEnd_808065 138308581691828725223761 := by
  unfold tailWord_808065
  simp only [CollatzResearch.WordTrace]
  refine ⟨29472551817525986359849649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19648367878350657573233099 29472551817525986359849649)
  ·
    refine ⟨22104413863144489769887237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29472551817525986359849649 22104413863144489769887237)
    ·
      refine ⟨4144577599339591831853857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22104413863144489769887237 4144577599339591831853857)
      ·
        refine ⟨3108433199504693873890393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4144577599339591831853857 3108433199504693873890393)
        ·
          refine ⟨2331324899628520405417795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108433199504693873890393 2331324899628520405417795)
          ·
            refine ⟨3496987349442780608126693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331324899628520405417795 3496987349442780608126693)
            ·
              refine ⟨655685128020521364023755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3496987349442780608126693 655685128020521364023755)
              ·
                refine ⟨983527692030782046035633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655685128020521364023755 983527692030782046035633)
                ·
                  refine ⟨737645769023086534526725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983527692030782046035633 737645769023086534526725)
                  ·
                    refine ⟨138308581691828725223761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737645769023086534526725 138308581691828725223761)
                    ·
                      rfl

theorem cell23_808065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_808065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808065 prefixEnd_808065 := by exact prefixLift 808065
  have htrace : WordTrace (prefixWord ++ tailWord_808065) baseStart_808065 baseEnd_808065 := by
    simpa [prefixWord, tailWord_808065, baseEnd_808065] using wordTrace_append hprefix tailTrace_808065
  have hstable : (prefixWord ++ tailWord_808065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808065).length < 2 ^ (prefixWord ++ tailWord_808065).sum := by decide
  have hdescent : baseEnd_808065 < baseStart_808065 := by decide
  rcases family_descends (prefixWord ++ tailWord_808065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808071 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_808071 : Nat := 118140960795 + 808071 * 2 ^ 59
def prefixEnd_808071 : Nat := 4983230072969 + 3 ^ 40 * 808071 * 2
def baseEnd_808071 : Nat := 414928825959413152196255

theorem tailTrace_808071 : CollatzResearch.WordTrace tailWord_808071 prefixEnd_808071 414928825959413152196255 := by
  unfold tailWord_808071
  simp only [CollatzResearch.WordTrace]
  refine ⟨29472770655504249384568067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19648513770336166256378711 29472770655504249384568067)
  ·
    refine ⟨44209155983256374076852101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29472770655504249384568067 44209155983256374076852101)
    ·
      refine ⟨8289216746860570139409769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44209155983256374076852101 8289216746860570139409769)
      ·
        refine ⟨6216912560145427604557327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8289216746860570139409769 6216912560145427604557327)
        ·
          refine ⟨9325368840218141406835991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216912560145427604557327 9325368840218141406835991)
          ·
            refine ⟨13988053260327212110253987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325368840218141406835991 13988053260327212110253987)
            ·
              refine ⟨20982079890490818165380981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13988053260327212110253987 20982079890490818165380981)
              ·
                refine ⟨1967069989733514203004467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20982079890490818165380981 1967069989733514203004467)
                ·
                  refine ⟨2950604984600271304506701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967069989733514203004467 2950604984600271304506701)
                  ·
                    refine ⟨1106476869225101739190013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950604984600271304506701 1106476869225101739190013)
                    ·
                      refine ⟨414928825959413152196255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106476869225101739190013 414928825959413152196255)
                      ·
                        rfl

theorem cell23_808071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_808071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808071 prefixEnd_808071 := by exact prefixLift 808071
  have htrace : WordTrace (prefixWord ++ tailWord_808071) baseStart_808071 baseEnd_808071 := by
    simpa [prefixWord, tailWord_808071, baseEnd_808071] using wordTrace_append hprefix tailTrace_808071
  have hstable : (prefixWord ++ tailWord_808071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808071).length < 2 ^ (prefixWord ++ tailWord_808071).sum := by decide
  have hdescent : baseEnd_808071 < baseStart_808071 := by decide
  rcases family_descends (prefixWord ++ tailWord_808071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808072 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_808072 : Nat := 118140960795 + 808072 * 2 ^ 59
def prefixEnd_808072 : Nat := 4983230072969 + 3 ^ 40 * 808072 * 2
def baseEnd_808072 : Nat := 414929339440067648283751

theorem tailTrace_808072 : CollatzResearch.WordTrace tailWord_808072 prefixEnd_808072 414929339440067648283751 := by
  unfold tailWord_808072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736403564250313277677235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19648538085667084370236313 14736403564250313277677235)
  ·
    refine ⟨22104605346375469916515853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14736403564250313277677235 22104605346375469916515853)
    ·
      refine ⟨8289227004890801218693445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22104605346375469916515853 8289227004890801218693445)
      ·
        refine ⟨1554230063417025228505021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8289227004890801218693445 1554230063417025228505021)
        ·
          refine ⟨582836273781384460689383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1554230063417025228505021 582836273781384460689383)
          ·
            refine ⟨874254410672076691034075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582836273781384460689383 874254410672076691034075)
            ·
              refine ⟨1311381616008115036551113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874254410672076691034075 1311381616008115036551113)
              ·
                refine ⟨983536212006086277413335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311381616008115036551113 983536212006086277413335)
                ·
                  refine ⟨1475304318009129416120003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983536212006086277413335 1475304318009129416120003)
                  ·
                    refine ⟨2212956477013694124180005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475304318009129416120003 2212956477013694124180005)
                    ·
                      refine ⟨414929339440067648283751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2212956477013694124180005 414929339440067648283751)
                      ·
                        rfl

theorem cell23_808072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_808072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808072 prefixEnd_808072 := by exact prefixLift 808072
  have htrace : WordTrace (prefixWord ++ tailWord_808072) baseStart_808072 baseEnd_808072 := by
    simpa [prefixWord, tailWord_808072, baseEnd_808072] using wordTrace_append hprefix tailTrace_808072
  have hstable : (prefixWord ++ tailWord_808072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808072).length < 2 ^ (prefixWord ++ tailWord_808072).sum := by decide
  have hdescent : baseEnd_808072 < baseStart_808072 := by decide
  rcases family_descends (prefixWord ++ tailWord_808072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808088 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_808088 : Nat := 118140960795 + 808088 * 2 ^ 59
def prefixEnd_808088 : Nat := 4983230072969 + 3 ^ 40 * 808088 * 2
def baseEnd_808088 : Nat := 414937555130539585683677

theorem tailTrace_808088 : CollatzResearch.WordTrace tailWord_808088 prefixEnd_808088 414937555130539585683677 := by
  unfold tailWord_808088
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736695348221330643968459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19648927130961774191957945 14736695348221330643968459)
  ·
    refine ⟨22105043022331995965952689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14736695348221330643968459 22105043022331995965952689)
    ·
      refine ⟨16578782266748996974464517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22105043022331995965952689 16578782266748996974464517)
      ·
        refine ⟨3108521675015436932712097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16578782266748996974464517 3108521675015436932712097)
        ·
          refine ⟨2331391256261577699534073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108521675015436932712097 2331391256261577699534073)
          ·
            refine ⟨1748543442196183274650555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331391256261577699534073 1748543442196183274650555)
            ·
              refine ⟨2622815163294274911975833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748543442196183274650555 2622815163294274911975833)
              ·
                refine ⟨1967111372470706183981875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622815163294274911975833 1967111372470706183981875)
                ·
                  refine ⟨2950667058706059275972813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967111372470706183981875 2950667058706059275972813)
                  ·
                    refine ⟨1106500147014772228489805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950667058706059275972813 1106500147014772228489805)
                    ·
                      refine ⟨414937555130539585683677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106500147014772228489805 414937555130539585683677)
                      ·
                        rfl

theorem cell23_808088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_808088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808088 prefixEnd_808088 := by exact prefixLift 808088
  have htrace : WordTrace (prefixWord ++ tailWord_808088) baseStart_808088 baseEnd_808088 := by
    simpa [prefixWord, tailWord_808088, baseEnd_808088] using wordTrace_append hprefix tailTrace_808088
  have hstable : (prefixWord ++ tailWord_808088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808088).length < 2 ^ (prefixWord ++ tailWord_808088).sum := by decide
  have hdescent : baseEnd_808088 < baseStart_808088 := by decide
  rcases family_descends (prefixWord ++ tailWord_808088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808106 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_808106 : Nat := 118140960795 + 808106 * 2 ^ 59
def prefixEnd_808106 : Nat := 4983230072969 + 3 ^ 40 * 808106 * 2
def baseEnd_808106 : Nat := 414946797782320515258595

theorem tailTrace_808106 : CollatzResearch.WordTrace tailWord_808106 prefixEnd_808106 414946797782320515258595 := by
  unfold tailWord_808106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7368511802594362590523043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19649364806918300241394781 7368511802594362590523043)
  ·
    refine ⟨11052767703891543885784565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7368511802594362590523043 11052767703891543885784565)
    ·
      refine ⟨1036196972239832239292303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11052767703891543885784565 1036196972239832239292303)
      ·
        refine ⟨1554295458359748358938455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036196972239832239292303 1554295458359748358938455)
        ·
          refine ⟨2331443187539622538407683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554295458359748358938455 2331443187539622538407683)
          ·
            refine ⟨3497164781309433807611525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331443187539622538407683 3497164781309433807611525)
            ·
              refine ⟨655718396495518838927161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3497164781309433807611525 655718396495518838927161)
              ·
                refine ⟨491788797371639129195371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655718396495518838927161 491788797371639129195371)
                ·
                  refine ⟨737683196057458693793057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491788797371639129195371 737683196057458693793057)
                  ·
                    refine ⟨553262397043094020344793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 737683196057458693793057 553262397043094020344793)
                    ·
                      refine ⟨414946797782320515258595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553262397043094020344793 414946797782320515258595)
                      ·
                        rfl

theorem cell23_808106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_808106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808106 prefixEnd_808106 := by exact prefixLift 808106
  have htrace : WordTrace (prefixWord ++ tailWord_808106) baseStart_808106 baseEnd_808106 := by
    simpa [prefixWord, tailWord_808106, baseEnd_808106] using wordTrace_append hprefix tailTrace_808106
  have hstable : (prefixWord ++ tailWord_808106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808106).length < 2 ^ (prefixWord ++ tailWord_808106).sum := by decide
  have hdescent : baseEnd_808106 < baseStart_808106 := by decide
  rcases family_descends (prefixWord ++ tailWord_808106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808121 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_808121 : Nat := 118140960795 + 808121 * 2 ^ 59
def prefixEnd_808121 : Nat := 4983230072969 + 3 ^ 40 * 808121 * 2
def baseEnd_808121 : Nat := 138318166664045985523675

theorem tailTrace_808121 : CollatzResearch.WordTrace tailWord_808121 prefixEnd_808121 138318166664045985523675 := by
  unfold tailWord_808121
  simp only [CollatzResearch.WordTrace]
  refine ⟨29474594305323107923888217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19649729536882071949258811 29474594305323107923888217)
  ·
    refine ⟨22105945728992330942916163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29474594305323107923888217 22105945728992330942916163)
    ·
      refine ⟨33158918593488496414374245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22105945728992330942916163 33158918593488496414374245)
      ·
        refine ⟨6217297236279093077695171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33158918593488496414374245 6217297236279093077695171)
        ·
          refine ⟨9325945854418639616542757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217297236279093077695171 9325945854418639616542757)
          ·
            refine ⟨1748614847703494928101767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9325945854418639616542757 1748614847703494928101767)
            ·
              refine ⟨2622922271555242392152651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748614847703494928101767 2622922271555242392152651)
              ·
                refine ⟨3934383407332863588228977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622922271555242392152651 3934383407332863588228977)
                ·
                  refine ⟨2950787555499647691171733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934383407332863588228977 2950787555499647691171733)
                  ·
                    refine ⟨138318166664045985523675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2950787555499647691171733 138318166664045985523675)
                    ·
                      rfl

theorem cell23_808121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_808121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808121 prefixEnd_808121 := by exact prefixLift 808121
  have htrace : WordTrace (prefixWord ++ tailWord_808121) baseStart_808121 baseEnd_808121 := by
    simpa [prefixWord, tailWord_808121, baseEnd_808121] using wordTrace_append hprefix tailTrace_808121
  have hstable : (prefixWord ++ tailWord_808121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808121).length < 2 ^ (prefixWord ++ tailWord_808121).sum := by decide
  have hdescent : baseEnd_808121 < baseStart_808121 := by decide
  rcases family_descends (prefixWord ++ tailWord_808121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808149 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_808149 : Nat := 118140960795 + 808149 * 2 ^ 59
def prefixEnd_808149 : Nat := 4983230072969 + 3 ^ 40 * 808149 * 2
def baseEnd_808149 : Nat := 414968877450463847020897

theorem tailTrace_808149 : CollatzResearch.WordTrace tailWord_808149 prefixEnd_808149 414968877450463847020897 := by
  unfold tailWord_808149
  simp only [CollatzResearch.WordTrace]
  refine ⟨29475615549221668705907501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19650410366147779137271667 29475615549221668705907501)
  ·
    refine ⟨11053355830958125764715313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29475615549221668705907501 11053355830958125764715313)
    ·
      refine ⟨8290016873218594323536485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11053355830958125764715313 8290016873218594323536485)
      ·
        refine ⟨1554378163728486435663091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8290016873218594323536485 1554378163728486435663091)
        ·
          refine ⟨2331567245592729653494637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554378163728486435663091 2331567245592729653494637)
          ·
            refine ⟨874337717097273620060489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2331567245592729653494637 874337717097273620060489)
            ·
              refine ⟨655753287822955215045367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874337717097273620060489 655753287822955215045367)
              ·
                refine ⟨983629931734432822568051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655753287822955215045367 983629931734432822568051)
                ·
                  refine ⟨1475444897601649233852077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983629931734432822568051 1475444897601649233852077)
                  ·
                    refine ⟨553291836600618462694529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475444897601649233852077 553291836600618462694529)
                    ·
                      refine ⟨414968877450463847020897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553291836600618462694529 414968877450463847020897)
                      ·
                        rfl

theorem cell23_808149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_808149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808149 prefixEnd_808149 := by exact prefixLift 808149
  have htrace : WordTrace (prefixWord ++ tailWord_808149) baseStart_808149 baseEnd_808149 := by
    simpa [prefixWord, tailWord_808149, baseEnd_808149] using wordTrace_append hprefix tailTrace_808149
  have hstable : (prefixWord ++ tailWord_808149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808149).length < 2 ^ (prefixWord ++ tailWord_808149).sum := by decide
  have hdescent : baseEnd_808149 < baseStart_808149 := by decide
  rcases family_descends (prefixWord ++ tailWord_808149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808168 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 5]
def baseStart_808168 : Nat := 118140960795 + 808168 * 2 ^ 59
def prefixEnd_808168 : Nat := 4983230072969 + 3 ^ 40 * 808168 * 2
def baseEnd_808168 : Nat := 46108737064766585853701

theorem tailTrace_808168 : CollatzResearch.WordTrace tailWord_808168 prefixEnd_808168 46108737064766585853701 := by
  unfold tailWord_808168
  simp only [CollatzResearch.WordTrace]
  refine ⟨14738154268076417475424579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19650872357435223300566105 14738154268076417475424579)
  ·
    refine ⟨22107231402114626213136869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14738154268076417475424579 22107231402114626213136869)
    ·
      refine ⟨4145105887896492414963163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22107231402114626213136869 4145105887896492414963163)
      ·
        refine ⟨6217658831844738622444745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145105887896492414963163 6217658831844738622444745)
        ·
          refine ⟨4663244123883553966833559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6217658831844738622444745 4663244123883553966833559)
          ·
            refine ⟨6994866185825330950250339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663244123883553966833559 6994866185825330950250339)
            ·
              refine ⟨10492299278737996425375509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994866185825330950250339 10492299278737996425375509)
              ·
                refine ⟨491826528690843582439477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10492299278737996425375509 491826528690843582439477)
                ·
                  refine ⟨46108737064766585853701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 491826528690843582439477 46108737064766585853701)
                  ·
                    rfl

theorem cell23_808168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 5].length) (baseStart_808168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808168 prefixEnd_808168 := by exact prefixLift 808168
  have htrace : WordTrace (prefixWord ++ tailWord_808168) baseStart_808168 baseEnd_808168 := by
    simpa [prefixWord, tailWord_808168, baseEnd_808168] using wordTrace_append hprefix tailTrace_808168
  have hstable : (prefixWord ++ tailWord_808168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808168).length < 2 ^ (prefixWord ++ tailWord_808168).sum := by decide
  have hdescent : baseEnd_808168 < baseStart_808168 := by decide
  rcases family_descends (prefixWord ++ tailWord_808168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808201 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_808201 : Nat := 118140960795 + 808201 * 2 ^ 59
def prefixEnd_808201 : Nat := 4983230072969 + 3 ^ 40 * 808201 * 2
def baseEnd_808201 : Nat := 414995578444497643570657

theorem tailTrace_808201 : CollatzResearch.WordTrace tailWord_808201 prefixEnd_808201 414995578444497643570657 := by
  unfold tailWord_808201
  simp only [CollatzResearch.WordTrace]
  refine ⟨29477512145033281586800457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19651674763355521057866971 29477512145033281586800457)
  ·
    refine ⟨22108134108774961190100343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29477512145033281586800457 22108134108774961190100343)
    ·
      refine ⟨33162201163162441785150515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22108134108774961190100343 33162201163162441785150515)
      ·
        refine ⟨49743301744743662677725773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33162201163162441785150515 49743301744743662677725773)
        ·
          refine ⟨18653738154278873504147165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49743301744743662677725773 18653738154278873504147165)
          ·
            refine ⟨6995151807854577564055187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18653738154278873504147165 6995151807854577564055187)
            ·
              refine ⟨10492727711781866346082781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6995151807854577564055187 10492727711781866346082781)
              ·
                refine ⟨3934772891918199879781043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10492727711781866346082781 3934772891918199879781043)
                ·
                  refine ⟨5902159337877299819671565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934772891918199879781043 5902159337877299819671565)
                  ·
                    refine ⟨2213309751703987432376837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5902159337877299819671565 2213309751703987432376837)
                    ·
                      refine ⟨414995578444497643570657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2213309751703987432376837 414995578444497643570657)
                      ·
                        rfl

theorem cell23_808201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_808201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808201 prefixEnd_808201 := by exact prefixLift 808201
  have htrace : WordTrace (prefixWord ++ tailWord_808201) baseStart_808201 baseEnd_808201 := by
    simpa [prefixWord, tailWord_808201, baseEnd_808201] using wordTrace_append hprefix tailTrace_808201
  have hstable : (prefixWord ++ tailWord_808201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808201).length < 2 ^ (prefixWord ++ tailWord_808201).sum := by decide
  have hdescent : baseEnd_808201 < baseStart_808201 := by decide
  rcases family_descends (prefixWord ++ tailWord_808201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808218 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_808218 : Nat := 118140960795 + 808218 * 2 ^ 59
def prefixEnd_808218 : Nat := 4983230072969 + 3 ^ 40 * 808218 * 2
def baseEnd_808218 : Nat := 415004307615624077058079

theorem tailTrace_808218 : CollatzResearch.WordTrace tailWord_808218 prefixEnd_808218 415004307615624077058079 := by
  unfold tailWord_808218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369533046492923372542327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19652088123981128993446205 7369533046492923372542327)
  ·
    refine ⟨11054299569739385058813491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7369533046492923372542327 11054299569739385058813491)
    ·
      refine ⟨16581449354609077588220237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11054299569739385058813491 16581449354609077588220237)
      ·
        refine ⟨6218043507978404095582589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16581449354609077588220237 6218043507978404095582589)
        ·
          refine ⟨2331766315491901535843471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6218043507978404095582589 2331766315491901535843471)
          ·
            refine ⟨3497649473237852303765207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331766315491901535843471 3497649473237852303765207)
            ·
              refine ⟨5246474209856778455647811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497649473237852303765207 5246474209856778455647811)
              ·
                refine ⟨7869711314785167683471717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246474209856778455647811 7869711314785167683471717)
                ·
                  refine ⟨1475570871522218940650947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7869711314785167683471717 1475570871522218940650947)
                  ·
                    refine ⟨2213356307283328410976421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475570871522218940650947 2213356307283328410976421)
                    ·
                      refine ⟨415004307615624077058079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2213356307283328410976421 415004307615624077058079)
                      ·
                        rfl

theorem cell23_808218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_808218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808218 prefixEnd_808218 := by exact prefixLift 808218
  have htrace : WordTrace (prefixWord ++ tailWord_808218) baseStart_808218 baseEnd_808218 := by
    simpa [prefixWord, tailWord_808218, baseEnd_808218] using wordTrace_append hprefix tailTrace_808218
  have hstable : (prefixWord ++ tailWord_808218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808218).length < 2 ^ (prefixWord ++ tailWord_808218).sum := by decide
  have hdescent : baseEnd_808218 < baseStart_808218 := by decide
  rcases family_descends (prefixWord ++ tailWord_808218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808255 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_808255 : Nat := 118140960795 + 808255 * 2 ^ 59
def prefixEnd_808255 : Nat := 4983230072969 + 3 ^ 40 * 808255 * 2
def baseEnd_808255 : Nat := 415023306399840432295409

theorem tailTrace_808255 : CollatzResearch.WordTrace tailWord_808255 prefixEnd_808255 415023306399840432295409 := by
  unfold tailWord_808255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29479481686837648809266219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19652987791225099206177479 29479481686837648809266219)
  ·
    refine ⟨44219222530256473213899329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29479481686837648809266219 44219222530256473213899329)
    ·
      refine ⟨33164416897692354910424497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44219222530256473213899329 33164416897692354910424497)
      ·
        refine ⟨24873312673269266182818373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33164416897692354910424497 24873312673269266182818373)
        ·
          refine ⟨4663746126237987409278445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24873312673269266182818373 4663746126237987409278445)
          ·
            refine ⟨1748904797339245278479417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4663746126237987409278445 1748904797339245278479417)
            ·
              refine ⟨1311678598004433958859563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748904797339245278479417 1311678598004433958859563)
              ·
                refine ⟨1967517897006650938289345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311678598004433958859563 1967517897006650938289345)
                ·
                  refine ⟨1475638422754988203717009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967517897006650938289345 1475638422754988203717009)
                  ·
                    refine ⟨1106728817066241152787757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1475638422754988203717009 1106728817066241152787757)
                    ·
                      refine ⟨415023306399840432295409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106728817066241152787757 415023306399840432295409)
                      ·
                        rfl

theorem cell23_808255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_808255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808255 prefixEnd_808255 := by exact prefixLift 808255
  have htrace : WordTrace (prefixWord ++ tailWord_808255) baseStart_808255 baseEnd_808255 := by
    simpa [prefixWord, tailWord_808255, baseEnd_808255] using wordTrace_append hprefix tailTrace_808255
  have hstable : (prefixWord ++ tailWord_808255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808255).length < 2 ^ (prefixWord ++ tailWord_808255).sum := by decide
  have hdescent : baseEnd_808255 < baseStart_808255 := by decide
  rcases family_descends (prefixWord ++ tailWord_808255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808279 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 1, 4]
def baseStart_808279 : Nat := 118140960795 + 808279 * 2 ^ 59
def prefixEnd_808279 : Nat := 4983230072969 + 3 ^ 40 * 808279 * 2
def baseEnd_808279 : Nat := 138345209978516112798433

theorem tailTrace_808279 : CollatzResearch.WordTrace tailWord_808279 prefixEnd_808279 138345209978516112798433 := by
  unfold tailWord_808279
  simp only [CollatzResearch.WordTrace]
  refine ⟨29480357038750700908139891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19653571359167133938759927 29480357038750700908139891)
  ·
    refine ⟨44220535558126051362209837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29480357038750700908139891 44220535558126051362209837)
    ·
      refine ⟨16582700834297269260828689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44220535558126051362209837 16582700834297269260828689)
      ·
        refine ⟨12437025625722951945621517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16582700834297269260828689 12437025625722951945621517)
        ·
          refine ⟨4663884609646106979608069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12437025625722951945621517 4663884609646106979608069)
          ·
            refine ⟨874478364308645058676513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4663884609646106979608069 874478364308645058676513)
            ·
              refine ⟨655858773231483794007385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874478364308645058676513 655858773231483794007385)
              ·
                refine ⟨491894079923612845505539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655858773231483794007385 491894079923612845505539)
                ·
                  refine ⟨737841119885419268258309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491894079923612845505539 737841119885419268258309)
                  ·
                    refine ⟨138345209978516112798433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737841119885419268258309 138345209978516112798433)
                    ·
                      rfl

theorem cell23_808279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_808279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808279 prefixEnd_808279 := by exact prefixLift 808279
  have htrace : WordTrace (prefixWord ++ tailWord_808279) baseStart_808279 baseEnd_808279 := by
    simpa [prefixWord, tailWord_808279, baseEnd_808279] using wordTrace_append hprefix tailTrace_808279
  have hstable : (prefixWord ++ tailWord_808279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808279).length < 2 ^ (prefixWord ++ tailWord_808279).sum := by decide
  have hdescent : baseEnd_808279 < baseStart_808279 := by decide
  rcases family_descends (prefixWord ++ tailWord_808279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808288 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 3, 5]
def baseStart_808288 : Nat := 118140960795 + 808288 * 2 ^ 59
def prefixEnd_808288 : Nat := 4983230072969 + 3 ^ 40 * 808288 * 2
def baseEnd_808288 : Nat := 138346750420479601060919

theorem tailTrace_808288 : CollatzResearch.WordTrace tailWord_808288 prefixEnd_808288 138346750420479601060919 := by
  unfold tailWord_808288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14740342647859047722608759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19653790197145396963478345 14740342647859047722608759)
  ·
    refine ⟨22110513971788571583913139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14740342647859047722608759 22110513971788571583913139)
    ·
      refine ⟨33165770957682857375869709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22110513971788571583913139 33165770957682857375869709)
      ·
        refine ⟨12437164109131071515951141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33165770957682857375869709 12437164109131071515951141)
        ·
          refine ⟨2331968270462075909240839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12437164109131071515951141 2331968270462075909240839)
          ·
            refine ⟨3497952405693113863861259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331968270462075909240839 3497952405693113863861259)
            ·
              refine ⟨5246928608539670795791889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497952405693113863861259 5246928608539670795791889)
              ·
                refine ⟨3935196456404753096843917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246928608539670795791889 3935196456404753096843917)
                ·
                  refine ⟨1475698671151782411316469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3935196456404753096843917 1475698671151782411316469)
                  ·
                    refine ⟨138346750420479601060919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1475698671151782411316469 138346750420479601060919)
                    ·
                      rfl

theorem cell23_808288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_808288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808288 prefixEnd_808288 := by exact prefixLift 808288
  have htrace : WordTrace (prefixWord ++ tailWord_808288) baseStart_808288 baseEnd_808288 := by
    simpa [prefixWord, tailWord_808288, baseEnd_808288] using wordTrace_append hprefix tailTrace_808288
  have hstable : (prefixWord ++ tailWord_808288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808288).length < 2 ^ (prefixWord ++ tailWord_808288).sum := by decide
  have hdescent : baseEnd_808288 < baseStart_808288 := by decide
  rcases family_descends (prefixWord ++ tailWord_808288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808331 : List Nat := [1, 1, 1, 1, 4, 3, 12]
def baseStart_808331 : Nat := 118140960795 + 808331 * 2 ^ 59
def prefixEnd_808331 : Nat := 4983230072969 + 3 ^ 40 * 808331 * 2
def baseEnd_808331 : Nat := 5124226307772618949939

theorem tailTrace_808331 : CollatzResearch.WordTrace tailWord_808331 prefixEnd_808331 5124226307772618949939 := by
  unfold tailWord_808331
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482253634562313789032847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19654835756374875859355231 29482253634562313789032847)
  ·
    refine ⟨44223380451843470683549271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29482253634562313789032847 44223380451843470683549271)
    ·
      refine ⟨66335070677765206025323907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44223380451843470683549271 66335070677765206025323907)
      ·
        refine ⟨99502606016647809037985861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66335070677765206025323907 99502606016647809037985861)
        ·
          refine ⟨18656738628121464194622349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99502606016647809037985861 18656738628121464194622349)
          ·
            refine ⟨6996276985545549072983381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18656738628121464194622349 6996276985545549072983381)
            ·
              refine ⟨5124226307772618949939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 6996276985545549072983381 5124226307772618949939)
              ·
                rfl

theorem cell23_808331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 12].length) (baseStart_808331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808331 prefixEnd_808331 := by exact prefixLift 808331
  have htrace : WordTrace (prefixWord ++ tailWord_808331) baseStart_808331 baseEnd_808331 := by
    simpa [prefixWord, tailWord_808331, baseEnd_808331] using wordTrace_append hprefix tailTrace_808331
  have hstable : (prefixWord ++ tailWord_808331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808331).length < 2 ^ (prefixWord ++ tailWord_808331).sum := by decide
  have hdescent : baseEnd_808331 < baseStart_808331 := by decide
  rcases family_descends (prefixWord ++ tailWord_808331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808352 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 2, 4]
def baseStart_808352 : Nat := 118140960795 + 808352 * 2 ^ 59
def prefixEnd_808352 : Nat := 4983230072969 + 3 ^ 40 * 808352 * 2
def baseEnd_808352 : Nat := 138357704674442184260821

theorem tailTrace_808352 : CollatzResearch.WordTrace tailWord_808352 prefixEnd_808352 138357704674442184260821 := by
  unfold tailWord_808352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14741509783743117187773655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19655346378324156250364873 14741509783743117187773655)
  ·
    refine ⟨22112264675614675781660483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14741509783743117187773655 22112264675614675781660483)
    ·
      refine ⟨33168397013422013672490725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22112264675614675781660483 33168397013422013672490725)
      ·
        refine ⟨6219074440016627563592011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33168397013422013672490725 6219074440016627563592011)
        ·
          refine ⟨9328611660024941345388017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219074440016627563592011 9328611660024941345388017)
          ·
            refine ⟨6996458745018706009041013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9328611660024941345388017 6996458745018706009041013)
            ·
              refine ⟨655918007345503688347595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6996458745018706009041013 655918007345503688347595)
              ·
                refine ⟨983877011018255532521393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655918007345503688347595 983877011018255532521393)
                ·
                  refine ⟨737907758263691649391045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983877011018255532521393 737907758263691649391045)
                  ·
                    refine ⟨138357704674442184260821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737907758263691649391045 138357704674442184260821)
                    ·
                      rfl

theorem cell23_808352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_808352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808352 prefixEnd_808352 := by exact prefixLift 808352
  have htrace : WordTrace (prefixWord ++ tailWord_808352) baseStart_808352 baseEnd_808352 := by
    simpa [prefixWord, tailWord_808352, baseEnd_808352] using wordTrace_append hprefix tailTrace_808352
  have hstable : (prefixWord ++ tailWord_808352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808352).length < 2 ^ (prefixWord ++ tailWord_808352).sum := by decide
  have hdescent : baseEnd_808352 < baseStart_808352 := by decide
  rcases family_descends (prefixWord ++ tailWord_808352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808365 : List Nat := [1, 5, 2, 2, 1, 2, 1, 9]
def baseStart_808365 : Nat := 118140960795 + 808365 * 2 ^ 59
def prefixEnd_808365 : Nat := 4983230072969 + 3 ^ 40 * 808365 * 2
def baseEnd_808365 : Nat := 15373325528586481552589

theorem tailTrace_808365 : CollatzResearch.WordTrace tailWord_808365 prefixEnd_808365 15373325528586481552589 := by
  unfold tailWord_808365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483493716439137595770549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19655662477626091730513699 29483493716439137595770549)
  ·
    refine ⟨2764077535916169149603489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29483493716439137595770549 2764077535916169149603489)
    ·
      refine ⟨2073058151937126862202617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2764077535916169149603489 2073058151937126862202617)
      ·
        refine ⟨1554793613952845146651963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2073058151937126862202617 1554793613952845146651963)
        ·
          refine ⟨2332190420929267719977945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554793613952845146651963 2332190420929267719977945)
          ·
            refine ⟨1749142815696950789983459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332190420929267719977945 1749142815696950789983459)
            ·
              refine ⟨2623714223545426184975189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749142815696950789983459 2623714223545426184975189)
              ·
                refine ⟨15373325528586481552589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2623714223545426184975189 15373325528586481552589)
                ·
                  rfl

theorem cell23_808365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 9].length) (baseStart_808365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808365 prefixEnd_808365 := by exact prefixLift 808365
  have htrace : WordTrace (prefixWord ++ tailWord_808365) baseStart_808365 baseEnd_808365 := by
    simpa [prefixWord, tailWord_808365, baseEnd_808365] using wordTrace_append hprefix tailTrace_808365
  have hstable : (prefixWord ++ tailWord_808365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808365).length < 2 ^ (prefixWord ++ tailWord_808365).sum := by decide
  have hdescent : baseEnd_808365 < baseStart_808365 := by decide
  rcases family_descends (prefixWord ++ tailWord_808365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808375 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_808375 : Nat := 118140960795 + 808375 * 2 ^ 59
def prefixEnd_808375 : Nat := 4983230072969 + 3 ^ 40 * 808375 * 2
def baseEnd_808375 : Nat := 415084924078379962794857

theorem tailTrace_808375 : CollatzResearch.WordTrace tailWord_808375 prefixEnd_808375 415084924078379962794857 := by
  unfold tailWord_808375
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483858446402909303634579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19655905630935272869089719 29483858446402909303634579)
  ·
    refine ⟨44225787669604363955451869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29483858446402909303634579 44225787669604363955451869)
    ·
      refine ⟨16584670376101636483294451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44225787669604363955451869 16584670376101636483294451)
      ·
        refine ⟨24877005564152454724941677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16584670376101636483294451 24877005564152454724941677)
        ·
          refine ⟨9328877086557170521853129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24877005564152454724941677 9328877086557170521853129)
          ·
            refine ⟨6996657814917877891389847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9328877086557170521853129 6996657814917877891389847)
            ·
              refine ⟨10494986722376816837084771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996657814917877891389847 10494986722376816837084771)
              ·
                refine ⟨15742480083565225255627157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494986722376816837084771 15742480083565225255627157)
                ·
                  refine ⟨737928753917119933857523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15742480083565225255627157 737928753917119933857523)
                  ·
                    refine ⟨1106893130875679900786285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737928753917119933857523 1106893130875679900786285)
                    ·
                      refine ⟨415084924078379962794857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106893130875679900786285 415084924078379962794857)
                      ·
                        rfl

theorem cell23_808375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_808375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808375 prefixEnd_808375 := by exact prefixLift 808375
  have htrace : WordTrace (prefixWord ++ tailWord_808375) baseStart_808375 baseEnd_808375 := by
    simpa [prefixWord, tailWord_808375, baseEnd_808375] using wordTrace_append hprefix tailTrace_808375
  have hstable : (prefixWord ++ tailWord_808375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808375).length < 2 ^ (prefixWord ++ tailWord_808375).sum := by decide
  have hdescent : baseEnd_808375 < baseStart_808375 := by decide
  rcases family_descends (prefixWord ++ tailWord_808375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808392 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_808392 : Nat := 118140960795 + 808392 * 2 ^ 59
def prefixEnd_808392 : Nat := 4983230072969 + 3 ^ 40 * 808392 * 2
def baseEnd_808392 : Nat := 415093653249506396282279

theorem tailTrace_808392 : CollatzResearch.WordTrace tailWord_808392 prefixEnd_808392 415093653249506396282279 := by
  unfold tailWord_808392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742239243670660603501715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19656318991560880804668953 14742239243670660603501715)
  ·
    refine ⟨22113358865505990905252573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14742239243670660603501715 22113358865505990905252573)
    ·
      refine ⟨8292509574564746589469715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22113358865505990905252573 8292509574564746589469715)
      ·
        refine ⟨12438764361847119884204573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292509574564746589469715 12438764361847119884204573)
        ·
          refine ⟨4664536635692669956576715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12438764361847119884204573 4664536635692669956576715)
          ·
            refine ⟨6996804953539004934865073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664536635692669956576715 6996804953539004934865073)
            ·
              refine ⟨5247603715154253701148805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6996804953539004934865073 5247603715154253701148805)
              ·
                refine ⟨983925696591422568965401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5247603715154253701148805 983925696591422568965401)
                ·
                  refine ⟨737944272443566926724051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983925696591422568965401 737944272443566926724051)
                  ·
                    refine ⟨1106916408665350390086077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737944272443566926724051 1106916408665350390086077)
                    ·
                      refine ⟨415093653249506396282279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106916408665350390086077 415093653249506396282279)
                      ·
                        rfl

theorem cell23_808392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_808392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808392 prefixEnd_808392 := by exact prefixLift 808392
  have htrace : WordTrace (prefixWord ++ tailWord_808392) baseStart_808392 baseEnd_808392 := by
    simpa [prefixWord, tailWord_808392, baseEnd_808392] using wordTrace_append hprefix tailTrace_808392
  have hstable : (prefixWord ++ tailWord_808392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808392).length < 2 ^ (prefixWord ++ tailWord_808392).sum := by decide
  have hdescent : baseEnd_808392 < baseStart_808392 := by decide
  rcases family_descends (prefixWord ++ tailWord_808392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808408 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 2, 6]
def baseStart_808408 : Nat := 118140960795 + 808408 * 2 ^ 59
def prefixEnd_808408 : Nat := 4983230072969 + 3 ^ 40 * 808408 * 2
def baseEnd_808408 : Nat := 138367289646659444560735

theorem tailTrace_808408 : CollatzResearch.WordTrace tailWord_808408 prefixEnd_808408 138367289646659444560735 := by
  unfold tailWord_808408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742531027641677969792939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19656708036855570626390585 14742531027641677969792939)
  ·
    refine ⟨22113796541462516954689409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14742531027641677969792939 22113796541462516954689409)
    ·
      refine ⟨16585347406096887716017057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22113796541462516954689409 16585347406096887716017057)
      ·
        refine ⟨12439010554572665787012793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16585347406096887716017057 12439010554572665787012793)
        ·
          refine ⟨9329257915929499340259595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12439010554572665787012793 9329257915929499340259595)
          ·
            refine ⟨13993886873894249010389393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329257915929499340259595 13993886873894249010389393)
            ·
              refine ⟨10495415155420686757792045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13993886873894249010389393 10495415155420686757792045)
              ·
                refine ⟨3935780683282757534172017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10495415155420686757792045 3935780683282757534172017)
                ·
                  refine ⟨2951835512462068150629013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935780683282757534172017 2951835512462068150629013)
                  ·
                    refine ⟨138367289646659444560735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2951835512462068150629013 138367289646659444560735)
                    ·
                      rfl

theorem cell23_808408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_808408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808408 prefixEnd_808408 := by exact prefixLift 808408
  have htrace : WordTrace (prefixWord ++ tailWord_808408) baseStart_808408 baseEnd_808408 := by
    simpa [prefixWord, tailWord_808408, baseEnd_808408] using wordTrace_append hprefix tailTrace_808408
  have hstable : (prefixWord ++ tailWord_808408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808408).length < 2 ^ (prefixWord ++ tailWord_808408).sum := by decide
  have hdescent : baseEnd_808408 < baseStart_808408 := by decide
  rcases family_descends (prefixWord ++ tailWord_808408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808409 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 2, 1, 3]
def baseStart_808409 : Nat := 118140960795 + 808409 * 2 ^ 59
def prefixEnd_808409 : Nat := 4983230072969 + 3 ^ 40 * 808409 * 2
def baseEnd_808409 : Nat := 415102382420632829769701

theorem tailTrace_808409 : CollatzResearch.WordTrace tailWord_808409 prefixEnd_808409 415102382420632829769701 := by
  unfold tailWord_808409
  simp only [CollatzResearch.WordTrace]
  refine ⟨29485098528279733110372281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19656732352186488740248187 29485098528279733110372281)
  ·
    refine ⟨22113823896209799832779211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29485098528279733110372281 22113823896209799832779211)
    ·
      refine ⟨33170735844314699749168817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22113823896209799832779211 33170735844314699749168817)
      ·
        refine ⟨24878051883236024811876613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33170735844314699749168817 24878051883236024811876613)
        ·
          refine ⟨4664634728106754652226865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24878051883236024811876613 4664634728106754652226865)
          ·
            refine ⟨3498476046080065989170149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4664634728106754652226865 3498476046080065989170149)
            ·
              refine ⟨655964258640012372969403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3498476046080065989170149 655964258640012372969403)
              ·
                refine ⟨983946387960018559454105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655964258640012372969403 983946387960018559454105)
                ·
                  refine ⟨737959790970013919590579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983946387960018559454105 737959790970013919590579)
                  ·
                    refine ⟨1106939686455020879385869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737959790970013919590579 1106939686455020879385869)
                    ·
                      refine ⟨415102382420632829769701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1106939686455020879385869 415102382420632829769701)
                      ·
                        rfl

theorem cell23_808409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_808409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808409 prefixEnd_808409 := by exact prefixLift 808409
  have htrace : WordTrace (prefixWord ++ tailWord_808409) baseStart_808409 baseEnd_808409 := by
    simpa [prefixWord, tailWord_808409, baseEnd_808409] using wordTrace_append hprefix tailTrace_808409
  have hstable : (prefixWord ++ tailWord_808409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808409).length < 2 ^ (prefixWord ++ tailWord_808409).sum := by decide
  have hdescent : baseEnd_808409 < baseStart_808409 := by decide
  rcases family_descends (prefixWord ++ tailWord_808409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808419 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 1, 3, 2]
def baseStart_808419 : Nat := 118140960795 + 808419 * 2 ^ 59
def prefixEnd_808419 : Nat := 4983230072969 + 3 ^ 40 * 808419 * 2
def baseEnd_808419 : Nat := 415107517227177790644655

theorem tailTrace_808419 : CollatzResearch.WordTrace tailWord_808419 prefixEnd_808419 415107517227177790644655 := by
  unfold tailWord_808419
  simp only [CollatzResearch.WordTrace]
  refine ⟨29485463258243504818236311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19656975505495669878824207 29485463258243504818236311)
  ·
    refine ⟨44228194887365257227354467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29485463258243504818236311 44228194887365257227354467)
    ·
      refine ⟨66342292331047885841031701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44228194887365257227354467 66342292331047885841031701)
      ·
        refine ⟨3109794953017869648798361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66342292331047885841031701 3109794953017869648798361)
        ·
          refine ⟨2332346214763402236598771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109794953017869648798361 2332346214763402236598771)
          ·
            refine ⟨3498519322145103354898157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332346214763402236598771 3498519322145103354898157)
            ·
              refine ⟨1311944745804413758086809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3498519322145103354898157 1311944745804413758086809)
              ·
                refine ⟨983958559353310318565107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311944745804413758086809 983958559353310318565107)
                ·
                  refine ⟨1475937839029965477847661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983958559353310318565107 1475937839029965477847661)
                  ·
                    refine ⟨553476689636237054192873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475937839029965477847661 553476689636237054192873)
                    ·
                      refine ⟨415107517227177790644655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553476689636237054192873 415107517227177790644655)
                      ·
                        rfl

theorem cell23_808419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_808419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808419 prefixEnd_808419 := by exact prefixLift 808419
  have htrace : WordTrace (prefixWord ++ tailWord_808419) baseStart_808419 baseEnd_808419 := by
    simpa [prefixWord, tailWord_808419, baseEnd_808419] using wordTrace_append hprefix tailTrace_808419
  have hstable : (prefixWord ++ tailWord_808419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808419).length < 2 ^ (prefixWord ++ tailWord_808419).sum := by decide
  have hdescent : baseEnd_808419 < baseStart_808419 := by decide
  rcases family_descends (prefixWord ++ tailWord_808419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808428 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_808428 : Nat := 118140960795 + 808428 * 2 ^ 59
def prefixEnd_808428 : Nat := 4983230072969 + 3 ^ 40 * 808428 * 2
def baseEnd_808428 : Nat := 415112138553068255432113

theorem tailTrace_808428 : CollatzResearch.WordTrace tailWord_808428 prefixEnd_808428 415112138553068255432113 := by
  unfold tailWord_808428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742895757605449677656969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19657194343473932903542625 14742895757605449677656969)
  ·
    refine ⟨11057171818204087258242727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14742895757605449677656969 11057171818204087258242727)
    ·
      refine ⟨16585757727306130887364091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057171818204087258242727 16585757727306130887364091)
      ·
        refine ⟨24878636590959196331046137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16585757727306130887364091 24878636590959196331046137)
        ·
          refine ⟨18658977443219397248284603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24878636590959196331046137 18658977443219397248284603)
          ·
            refine ⟨27988466164829095872426905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18658977443219397248284603 27988466164829095872426905)
            ·
              refine ⟨20991349623621821904320179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27988466164829095872426905 20991349623621821904320179)
              ·
                refine ⟨31487024435432732856480269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20991349623621821904320179 31487024435432732856480269)
                ·
                  refine ⟨11807634163287274821180101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31487024435432732856480269 11807634163287274821180101)
                  ·
                    refine ⟨2213931405616364028971269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11807634163287274821180101 2213931405616364028971269)
                    ·
                      refine ⟨415112138553068255432113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2213931405616364028971269 415112138553068255432113)
                      ·
                        rfl

theorem cell23_808428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_808428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808428 prefixEnd_808428 := by exact prefixLift 808428
  have htrace : WordTrace (prefixWord ++ tailWord_808428) baseStart_808428 baseEnd_808428 := by
    simpa [prefixWord, tailWord_808428, baseEnd_808428] using wordTrace_append hprefix tailTrace_808428
  have hstable : (prefixWord ++ tailWord_808428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808428).length < 2 ^ (prefixWord ++ tailWord_808428).sum := by decide
  have hdescent : baseEnd_808428 < baseStart_808428 := by decide
  rcases family_descends (prefixWord ++ tailWord_808428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808432 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2]
def baseStart_808432 : Nat := 118140960795 + 808432 * 2 ^ 59
def prefixEnd_808432 : Nat := 4983230072969 + 3 ^ 40 * 808432 * 2
def baseEnd_808432 : Nat := 415114192475686239782095

theorem tailTrace_808432 : CollatzResearch.WordTrace tailWord_808432 prefixEnd_808432 415114192475686239782095 := by
  unfold tailWord_808432
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742968703598204019229775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19657291604797605358973033 14742968703598204019229775)
  ·
    refine ⟨22114453055397306028844663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14742968703598204019229775 22114453055397306028844663)
    ·
      refine ⟨33171679583095959043266995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22114453055397306028844663 33171679583095959043266995)
      ·
        refine ⟨49757519374643938564900493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33171679583095959043266995 49757519374643938564900493)
        ·
          refine ⟨18659069765491476961837685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49757519374643938564900493 18659069765491476961837685)
          ·
            refine ⟨1749287790514825965172283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18659069765491476961837685 1749287790514825965172283)
            ·
              refine ⟨2623931685772238947758425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749287790514825965172283 2623931685772238947758425)
              ·
                refine ⟨1967948764329179210818819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623931685772238947758425 1967948764329179210818819)
                ·
                  refine ⟨2951923146493768816228229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967948764329179210818819 2951923146493768816228229)
                  ·
                    refine ⟨553485589967581653042793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2951923146493768816228229 553485589967581653042793)
                    ·
                      refine ⟨415114192475686239782095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553485589967581653042793 415114192475686239782095)
                      ·
                        rfl

theorem cell23_808432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2].length) (baseStart_808432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808432 prefixEnd_808432 := by exact prefixLift 808432
  have htrace : WordTrace (prefixWord ++ tailWord_808432) baseStart_808432 baseEnd_808432 := by
    simpa [prefixWord, tailWord_808432, baseEnd_808432] using wordTrace_append hprefix tailTrace_808432
  have hstable : (prefixWord ++ tailWord_808432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808432).length < 2 ^ (prefixWord ++ tailWord_808432).sum := by decide
  have hdescent : baseEnd_808432 < baseStart_808432 := by decide
  rcases family_descends (prefixWord ++ tailWord_808432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808462 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_808462 : Nat := 118140960795 + 808462 * 2 ^ 59
def prefixEnd_808462 : Nat := 4983230072969 + 3 ^ 40 * 808462 * 2
def baseEnd_808462 : Nat := 415129596895321122406957

theorem tailTrace_808462 : CollatzResearch.WordTrace tailWord_808462 prefixEnd_808462 415129596895321122406957 := by
  unfold tailWord_808462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685878949635965395256455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19658021064725148774701093 3685878949635965395256455)
  ·
    refine ⟨5528818424453948092884683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685878949635965395256455 5528818424453948092884683)
    ·
      refine ⟨8293227636680922139327025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528818424453948092884683 8293227636680922139327025)
      ·
        refine ⟨6219920727510691604495269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8293227636680922139327025 6219920727510691604495269)
        ·
          refine ⟨1166235136408254675842863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6219920727510691604495269 1166235136408254675842863)
          ·
            refine ⟨1749352704612382013764295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166235136408254675842863 1749352704612382013764295)
            ·
              refine ⟨2624029056918573020646443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749352704612382013764295 2624029056918573020646443)
              ·
                refine ⟨3936043585377859530969665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624029056918573020646443 3936043585377859530969665)
                ·
                  refine ⟨2952032689033394648227249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936043585377859530969665 2952032689033394648227249)
                  ·
                    refine ⟨2214024516775045986170437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2952032689033394648227249 2214024516775045986170437)
                    ·
                      refine ⟨415129596895321122406957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2214024516775045986170437 415129596895321122406957)
                      ·
                        rfl

theorem cell23_808462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_808462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808462 prefixEnd_808462 := by exact prefixLift 808462
  have htrace : WordTrace (prefixWord ++ tailWord_808462) baseStart_808462 baseEnd_808462 := by
    simpa [prefixWord, tailWord_808462, baseEnd_808462] using wordTrace_append hprefix tailTrace_808462
  have hstable : (prefixWord ++ tailWord_808462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808462).length < 2 ^ (prefixWord ++ tailWord_808462).sum := by decide
  have hdescent : baseEnd_808462 < baseStart_808462 := by decide
  rcases family_descends (prefixWord ++ tailWord_808462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808465 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_808465 : Nat := 118140960795 + 808465 * 2 ^ 59
def prefixEnd_808465 : Nat := 4983230072969 + 3 ^ 40 * 808465 * 2
def baseEnd_808465 : Nat := 415131137337284610669443

theorem tailTrace_808465 : CollatzResearch.WordTrace tailWord_808465 prefixEnd_808465 415131137337284610669443 := by
  unfold tailWord_808465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29487141016076854674410849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19658094010717903116273899 29487141016076854674410849)
  ·
    refine ⟨22115355762057641005808137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29487141016076854674410849 22115355762057641005808137)
    ·
      refine ⟨16586516821543230754356103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22115355762057641005808137 16586516821543230754356103)
      ·
        refine ⟨24879775232314846131534155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16586516821543230754356103 24879775232314846131534155)
        ·
          refine ⟨37319662848472269197301233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24879775232314846131534155 37319662848472269197301233)
          ·
            refine ⟨27989747136354201897975925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37319662848472269197301233 27989747136354201897975925)
            ·
              refine ⟨2624038794033206427935243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27989747136354201897975925 2624038794033206427935243)
              ·
                refine ⟨3936058191049809641902865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624038794033206427935243 3936058191049809641902865)
                ·
                  refine ⟨2952043643287357231427149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936058191049809641902865 2952043643287357231427149)
                  ·
                    refine ⟨1107016366232758961785181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952043643287357231427149 1107016366232758961785181)
                    ·
                      refine ⟨415131137337284610669443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1107016366232758961785181 415131137337284610669443)
                      ·
                        rfl

theorem cell23_808465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_808465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808465 prefixEnd_808465 := by exact prefixLift 808465
  have htrace : WordTrace (prefixWord ++ tailWord_808465) baseStart_808465 baseEnd_808465 := by
    simpa [prefixWord, tailWord_808465, baseEnd_808465] using wordTrace_append hprefix tailTrace_808465
  have hstable : (prefixWord ++ tailWord_808465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808465).length < 2 ^ (prefixWord ++ tailWord_808465).sum := by decide
  have hdescent : baseEnd_808465 < baseStart_808465 := by decide
  rcases family_descends (prefixWord ++ tailWord_808465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808522 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_808522 : Nat := 118140960795 + 808522 * 2 ^ 59
def prefixEnd_808522 : Nat := 4983230072969 + 3 ^ 40 * 808522 * 2
def baseEnd_808522 : Nat := 415160405734590887656681

theorem tailTrace_808522 : CollatzResearch.WordTrace tailWord_808522 prefixEnd_808522 415160405734590887656681 := by
  unfold tailWord_808522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372304994217588352308955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19659479984580235606157213 7372304994217588352308955)
  ·
    refine ⟨11058457491326382528463433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7372304994217588352308955 11058457491326382528463433)
    ·
      refine ⟨8293843118494786896347575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11058457491326382528463433 8293843118494786896347575)
      ·
        refine ⟨12440764677742180344521363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8293843118494786896347575 12440764677742180344521363)
        ·
          refine ⟨18661147016613270516782045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12440764677742180344521363 18661147016613270516782045)
          ·
            refine ⟨6997930131229976443793267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18661147016613270516782045 6997930131229976443793267)
            ·
              refine ⟨10496895196844964665689901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997930131229976443793267 10496895196844964665689901)
              ·
                refine ⟨3936335698816861749633713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10496895196844964665689901 3936335698816861749633713)
                ·
                  refine ⟨2952251774112646312225285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936335698816861749633713 2952251774112646312225285)
                  ·
                    refine ⟨553547207646121183542241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952251774112646312225285 553547207646121183542241)
                    ·
                      refine ⟨415160405734590887656681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553547207646121183542241 415160405734590887656681)
                      ·
                        rfl

theorem cell23_808522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_808522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808522 prefixEnd_808522 := by exact prefixLift 808522
  have htrace : WordTrace (prefixWord ++ tailWord_808522) baseStart_808522 baseEnd_808522 := by
    simpa [prefixWord, tailWord_808522, baseEnd_808522] using wordTrace_append hprefix tailTrace_808522
  have hstable : (prefixWord ++ tailWord_808522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808522).length < 2 ^ (prefixWord ++ tailWord_808522).sum := by decide
  have hdescent : baseEnd_808522 < baseStart_808522 := by decide
  rcases family_descends (prefixWord ++ tailWord_808522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808532 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_808532 : Nat := 118140960795 + 808532 * 2 ^ 59
def prefixEnd_808532 : Nat := 4983230072969 + 3 ^ 40 * 808532 * 2
def baseEnd_808532 : Nat := 138388513513711949510545

theorem tailTrace_808532 : CollatzResearch.WordTrace tailWord_808532 prefixEnd_808532 138388513513711949510545 := by
  unfold tailWord_808532
  simp only [CollatzResearch.WordTrace]
  refine ⟨14744792353417062558549925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19659723137889416744733233 14744792353417062558549925)
  ·
    refine ⟨2764648566265699229728111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14744792353417062558549925 2764648566265699229728111)
    ·
      refine ⟨4146972849398548844592167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764648566265699229728111 4146972849398548844592167)
      ·
        refine ⟨6220459274097823266888251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146972849398548844592167 6220459274097823266888251)
        ·
          refine ⟨9330688911146734900332377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220459274097823266888251 9330688911146734900332377)
          ·
            refine ⟨6998016683360051175249283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9330688911146734900332377 6998016683360051175249283)
            ·
              refine ⟨10497025025040076762873925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998016683360051175249283 10497025025040076762873925)
              ·
                refine ⟨1968192192195014393038861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10497025025040076762873925 1968192192195014393038861)
                ·
                  refine ⟨738072072073130397389573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1968192192195014393038861 738072072073130397389573)
                  ·
                    refine ⟨138388513513711949510545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 738072072073130397389573 138388513513711949510545)
                    ·
                      rfl

theorem cell23_808532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_808532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808532 prefixEnd_808532 := by exact prefixLift 808532
  have htrace : WordTrace (prefixWord ++ tailWord_808532) baseStart_808532 baseEnd_808532 := by
    simpa [prefixWord, tailWord_808532, baseEnd_808532] using wordTrace_append hprefix tailTrace_808532
  have hstable : (prefixWord ++ tailWord_808532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808532).length < 2 ^ (prefixWord ++ tailWord_808532).sum := by decide
  have hdescent : baseEnd_808532 < baseStart_808532 := by decide
  rcases family_descends (prefixWord ++ tailWord_808532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808566 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_808566 : Nat := 118140960795 + 808566 * 2 ^ 59
def prefixEnd_808566 : Nat := 4983230072969 + 3 ^ 40 * 808566 * 2
def baseEnd_808566 : Nat := 138394332961129571835493

theorem tailTrace_808566 : CollatzResearch.WordTrace tailWord_808566 prefixEnd_808566 138394332961129571835493 := by
  unfold tailWord_808566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843176549294434307739847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19660549859140632615891701 1843176549294434307739847)
  ·
    refine ⟨2764764823941651461609771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1843176549294434307739847 2764764823941651461609771)
    ·
      refine ⟨4147147235912477192414657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764764823941651461609771 4147147235912477192414657)
      ·
        refine ⟨3110360426934357894310993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4147147235912477192414657 3110360426934357894310993)
        ·
          refine ⟨2332770320200768420733245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3110360426934357894310993 2332770320200768420733245)
          ·
            refine ⟨874788870075288157774967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2332770320200768420733245 874788870075288157774967)
            ·
              refine ⟨1312183305112932236662451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874788870075288157774967 1312183305112932236662451)
              ·
                refine ⟨1968274957669398354993677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312183305112932236662451 1968274957669398354993677)
                ·
                  refine ⟨738103109126024383122629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1968274957669398354993677 738103109126024383122629)
                  ·
                    refine ⟨138394332961129571835493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 738103109126024383122629 138394332961129571835493)
                    ·
                      rfl

theorem cell23_808566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_808566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808566 prefixEnd_808566 := by exact prefixLift 808566
  have htrace : WordTrace (prefixWord ++ tailWord_808566) baseStart_808566 baseEnd_808566 := by
    simpa [prefixWord, tailWord_808566, baseEnd_808566] using wordTrace_append hprefix tailTrace_808566
  have hstable : (prefixWord ++ tailWord_808566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808566).length < 2 ^ (prefixWord ++ tailWord_808566).sum := by decide
  have hdescent : baseEnd_808566 < baseStart_808566 := by decide
  rcases family_descends (prefixWord ++ tailWord_808566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808599 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_808599 : Nat := 118140960795 + 808599 * 2 ^ 59
def prefixEnd_808599 : Nat := 4983230072969 + 3 ^ 40 * 808599 * 2
def baseEnd_808599 : Nat := 415199943744987086393827

theorem tailTrace_808599 : CollatzResearch.WordTrace tailWord_808599 prefixEnd_808599 415199943744987086393827 := by
  unfold tailWord_808599
  simp only [CollatzResearch.WordTrace]
  refine ⟨29492028397591395559788851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19661352265060930373192567 29492028397591395559788851)
  ·
    refine ⟨44238042596387093339683277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29492028397591395559788851 44238042596387093339683277)
    ·
      refine ⟨16589265973645160002381229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44238042596387093339683277 16589265973645160002381229)
      ·
        refine ⟨6220974740116935000892961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16589265973645160002381229 6220974740116935000892961)
        ·
          refine ⟨4665731055087701250669721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6220974740116935000892961 4665731055087701250669721)
          ·
            refine ⟨3499298291315775938002291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665731055087701250669721 3499298291315775938002291)
            ·
              refine ⟨5248947436973663907003437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499298291315775938002291 5248947436973663907003437)
              ·
                refine ⟨1968355288865123965126289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5248947436973663907003437 1968355288865123965126289)
                ·
                  refine ⟨1476266466648842973844717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1968355288865123965126289 1476266466648842973844717)
                  ·
                    refine ⟨553599924993316115191769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476266466648842973844717 553599924993316115191769)
                    ·
                      refine ⟨415199943744987086393827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553599924993316115191769 415199943744987086393827)
                      ·
                        rfl

theorem cell23_808599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_808599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808599 prefixEnd_808599 := by exact prefixLift 808599
  have htrace : WordTrace (prefixWord ++ tailWord_808599) baseStart_808599 baseEnd_808599 := by
    simpa [prefixWord, tailWord_808599, baseEnd_808599] using wordTrace_append hprefix tailTrace_808599
  have hstable : (prefixWord ++ tailWord_808599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808599).length < 2 ^ (prefixWord ++ tailWord_808599).sum := by decide
  have hdescent : baseEnd_808599 < baseStart_808599 := by decide
  rcases family_descends (prefixWord ++ tailWord_808599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808663 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 1, 2, 2]
def baseStart_808663 : Nat := 118140960795 + 808663 * 2 ^ 59
def prefixEnd_808663 : Nat := 4983230072969 + 3 ^ 40 * 808663 * 2
def baseEnd_808663 : Nat := 415232806506874835993533

theorem tailTrace_808663 : CollatzResearch.WordTrace tailWord_808663 prefixEnd_808663 415232806506874835993533 := by
  unfold tailWord_808663
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494362669359534490118643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19662908446239689660079095 29494362669359534490118643)
  ·
    refine ⟨44241544004039301735177965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29494362669359534490118643 44241544004039301735177965)
    ·
      refine ⟨16590579001514738150691737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44241544004039301735177965 16590579001514738150691737)
      ·
        refine ⟨12442934251136053613018803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16590579001514738150691737 12442934251136053613018803)
        ·
          refine ⟨18664401376704080419528205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12442934251136053613018803 18664401376704080419528205)
          ·
            refine ⟨6999150516264030157323077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18664401376704080419528205 6999150516264030157323077)
            ·
              refine ⟨1312340721799505654498077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6999150516264030157323077 1312340721799505654498077)
              ·
                refine ⟨492127770674814620436779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312340721799505654498077 492127770674814620436779)
                ·
                  refine ⟨738191656012221930655169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492127770674814620436779 738191656012221930655169)
                  ·
                    refine ⟨553643742009166447991377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738191656012221930655169 553643742009166447991377)
                    ·
                      refine ⟨415232806506874835993533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553643742009166447991377 415232806506874835993533)
                      ·
                        rfl

theorem cell23_808663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_808663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808663 prefixEnd_808663 := by exact prefixLift 808663
  have htrace : WordTrace (prefixWord ++ tailWord_808663) baseStart_808663 baseEnd_808663 := by
    simpa [prefixWord, tailWord_808663, baseEnd_808663] using wordTrace_append hprefix tailTrace_808663
  have hstable : (prefixWord ++ tailWord_808663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808663).length < 2 ^ (prefixWord ++ tailWord_808663).sum := by decide
  have hdescent : baseEnd_808663 < baseStart_808663 := by decide
  rcases family_descends (prefixWord ++ tailWord_808663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808666 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_808666 : Nat := 118140960795 + 808666 * 2 ^ 59
def prefixEnd_808666 : Nat := 4983230072969 + 3 ^ 40 * 808666 * 2
def baseEnd_808666 : Nat := 415234346948838324256019

theorem tailTrace_808666 : CollatzResearch.WordTrace tailWord_808666 prefixEnd_808666 415234346948838324256019 := by
  unfold tailWord_808666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7373618022087166500619463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19662981392232444001651901 7373618022087166500619463)
  ·
    refine ⟨11060427033130749750929195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7373618022087166500619463 11060427033130749750929195)
    ·
      refine ⟨16590640549696124626393793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11060427033130749750929195 16590640549696124626393793)
      ·
        refine ⟨12442980412272093469795345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16590640549696124626393793 12442980412272093469795345)
        ·
          refine ⟨9332235309204070102346509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12442980412272093469795345 9332235309204070102346509)
          ·
            refine ⟨3499588240951526288379941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9332235309204070102346509 3499588240951526288379941)
            ·
              refine ⟨656172795178411179071239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3499588240951526288379941 656172795178411179071239)
              ·
                refine ⟨984259192767616768606859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656172795178411179071239 984259192767616768606859)
                ·
                  refine ⟨1476388789151425152910289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984259192767616768606859 1476388789151425152910289)
                  ·
                    refine ⟨1107291591863568864682717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476388789151425152910289 1107291591863568864682717)
                    ·
                      refine ⟨415234346948838324256019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1107291591863568864682717 415234346948838324256019)
                      ·
                        rfl

theorem cell23_808666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_808666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808666 prefixEnd_808666 := by exact prefixLift 808666
  have htrace : WordTrace (prefixWord ++ tailWord_808666) baseStart_808666 baseEnd_808666 := by
    simpa [prefixWord, tailWord_808666, baseEnd_808666] using wordTrace_append hprefix tailTrace_808666
  have hstable : (prefixWord ++ tailWord_808666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808666).length < 2 ^ (prefixWord ++ tailWord_808666).sum := by decide
  have hdescent : baseEnd_808666 < baseStart_808666 := by decide
  rcases family_descends (prefixWord ++ tailWord_808666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808669 : List Nat := [1, 4, 3, 3, 1, 1, 10]
def baseStart_808669 : Nat := 118140960795 + 808669 * 2 ^ 59
def prefixEnd_808669 : Nat := 4983230072969 + 3 ^ 40 * 808669 * 2
def baseEnd_808669 : Nat := 5126368980133355710105

theorem tailTrace_808669 : CollatzResearch.WordTrace tailWord_808669 prefixEnd_808669 5126368980133355710105 := by
  unfold tailWord_808669
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494581507337797514837061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19663054338225198343224707 29494581507337797514837061)
  ·
    refine ⟨5530234032625837034031949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29494581507337797514837061 5530234032625837034031949)
    ·
      refine ⟨2073837762234688887761981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5530234032625837034031949 2073837762234688887761981)
      ·
        refine ⟨777689160838008332910743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2073837762234688887761981 777689160838008332910743)
        ·
          refine ⟨1166533741257012499366115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777689160838008332910743 1166533741257012499366115)
          ·
            refine ⟨1749800611885518749049173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166533741257012499366115 1749800611885518749049173)
            ·
              refine ⟨5126368980133355710105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1749800611885518749049173 5126368980133355710105)
              ·
                rfl

theorem cell23_808669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 10].length) (baseStart_808669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808669 prefixEnd_808669 := by exact prefixLift 808669
  have htrace : WordTrace (prefixWord ++ tailWord_808669) baseStart_808669 baseEnd_808669 := by
    simpa [prefixWord, tailWord_808669, baseEnd_808669] using wordTrace_append hprefix tailTrace_808669
  have hstable : (prefixWord ++ tailWord_808669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808669).length < 2 ^ (prefixWord ++ tailWord_808669).sum := by decide
  have hdescent : baseEnd_808669 < baseStart_808669 := by decide
  rcases family_descends (prefixWord ++ tailWord_808669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808673 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 2, 4]
def baseStart_808673 : Nat := 118140960795 + 808673 * 2 ^ 59
def prefixEnd_808673 : Nat := 4983230072969 + 3 ^ 40 * 808673 * 2
def baseEnd_808673 : Nat := 138412647104473265622829

theorem tailTrace_808673 : CollatzResearch.WordTrace tailWord_808673 prefixEnd_808673 138412647104473265622829 := by
  unfold tailWord_808673
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494727399323306197982673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19663151599548870798655115 29494727399323306197982673)
  ·
    refine ⟨22121045549492479648487005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29494727399323306197982673 22121045549492479648487005)
    ·
      refine ⟨8295392081059679868182627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22121045549492479648487005 8295392081059679868182627)
      ·
        refine ⟨12443088121589519802273941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8295392081059679868182627 12443088121589519802273941)
        ·
          refine ⟨583269755699508740731591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12443088121589519802273941 583269755699508740731591)
          ·
            refine ⟨874904633549263111097387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583269755699508740731591 874904633549263111097387)
            ·
              refine ⟨1312356950323894666646081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874904633549263111097387 1312356950323894666646081)
              ·
                refine ⟨984267712742920999984561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312356950323894666646081 984267712742920999984561)
                ·
                  refine ⟨738200784557190749988421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 984267712742920999984561 738200784557190749988421)
                  ·
                    refine ⟨138412647104473265622829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 738200784557190749988421 138412647104473265622829)
                    ·
                      rfl

theorem cell23_808673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_808673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808673 prefixEnd_808673 := by exact prefixLift 808673
  have htrace : WordTrace (prefixWord ++ tailWord_808673) baseStart_808673 baseEnd_808673 := by
    simpa [prefixWord, tailWord_808673, baseEnd_808673] using wordTrace_append hprefix tailTrace_808673
  have hstable : (prefixWord ++ tailWord_808673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808673).length < 2 ^ (prefixWord ++ tailWord_808673).sum := by decide
  have hdescent : baseEnd_808673 < baseStart_808673 := by decide
  rcases family_descends (prefixWord ++ tailWord_808673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808736 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2]
def baseStart_808736 : Nat := 118140960795 + 808736 * 2 ^ 59
def prefixEnd_808736 : Nat := 4983230072969 + 3 ^ 40 * 808736 * 2
def baseEnd_808736 : Nat := 415270290594653050380697

theorem tailTrace_808736 : CollatzResearch.WordTrace tailWord_808736 prefixEnd_808736 415270290594653050380697 := by
  unfold tailWord_808736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748512599047533978763031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19664683465396711971684041 14748512599047533978763031)
  ·
    refine ⟨22122768898571300968144547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14748512599047533978763031 22122768898571300968144547)
    ·
      refine ⟨33184153347856951452216821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22122768898571300968144547 33184153347856951452216821)
      ·
        refine ⟨3111014376361589198645327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33184153347856951452216821 3111014376361589198645327)
        ·
          refine ⟨4666521564542383797967991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111014376361589198645327 4666521564542383797967991)
          ·
            refine ⟨6999782346813575696951987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666521564542383797967991 6999782346813575696951987)
            ·
              refine ⟨10499673520220363545427981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999782346813575696951987 10499673520220363545427981)
              ·
                refine ⟨3937377570082636329535493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10499673520220363545427981 3937377570082636329535493)
                ·
                  refine ⟨738258294390494311787905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3937377570082636329535493 738258294390494311787905)
                  ·
                    refine ⟨553693720792870733840929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738258294390494311787905 553693720792870733840929)
                    ·
                      refine ⟨415270290594653050380697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553693720792870733840929 415270290594653050380697)
                      ·
                        rfl

theorem cell23_808736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_808736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808736 prefixEnd_808736 := by exact prefixLift 808736
  have htrace : WordTrace (prefixWord ++ tailWord_808736) baseStart_808736 baseEnd_808736 := by
    simpa [prefixWord, tailWord_808736, baseEnd_808736] using wordTrace_append hprefix tailTrace_808736
  have hstable : (prefixWord ++ tailWord_808736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808736).length < 2 ^ (prefixWord ++ tailWord_808736).sum := by decide
  have hdescent : baseEnd_808736 < baseStart_808736 := by decide
  rcases family_descends (prefixWord ++ tailWord_808736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808753 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_808753 : Nat := 118140960795 + 808753 * 2 ^ 59
def prefixEnd_808753 : Nat := 4983230072969 + 3 ^ 40 * 808753 * 2
def baseEnd_808753 : Nat := 415279019765779483868119

theorem tailTrace_808753 : CollatzResearch.WordTrace tailWord_808753 prefixEnd_808753 415279019765779483868119 := by
  unfold tailWord_808753
  simp only [CollatzResearch.WordTrace]
  refine ⟨29497645239033479860894913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19665096826022319907263275 29497645239033479860894913)
  ·
    refine ⟨22123233929275109895671185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29497645239033479860894913 22123233929275109895671185)
    ·
      refine ⟨16592425446956332421753389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22123233929275109895671185 16592425446956332421753389)
      ·
        refine ⟨6222159542608624658157521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16592425446956332421753389 6222159542608624658157521)
        ·
          refine ⟨4666619656956468493618141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222159542608624658157521 4666619656956468493618141)
          ·
            refine ⟨1749982371358675685106803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4666619656956468493618141 1749982371358675685106803)
            ·
              refine ⟨2624973557038013527660205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749982371358675685106803 2624973557038013527660205)
              ·
                refine ⟨984365083889255072872577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624973557038013527660205 984365083889255072872577)
                ·
                  refine ⟨738273812916941304654433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 984365083889255072872577 738273812916941304654433)
                  ·
                    refine ⟨553705359687705978490825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738273812916941304654433 553705359687705978490825)
                    ·
                      refine ⟨415279019765779483868119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553705359687705978490825 415279019765779483868119)
                      ·
                        rfl

theorem cell23_808753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_808753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808753 prefixEnd_808753 := by exact prefixLift 808753
  have htrace : WordTrace (prefixWord ++ tailWord_808753) baseStart_808753 baseEnd_808753 := by
    simpa [prefixWord, tailWord_808753, baseEnd_808753] using wordTrace_append hprefix tailTrace_808753
  have hstable : (prefixWord ++ tailWord_808753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808753).length < 2 ^ (prefixWord ++ tailWord_808753).sum := by decide
  have hdescent : baseEnd_808753 < baseStart_808753 := by decide
  rcases family_descends (prefixWord ++ tailWord_808753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808789 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_808789 : Nat := 118140960795 + 808789 * 2 ^ 59
def prefixEnd_808789 : Nat := 4983230072969 + 3 ^ 40 * 808789 * 2
def baseEnd_808789 : Nat := 138432501689780447672651

theorem tailTrace_808789 : CollatzResearch.WordTrace tailWord_808789 prefixEnd_808789 138432501689780447672651 := by
  unfold tailWord_808789
  simp only [CollatzResearch.WordTrace]
  refine ⟨29498958266903058009205421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19665972177935372006136947 29498958266903058009205421)
  ·
    refine ⟨11062109350088646753452033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29498958266903058009205421 11062109350088646753452033)
    ·
      refine ⟨8296582012566485065089025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11062109350088646753452033 8296582012566485065089025)
      ·
        refine ⟨6222436509424863798816769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8296582012566485065089025 6222436509424863798816769)
        ·
          refine ⟨4666827382068647849112577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222436509424863798816769 4666827382068647849112577)
          ·
            refine ⟨3500120536551485886834433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4666827382068647849112577 3500120536551485886834433)
            ·
              refine ⟨2625090402413614415125825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500120536551485886834433 2625090402413614415125825)
              ·
                refine ⟨1968817801810210811344369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625090402413614415125825 1968817801810210811344369)
                ·
                  refine ⟨1476613351357658108508277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1968817801810210811344369 1476613351357658108508277)
                  ·
                    refine ⟨138432501689780447672651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1476613351357658108508277 138432501689780447672651)
                    ·
                      rfl

theorem cell23_808789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_808789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808789 prefixEnd_808789 := by exact prefixLift 808789
  have htrace : WordTrace (prefixWord ++ tailWord_808789) baseStart_808789 baseEnd_808789 := by
    simpa [prefixWord, tailWord_808789, baseEnd_808789] using wordTrace_append hprefix tailTrace_808789
  have hstable : (prefixWord ++ tailWord_808789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808789).length < 2 ^ (prefixWord ++ tailWord_808789).sum := by decide
  have hdescent : baseEnd_808789 < baseStart_808789 := by decide
  rcases family_descends (prefixWord ++ tailWord_808789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808792 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_808792 : Nat := 118140960795 + 808792 * 2 ^ 59
def prefixEnd_808792 : Nat := 4983230072969 + 3 ^ 40 * 808792 * 2
def baseEnd_808792 : Nat := 415299045511304831280439

theorem tailTrace_808792 : CollatzResearch.WordTrace tailWord_808792 prefixEnd_808792 415299045511304831280439 := by
  unfold tailWord_808792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14749533842946094760782315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19666045123928126347709753 14749533842946094760782315)
  ·
    refine ⟨22124300764419142141173473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14749533842946094760782315 22124300764419142141173473)
    ·
      refine ⟨16593225573314356605880105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22124300764419142141173473 16593225573314356605880105)
      ·
        refine ⟨12444919179985767454410079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16593225573314356605880105 12444919179985767454410079)
        ·
          refine ⟨18667378769978651181615119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12444919179985767454410079 18667378769978651181615119)
          ·
            refine ⟨28001068154967976772422679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18667378769978651181615119 28001068154967976772422679)
            ·
              refine ⟨42001602232451965158634019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28001068154967976772422679 42001602232451965158634019)
              ·
                refine ⟨63002403348677947737951029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42001602232451965158634019 63002403348677947737951029)
                ·
                  refine ⟨5906475313938557600432909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63002403348677947737951029 5906475313938557600432909)
                  ·
                    refine ⟨2214928242726959100162341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5906475313938557600432909 2214928242726959100162341)
                    ·
                      refine ⟨415299045511304831280439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2214928242726959100162341 415299045511304831280439)
                      ·
                        rfl

theorem cell23_808792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_808792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808792 prefixEnd_808792 := by exact prefixLift 808792
  have htrace : WordTrace (prefixWord ++ tailWord_808792) baseStart_808792 baseEnd_808792 := by
    simpa [prefixWord, tailWord_808792, baseEnd_808792] using wordTrace_append hprefix tailTrace_808792
  have hstable : (prefixWord ++ tailWord_808792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808792).length < 2 ^ (prefixWord ++ tailWord_808792).sum := by decide
  have hdescent : baseEnd_808792 < baseStart_808792 := by decide
  rcases family_descends (prefixWord ++ tailWord_808792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808832 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 8]
def baseStart_808832 : Nat := 118140960795 + 808832 * 2 ^ 59
def prefixEnd_808832 : Nat := 4983230072969 + 3 ^ 40 * 808832 * 2
def baseEnd_808832 : Nat := 46146620526387186086695

theorem tailTrace_808832 : CollatzResearch.WordTrace tailWord_808832 prefixEnd_808832 46146620526387186086695 := by
  unfold tailWord_808832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750263302873638176510375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19667017737164850902013833 14750263302873638176510375)
  ·
    refine ⟨22125394954310457264765563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14750263302873638176510375 22125394954310457264765563)
    ·
      refine ⟨33188092431465685897148345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22125394954310457264765563 33188092431465685897148345)
      ·
        refine ⟨24891069323599264422861259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33188092431465685897148345 24891069323599264422861259)
        ·
          refine ⟨37336603985398896634291889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24891069323599264422861259 37336603985398896634291889)
          ·
            refine ⟨28002452989049172475718917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37336603985398896634291889 28002452989049172475718917)
            ·
              refine ⟨5250459935446719839197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28002452989049172475718917 5250459935446719839197297)
              ·
                refine ⟨3937844951585039879397973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5250459935446719839197297 3937844951585039879397973)
                ·
                  refine ⟨46146620526387186086695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3937844951585039879397973 46146620526387186086695)
                  ·
                    rfl

theorem cell23_808832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_808832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808832 prefixEnd_808832 := by exact prefixLift 808832
  have htrace : WordTrace (prefixWord ++ tailWord_808832) baseStart_808832 baseEnd_808832 := by
    simpa [prefixWord, tailWord_808832, baseEnd_808832] using wordTrace_append hprefix tailTrace_808832
  have hstable : (prefixWord ++ tailWord_808832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808832).length < 2 ^ (prefixWord ++ tailWord_808832).sum := by decide
  have hdescent : baseEnd_808832 < baseStart_808832 := by decide
  rcases family_descends (prefixWord ++ tailWord_808832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808849 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 6]
def baseStart_808849 : Nat := 118140960795 + 808849 * 2 ^ 59
def prefixEnd_808849 : Nat := 4983230072969 + 3 ^ 40 * 808849 * 2
def baseEnd_808849 : Nat := 46147590434290123140853

theorem tailTrace_808849 : CollatzResearch.WordTrace tailWord_808849 prefixEnd_808849 46147590434290123140853 := by
  unfold tailWord_808849
  simp only [CollatzResearch.WordTrace]
  refine ⟨29501146646685688256389601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19667431097790458837593067 29501146646685688256389601)
  ·
    refine ⟨22125859985014266192292201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29501146646685688256389601 22125859985014266192292201)
    ·
      refine ⟨16594394988760699644219151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22125859985014266192292201 16594394988760699644219151)
      ·
        refine ⟨24891592483141049466328727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16594394988760699644219151 24891592483141049466328727)
        ·
          refine ⟨37337388724711574199493091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24891592483141049466328727 37337388724711574199493091)
          ·
            refine ⟨56006083087067361299239637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37337388724711574199493091 56006083087067361299239637)
            ·
              refine ⟨1312642572353141280450929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56006083087067361299239637 1312642572353141280450929)
              ·
                refine ⟨984481929264855960338197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312642572353141280450929 984481929264855960338197)
                ·
                  refine ⟨46147590434290123140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 984481929264855960338197 46147590434290123140853)
                  ·
                    rfl

theorem cell23_808849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_808849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808849 prefixEnd_808849 := by exact prefixLift 808849
  have htrace : WordTrace (prefixWord ++ tailWord_808849) baseStart_808849 baseEnd_808849 := by
    simpa [prefixWord, tailWord_808849, baseEnd_808849] using wordTrace_append hprefix tailTrace_808849
  have hstable : (prefixWord ++ tailWord_808849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808849).length < 2 ^ (prefixWord ++ tailWord_808849).sum := by decide
  have hdescent : baseEnd_808849 < baseStart_808849 := by decide
  rcases family_descends (prefixWord ++ tailWord_808849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808916 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_808916 : Nat := 118140960795 + 808916 * 2 ^ 59
def prefixEnd_808916 : Nat := 4983230072969 + 3 ^ 40 * 808916 * 2
def baseEnd_808916 : Nat := 415362717112462346129869

theorem tailTrace_808916 : CollatzResearch.WordTrace tailWord_808916 prefixEnd_808916 415362717112462346129869 := by
  unfold tailWord_808916
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751795168721479349539301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19669060224961972466052401 14751795168721479349539301)
  ·
    refine ⟨2765961594135277378038619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14751795168721479349539301 2765961594135277378038619)
    ·
      refine ⟨4148942391202916067057929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765961594135277378038619 4148942391202916067057929)
      ·
        refine ⟨3111706793402187050293447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4148942391202916067057929 3111706793402187050293447)
        ·
          refine ⟨4667560190103280575440171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111706793402187050293447 4667560190103280575440171)
          ·
            refine ⟨7001340285154920863160257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4667560190103280575440171 7001340285154920863160257)
            ·
              refine ⟨5251005213866190647370193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7001340285154920863160257 5251005213866190647370193)
              ·
                refine ⟨3938253910399642985527645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5251005213866190647370193 3938253910399642985527645)
                ·
                  refine ⟨1476845216399866119572867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3938253910399642985527645 1476845216399866119572867)
                  ·
                    refine ⟨2215267824599799179359301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1476845216399866119572867 2215267824599799179359301)
                    ·
                      refine ⟨415362717112462346129869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2215267824599799179359301 415362717112462346129869)
                      ·
                        rfl

theorem cell23_808916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_808916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808916 prefixEnd_808916 := by exact prefixLift 808916
  have htrace : WordTrace (prefixWord ++ tailWord_808916) baseStart_808916 baseEnd_808916 := by
    simpa [prefixWord, tailWord_808916, baseEnd_808916] using wordTrace_append hprefix tailTrace_808916
  have hstable : (prefixWord ++ tailWord_808916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808916).length < 2 ^ (prefixWord ++ tailWord_808916).sum := by decide
  have hdescent : baseEnd_808916 < baseStart_808916 := by decide
  rcases family_descends (prefixWord ++ tailWord_808916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808919 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_808919 : Nat := 118140960795 + 808919 * 2 ^ 59
def prefixEnd_808919 : Nat := 4983230072969 + 3 ^ 40 * 808919 * 2
def baseEnd_808919 : Nat := 415364257554425834392355

theorem tailTrace_808919 : CollatzResearch.WordTrace tailWord_808919 prefixEnd_808919 415364257554425834392355 := by
  unfold tailWord_808919
  simp only [CollatzResearch.WordTrace]
  refine ⟨29503699756432090211437811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19669133170954726807625207 29503699756432090211437811)
  ·
    refine ⟨44255549634648135317156717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29503699756432090211437811 44255549634648135317156717)
    ·
      refine ⟨16595831112993050743933769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44255549634648135317156717 16595831112993050743933769)
      ·
        refine ⟨12446873334744788057950327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16595831112993050743933769 12446873334744788057950327)
        ·
          refine ⟨18670310002117182086925491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446873334744788057950327 18670310002117182086925491)
          ·
            refine ⟨28005465003175773130388237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670310002117182086925491 28005465003175773130388237)
            ·
              refine ⟨10502049376190914923895589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28005465003175773130388237 10502049376190914923895589)
              ·
                refine ⟨1969134258035796548230423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10502049376190914923895589 1969134258035796548230423)
                ·
                  refine ⟨2953701387053694822345635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969134258035796548230423 2953701387053694822345635)
                  ·
                    refine ⟨4430552080580542233518453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2953701387053694822345635 4430552080580542233518453)
                    ·
                      refine ⟨415364257554425834392355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4430552080580542233518453 415364257554425834392355)
                      ·
                        rfl

theorem cell23_808919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_808919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808919 prefixEnd_808919 := by exact prefixLift 808919
  have htrace : WordTrace (prefixWord ++ tailWord_808919) baseStart_808919 baseEnd_808919 := by
    simpa [prefixWord, tailWord_808919, baseEnd_808919] using wordTrace_append hprefix tailTrace_808919
  have hstable : (prefixWord ++ tailWord_808919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808919).length < 2 ^ (prefixWord ++ tailWord_808919).sum := by decide
  have hdescent : baseEnd_808919 < baseStart_808919 := by decide
  rcases family_descends (prefixWord ++ tailWord_808919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808929 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_808929 : Nat := 118140960795 + 808929 * 2 ^ 59
def prefixEnd_808929 : Nat := 4983230072969 + 3 ^ 40 * 808929 * 2
def baseEnd_808929 : Nat := 415369392360970795267309

theorem tailTrace_808929 : CollatzResearch.WordTrace tailWord_808929 prefixEnd_808929 415369392360970795267309 := by
  unfold tailWord_808929
  simp only [CollatzResearch.WordTrace]
  refine ⟨29504064486395861919301841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19669376324263907946201227 29504064486395861919301841)
  ·
    refine ⟨22128048364796896439476381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29504064486395861919301841 22128048364796896439476381)
    ·
      refine ⟨8298018136798836164803643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22128048364796896439476381 8298018136798836164803643)
      ·
        refine ⟨12447027205198254247205465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8298018136798836164803643 12447027205198254247205465)
        ·
          refine ⟨9335270403898690685404099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12447027205198254247205465 9335270403898690685404099)
          ·
            refine ⟨14002905605848036028106149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9335270403898690685404099 14002905605848036028106149)
            ·
              refine ⟨2625544801096506755269903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14002905605848036028106149 2625544801096506755269903)
              ·
                refine ⟨3938317201644760132904855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625544801096506755269903 3938317201644760132904855)
                ·
                  refine ⟨5907475802467140199357283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938317201644760132904855 5907475802467140199357283)
                  ·
                    refine ⟨8861213703700710299035925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5907475802467140199357283 8861213703700710299035925)
                    ·
                      refine ⟨415369392360970795267309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8861213703700710299035925 415369392360970795267309)
                      ·
                        rfl

theorem cell23_808929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_808929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808929 prefixEnd_808929 := by exact prefixLift 808929
  have htrace : WordTrace (prefixWord ++ tailWord_808929) baseStart_808929 baseEnd_808929 := by
    simpa [prefixWord, tailWord_808929, baseEnd_808929] using wordTrace_append hprefix tailTrace_808929
  have hstable : (prefixWord ++ tailWord_808929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808929).length < 2 ^ (prefixWord ++ tailWord_808929).sum := by decide
  have hdescent : baseEnd_808929 < baseStart_808929 := by decide
  rcases family_descends (prefixWord ++ tailWord_808929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808967 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_808967 : Nat := 118140960795 + 808967 * 2 ^ 59
def prefixEnd_808967 : Nat := 4983230072969 + 3 ^ 40 * 808967 * 2
def baseEnd_808967 : Nat := 415388904625841646592135

theorem tailTrace_808967 : CollatzResearch.WordTrace tailWord_808967 prefixEnd_808967 415388904625841646592135 := by
  unfold tailWord_808967
  simp only [CollatzResearch.WordTrace]
  refine ⟨29505450460258194409185155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19670300306838796272790103 29505450460258194409185155)
  ·
    refine ⟨44258175690387291613777733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29505450460258194409185155 44258175690387291613777733)
    ·
      refine ⟨8298407941947617177583325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44258175690387291613777733 8298407941947617177583325)
      ·
        refine ⟨3111902978230356441593747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8298407941947617177583325 3111902978230356441593747)
        ·
          refine ⟨4667854467345534662390621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111902978230356441593747 4667854467345534662390621)
          ·
            refine ⟨1750445425254575498396483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4667854467345534662390621 1750445425254575498396483)
            ·
              refine ⟨2625668137881863247594725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750445425254575498396483 2625668137881863247594725)
              ·
                refine ⟨492312775852849358924011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2625668137881863247594725 492312775852849358924011)
                ·
                  refine ⟨738469163779274038386017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492312775852849358924011 738469163779274038386017)
                  ·
                    refine ⟨553851872834455528789513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738469163779274038386017 553851872834455528789513)
                    ·
                      refine ⟨415388904625841646592135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553851872834455528789513 415388904625841646592135)
                      ·
                        rfl

theorem cell23_808967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_808967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_808967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_808967 prefixEnd_808967 := by exact prefixLift 808967
  have htrace : WordTrace (prefixWord ++ tailWord_808967) baseStart_808967 baseEnd_808967 := by
    simpa [prefixWord, tailWord_808967, baseEnd_808967] using wordTrace_append hprefix tailTrace_808967
  have hstable : (prefixWord ++ tailWord_808967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808967).length < 2 ^ (prefixWord ++ tailWord_808967).sum := by decide
  have hdescent : baseEnd_808967 < baseStart_808967 := by decide
  rcases family_descends (prefixWord ++ tailWord_808967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809010 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_809010 : Nat := 118140960795 + 809010 * 2 ^ 59
def prefixEnd_809010 : Nat := 4983230072969 + 3 ^ 40 * 809010 * 2
def baseEnd_809010 : Nat := 415410984293984978354437

theorem tailTrace_809010 : CollatzResearch.WordTrace tailWord_809010 prefixEnd_809010 415410984293984978354437 := by
  unfold tailWord_809010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376754699775603188250121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19671345866068275168666989 7376754699775603188250121)
  ·
    refine ⟨5532566024831702391187591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7376754699775603188250121 5532566024831702391187591)
    ·
      refine ⟨8298849037247553586781387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532566024831702391187591 8298849037247553586781387)
      ·
        refine ⟨12448273555871330380172081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8298849037247553586781387 12448273555871330380172081)
        ·
          refine ⟨9336205166903497785129061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12448273555871330380172081 9336205166903497785129061)
          ·
            refine ⟨1750538468794405834711699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9336205166903497785129061 1750538468794405834711699)
            ·
              refine ⟨2625807703191608752067549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750538468794405834711699 2625807703191608752067549)
              ·
                refine ⟨984677888696853282025331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2625807703191608752067549 984677888696853282025331)
                ·
                  refine ⟨1477016833045279923037997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984677888696853282025331 1477016833045279923037997)
                  ·
                    refine ⟨553881312391979971139249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477016833045279923037997 553881312391979971139249)
                    ·
                      refine ⟨415410984293984978354437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 553881312391979971139249 415410984293984978354437)
                      ·
                        rfl

theorem cell23_809010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_809010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809010 prefixEnd_809010 := by exact prefixLift 809010
  have htrace : WordTrace (prefixWord ++ tailWord_809010) baseStart_809010 baseEnd_809010 := by
    simpa [prefixWord, tailWord_809010, baseEnd_809010] using wordTrace_append hprefix tailTrace_809010
  have hstable : (prefixWord ++ tailWord_809010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809010).length < 2 ^ (prefixWord ++ tailWord_809010).sum := by decide
  have hdescent : baseEnd_809010 < baseStart_809010 := by decide
  rcases family_descends (prefixWord ++ tailWord_809010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809017 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 3]
def baseStart_809017 : Nat := 118140960795 + 809017 * 2 ^ 59
def prefixEnd_809017 : Nat := 4983230072969 + 3 ^ 40 * 809017 * 2
def baseEnd_809017 : Nat := 415414578658566450966905

theorem tailTrace_809017 : CollatzResearch.WordTrace tailWord_809017 prefixEnd_809017 415414578658566450966905 := by
  unfold tailWord_809017
  simp only [CollatzResearch.WordTrace]
  refine ⟨29507274110077052948505305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19671516073384701965670203 29507274110077052948505305)
  ·
    refine ⟨22130455582557789711378979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29507274110077052948505305 22130455582557789711378979)
    ·
      refine ⟨33195683373836684567068469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22130455582557789711378979 33195683373836684567068469)
      ·
        refine ⟨3112095316297189178162669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33195683373836684567068469 3112095316297189178162669)
        ·
          refine ⟨1167035743611445941811001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3112095316297189178162669 1167035743611445941811001)
          ·
            refine ⟨875276807708584456358251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167035743611445941811001 875276807708584456358251)
            ·
              refine ⟨1312915211562876684537377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875276807708584456358251 1312915211562876684537377)
              ·
                refine ⟨984686408672157513403033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312915211562876684537377 984686408672157513403033)
                ·
                  refine ⟨738514806504118135052275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 984686408672157513403033 738514806504118135052275)
                  ·
                    refine ⟨1107772209756177202578413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 738514806504118135052275 1107772209756177202578413)
                    ·
                      refine ⟨415414578658566450966905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1107772209756177202578413 415414578658566450966905)
                      ·
                        rfl

theorem cell23_809017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_809017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809017 prefixEnd_809017 := by exact prefixLift 809017
  have htrace : WordTrace (prefixWord ++ tailWord_809017) baseStart_809017 baseEnd_809017 := by
    simpa [prefixWord, tailWord_809017, baseEnd_809017] using wordTrace_append hprefix tailTrace_809017
  have hstable : (prefixWord ++ tailWord_809017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809017).length < 2 ^ (prefixWord ++ tailWord_809017).sum := by decide
  have hdescent : baseEnd_809017 < baseStart_809017 := by decide
  rcases family_descends (prefixWord ++ tailWord_809017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809019 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_809019 : Nat := 118140960795 + 809019 * 2 ^ 59
def prefixEnd_809019 : Nat := 4983230072969 + 3 ^ 40 * 809019 * 2
def baseEnd_809019 : Nat := 415415605619875443141895

theorem tailTrace_809019 : CollatzResearch.WordTrace tailWord_809019 prefixEnd_809019 415415605619875443141895 := by
  unfold tailWord_809019
  simp only [CollatzResearch.WordTrace]
  refine ⟨29507347056069807290078111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19671564704046538193385407 29507347056069807290078111)
  ·
    refine ⟨44261020584104710935117167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29507347056069807290078111 44261020584104710935117167)
    ·
      refine ⟨66391530876157066402675751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44261020584104710935117167 66391530876157066402675751)
      ·
        refine ⟨99587296314235599604013627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66391530876157066402675751 99587296314235599604013627)
        ·
          refine ⟨149380944471353399406020441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99587296314235599604013627 149380944471353399406020441)
          ·
            refine ⟨112035708353515049554515331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149380944471353399406020441 112035708353515049554515331)
            ·
              refine ⟨168053562530272574331772997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112035708353515049554515331 168053562530272574331772997)
              ·
                refine ⟨31510042974426107687207437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168053562530272574331772997 31510042974426107687207437)
                ·
                  refine ⟨11816266115409790382702789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31510042974426107687207437 11816266115409790382702789)
                  ·
                    refine ⟨2215549896639335696756773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11816266115409790382702789 2215549896639335696756773)
                    ·
                      refine ⟨415415605619875443141895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2215549896639335696756773 415415605619875443141895)
                      ·
                        rfl

theorem cell23_809019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_809019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809019 prefixEnd_809019 := by exact prefixLift 809019
  have htrace : WordTrace (prefixWord ++ tailWord_809019) baseStart_809019 baseEnd_809019 := by
    simpa [prefixWord, tailWord_809019, baseEnd_809019] using wordTrace_append hprefix tailTrace_809019
  have hstable : (prefixWord ++ tailWord_809019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809019).length < 2 ^ (prefixWord ++ tailWord_809019).sum := by decide
  have hdescent : baseEnd_809019 < baseStart_809019 := by decide
  rcases family_descends (prefixWord ++ tailWord_809019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809036 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_809036 : Nat := 118140960795 + 809036 * 2 ^ 59
def prefixEnd_809036 : Nat := 4983230072969 + 3 ^ 40 * 809036 * 2
def baseEnd_809036 : Nat := 415424334791001876629317

theorem tailTrace_809036 : CollatzResearch.WordTrace tailWord_809036 prefixEnd_809036 415424334791001876629317 := by
  unfold tailWord_809036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14753983548504109596723481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19671978064672146128964641 14753983548504109596723481)
  ·
    refine ⟨11065487661378082197542611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14753983548504109596723481 11065487661378082197542611)
    ·
      refine ⟨16598231492067123296313917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11065487661378082197542611 16598231492067123296313917)
      ·
        refine ⟨6224336809525171236117719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16598231492067123296313917 6224336809525171236117719)
        ·
          refine ⟨9336505214287756854176579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224336809525171236117719 9336505214287756854176579)
          ·
            refine ⟨14004757821431635281264869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336505214287756854176579 14004757821431635281264869)
            ·
              refine ⟨2625892091518431615237163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14004757821431635281264869 2625892091518431615237163)
              ·
                refine ⟨3938838137277647422855745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625892091518431615237163 3938838137277647422855745)
                ·
                  refine ⟨2954128602958235567141809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3938838137277647422855745 2954128602958235567141809)
                  ·
                    refine ⟨2215596452218676675356357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954128602958235567141809 2215596452218676675356357)
                    ·
                      refine ⟨415424334791001876629317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2215596452218676675356357 415424334791001876629317)
                      ·
                        rfl

theorem cell23_809036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_809036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809036 prefixEnd_809036 := by exact prefixLift 809036
  have htrace : WordTrace (prefixWord ++ tailWord_809036) baseStart_809036 baseEnd_809036 := by
    simpa [prefixWord, tailWord_809036, baseEnd_809036] using wordTrace_append hprefix tailTrace_809036
  have hstable : (prefixWord ++ tailWord_809036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809036).length < 2 ^ (prefixWord ++ tailWord_809036).sum := by decide
  have hdescent : baseEnd_809036 < baseStart_809036 := by decide
  rcases family_descends (prefixWord ++ tailWord_809036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809164 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_809164 : Nat := 118140960795 + 809164 * 2 ^ 59
def prefixEnd_809164 : Nat := 4983230072969 + 3 ^ 40 * 809164 * 2
def baseEnd_809164 : Nat := 415490060314777375828729

theorem tailTrace_809164 : CollatzResearch.WordTrace tailWord_809164 prefixEnd_809164 415490060314777375828729 := by
  unfold tailWord_809164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14756317820272248527053273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19675090427029664702737697 14756317820272248527053273)
  ·
    refine ⟨11067238365204186395289955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14756317820272248527053273 11067238365204186395289955)
    ·
      refine ⟨16600857547806279592934933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067238365204186395289955 16600857547806279592934933)
      ·
        refine ⟨778165197553419355918825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16600857547806279592934933 778165197553419355918825)
        ·
          refine ⟨583623898165064516939119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778165197553419355918825 583623898165064516939119)
          ·
            refine ⟨875435847247596775408679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583623898165064516939119 875435847247596775408679)
            ·
              refine ⟨1313153770871395163113019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875435847247596775408679 1313153770871395163113019)
              ·
                refine ⟨1969730656307092744669529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313153770871395163113019 1969730656307092744669529)
                ·
                  refine ⟨1477297992230319558502147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1969730656307092744669529 1477297992230319558502147)
                  ·
                    refine ⟨2215946988345479337753221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477297992230319558502147 2215946988345479337753221)
                    ·
                      refine ⟨415490060314777375828729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2215946988345479337753221 415490060314777375828729)
                      ·
                        rfl

theorem cell23_809164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_809164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809164 prefixEnd_809164 := by exact prefixLift 809164
  have htrace : WordTrace (prefixWord ++ tailWord_809164) baseStart_809164 baseEnd_809164 := by
    simpa [prefixWord, tailWord_809164, baseEnd_809164] using wordTrace_append hprefix tailTrace_809164
  have hstable : (prefixWord ++ tailWord_809164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809164).length < 2 ^ (prefixWord ++ tailWord_809164).sum := by decide
  have hdescent : baseEnd_809164 < baseStart_809164 := by decide
  rcases family_descends (prefixWord ++ tailWord_809164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809174 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_809174 : Nat := 118140960795 + 809174 * 2 ^ 59
def prefixEnd_809174 : Nat := 4983230072969 + 3 ^ 40 * 809174 * 2
def baseEnd_809174 : Nat := 138498398373774112234561

theorem tailTrace_809174 : CollatzResearch.WordTrace tailWord_809174 prefixEnd_809174 138498398373774112234561 := by
  unfold tailWord_809174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844562523156766797623161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19675333580338845841313717 1844562523156766797623161)
  ·
    refine ⟨1383421892367575098217371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1844562523156766797623161 1383421892367575098217371)
    ·
      refine ⟨2075132838551362647326057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1383421892367575098217371 2075132838551362647326057)
      ·
        refine ⟨1556349628913521985494543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2075132838551362647326057 1556349628913521985494543)
        ·
          refine ⟨2334524443370282978241815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556349628913521985494543 2334524443370282978241815)
          ·
            refine ⟨3501786665055424467362723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334524443370282978241815 3501786665055424467362723)
            ·
              refine ⟨5252679997583136701044085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501786665055424467362723 5252679997583136701044085)
              ·
                refine ⟨492438749773419065722883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5252679997583136701044085 492438749773419065722883)
                ·
                  refine ⟨738658124660128598584325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492438749773419065722883 738658124660128598584325)
                  ·
                    refine ⟨138498398373774112234561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 738658124660128598584325 138498398373774112234561)
                    ·
                      rfl

theorem cell23_809174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_809174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809174 prefixEnd_809174 := by exact prefixLift 809174
  have htrace : WordTrace (prefixWord ++ tailWord_809174) baseStart_809174 baseEnd_809174 := by
    simpa [prefixWord, tailWord_809174, baseEnd_809174] using wordTrace_append hprefix tailTrace_809174
  have hstable : (prefixWord ++ tailWord_809174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809174).length < 2 ^ (prefixWord ++ tailWord_809174).sum := by decide
  have hdescent : baseEnd_809174 < baseStart_809174 := by decide
  rcases family_descends (prefixWord ++ tailWord_809174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809187 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 6]
def baseStart_809187 : Nat := 118140960795 + 809187 * 2 ^ 59
def prefixEnd_809187 : Nat := 4983230072969 + 3 ^ 40 * 809187 * 2
def baseEnd_809187 : Nat := 46166874485536753982347

theorem tailTrace_809187 : CollatzResearch.WordTrace tailWord_809187 prefixEnd_809187 46166874485536753982347 := by
  unfold tailWord_809187
  simp only [CollatzResearch.WordTrace]
  refine ⟨29513474519461171982193815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675649679640781321462543 29513474519461171982193815)
  ·
    refine ⟨44270211779191757973290723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29513474519461171982193815 44270211779191757973290723)
    ·
      refine ⟨66405317668787636959936085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44270211779191757973290723 66405317668787636959936085)
      ·
        refine ⟨778187316431105120624251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 66405317668787636959936085 778187316431105120624251)
        ·
          refine ⟨1167280974646657680936377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778187316431105120624251 1167280974646657680936377)
          ·
            refine ⟨875460730984993260702283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167280974646657680936377 875460730984993260702283)
            ·
              refine ⟨1313191096477489891053425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875460730984993260702283 1313191096477489891053425)
              ·
                refine ⟨984893322358117418290069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313191096477489891053425 984893322358117418290069)
                ·
                  refine ⟨46166874485536753982347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 984893322358117418290069 46166874485536753982347)
                  ·
                    rfl

theorem cell23_809187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 6].length) (baseStart_809187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809187 prefixEnd_809187 := by exact prefixLift 809187
  have htrace : WordTrace (prefixWord ++ tailWord_809187) baseStart_809187 baseEnd_809187 := by
    simpa [prefixWord, tailWord_809187, baseEnd_809187] using wordTrace_append hprefix tailTrace_809187
  have hstable : (prefixWord ++ tailWord_809187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809187).length < 2 ^ (prefixWord ++ tailWord_809187).sum := by decide
  have hdescent : baseEnd_809187 < baseStart_809187 := by decide
  rcases family_descends (prefixWord ++ tailWord_809187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809240 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_809240 : Nat := 118140960795 + 809240 * 2 ^ 59
def prefixEnd_809240 : Nat := 4983230072969 + 3 ^ 40 * 809240 * 2
def baseEnd_809240 : Nat := 415529084844519078478379

theorem tailTrace_809240 : CollatzResearch.WordTrace tailWord_809240 prefixEnd_809240 415529084844519078478379 := by
  unfold tailWord_809240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757703794134581016936587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19676938392179441355915449 14757703794134581016936587)
  ·
    refine ⟨22136555691201871525404881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14757703794134581016936587 22136555691201871525404881)
    ·
      refine ⟨16602416768401403644053661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22136555691201871525404881 16602416768401403644053661)
      ·
        refine ⟨6225906288150526366520123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16602416768401403644053661 6225906288150526366520123)
        ·
          refine ⟨9338859432225789549780185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6225906288150526366520123 9338859432225789549780185)
          ·
            refine ⟨7004144574169342162335139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9338859432225789549780185 7004144574169342162335139)
            ·
              refine ⟨10506216861254013243502709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004144574169342162335139 10506216861254013243502709)
              ·
                refine ⟨984957830742563741578379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10506216861254013243502709 984957830742563741578379)
                ·
                  refine ⟨1477436746113845612367569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984957830742563741578379 1477436746113845612367569)
                  ·
                    refine ⟨1108077559585384209275677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477436746113845612367569 1108077559585384209275677)
                    ·
                      refine ⟨415529084844519078478379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108077559585384209275677 415529084844519078478379)
                      ·
                        rfl

theorem cell23_809240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_809240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809240 prefixEnd_809240 := by exact prefixLift 809240
  have htrace : WordTrace (prefixWord ++ tailWord_809240) baseStart_809240 baseEnd_809240 := by
    simpa [prefixWord, tailWord_809240, baseEnd_809240] using wordTrace_append hprefix tailTrace_809240
  have hstable : (prefixWord ++ tailWord_809240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809240).length < 2 ^ (prefixWord ++ tailWord_809240).sum := by decide
  have hdescent : baseEnd_809240 < baseStart_809240 := by decide
  rcases family_descends (prefixWord ++ tailWord_809240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809303 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 2, 6]
def baseStart_809303 : Nat := 118140960795 + 809303 * 2 ^ 59
def prefixEnd_809303 : Nat := 4983230072969 + 3 ^ 40 * 809303 * 2
def baseEnd_809303 : Nat := 138520478041917443996863

theorem tailTrace_809303 : CollatzResearch.WordTrace tailWord_809303 prefixEnd_809303 138520478041917443996863 := by
  unfold tailWord_809303
  simp only [CollatzResearch.WordTrace]
  refine ⟨29517705387040923793416563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19678470258027282528944375 29517705387040923793416563)
  ·
    refine ⟨44276558080561385690124845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29517705387040923793416563 44276558080561385690124845)
    ·
      refine ⟨16603709280210519633796817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44276558080561385690124845 16603709280210519633796817)
      ·
        refine ⟨12452781960157889725347613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16603709280210519633796817 12452781960157889725347613)
        ·
          refine ⟨4669793235059208647005355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12452781960157889725347613 4669793235059208647005355)
          ·
            refine ⟨7004689852588812970508033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669793235059208647005355 7004689852588812970508033)
            ·
              refine ⟨5253517389441609727881025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004689852588812970508033 5253517389441609727881025)
              ·
                refine ⟨3940138042081207295910769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253517389441609727881025 3940138042081207295910769)
                ·
                  refine ⟨2955103531560905471933077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940138042081207295910769 2955103531560905471933077)
                  ·
                    refine ⟨138520478041917443996863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2955103531560905471933077 138520478041917443996863)
                    ·
                      rfl

theorem cell23_809303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_809303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809303 prefixEnd_809303 := by exact prefixLift 809303
  have htrace : WordTrace (prefixWord ++ tailWord_809303) baseStart_809303 baseEnd_809303 := by
    simpa [prefixWord, tailWord_809303, baseEnd_809303] using wordTrace_append hprefix tailTrace_809303
  have hstable : (prefixWord ++ tailWord_809303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809303).length < 2 ^ (prefixWord ++ tailWord_809303).sum := by decide
  have hdescent : baseEnd_809303 < baseStart_809303 := by decide
  rcases family_descends (prefixWord ++ tailWord_809303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809320 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 2, 6]
def baseStart_809320 : Nat := 118140960795 + 809320 * 2 ^ 59
def prefixEnd_809320 : Nat := 4983230072969 + 3 ^ 40 * 809320 * 2
def baseEnd_809320 : Nat := 138523387765626255159337

theorem tailTrace_809320 : CollatzResearch.WordTrace tailWord_809320 prefixEnd_809320 138523387765626255159337 := by
  unfold tailWord_809320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759162713989667848392707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19678883618652890464523609 14759162713989667848392707)
  ·
    refine ⟨22138744070984501772589061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14759162713989667848392707 22138744070984501772589061)
    ·
      refine ⟨4151014513309594082360449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22138744070984501772589061 4151014513309594082360449)
      ·
        refine ⟨3113260884982195561770337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4151014513309594082360449 3113260884982195561770337)
        ·
          refine ⟨2334945663736646671327753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3113260884982195561770337 2334945663736646671327753)
          ·
            refine ⟨1751209247802485003495815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334945663736646671327753 1751209247802485003495815)
            ·
              refine ⟨2626813871703727505243723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751209247802485003495815 2626813871703727505243723)
              ·
                refine ⟨3940220807555591257865585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626813871703727505243723 3940220807555591257865585)
                ·
                  refine ⟨2955165605666693443399189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940220807555591257865585 2955165605666693443399189)
                  ·
                    refine ⟨138523387765626255159337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2955165605666693443399189 138523387765626255159337)
                    ·
                      rfl

theorem cell23_809320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_809320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809320 prefixEnd_809320 := by exact prefixLift 809320
  have htrace : WordTrace (prefixWord ++ tailWord_809320) baseStart_809320 baseEnd_809320 := by
    simpa [prefixWord, tailWord_809320, baseEnd_809320] using wordTrace_append hprefix tailTrace_809320
  have hstable : (prefixWord ++ tailWord_809320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809320).length < 2 ^ (prefixWord ++ tailWord_809320).sum := by decide
  have hdescent : baseEnd_809320 < baseStart_809320 := by decide
  rcases family_descends (prefixWord ++ tailWord_809320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809323 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_809323 : Nat := 118140960795 + 809323 * 2 ^ 59
def prefixEnd_809323 : Nat := 4983230072969 + 3 ^ 40 * 809323 * 2
def baseEnd_809323 : Nat := 415571703738842253740497

theorem tailTrace_809323 : CollatzResearch.WordTrace tailWord_809323 prefixEnd_809323 415571703738842253740497 := by
  unfold tailWord_809323
  simp only [CollatzResearch.WordTrace]
  refine ⟨29518434846968467209144623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19678956564645644806096415 29518434846968467209144623)
  ·
    refine ⟨44277652270452700813716935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29518434846968467209144623 44277652270452700813716935)
    ·
      refine ⟨66416478405679051220575403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44277652270452700813716935 66416478405679051220575403)
      ·
        refine ⟨99624717608518576830863105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66416478405679051220575403 99624717608518576830863105)
        ·
          refine ⟨74718538206388932623147329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99624717608518576830863105 74718538206388932623147329)
          ·
            refine ⟨56038903654791699467360497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74718538206388932623147329 56038903654791699467360497)
            ·
              refine ⟨42029177741093774600520373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56038903654791699467360497 42029177741093774600520373)
              ·
                refine ⟨3940235413227541368798785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42029177741093774600520373 3940235413227541368798785)
                ·
                  refine ⟨2955176559920656026599089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940235413227541368798785 2955176559920656026599089)
                  ·
                    refine ⟨2216382419940492019949317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2955176559920656026599089 2216382419940492019949317)
                    ·
                      refine ⟨415571703738842253740497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2216382419940492019949317 415571703738842253740497)
                      ·
                        rfl

theorem cell23_809323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_809323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809323 prefixEnd_809323 := by exact prefixLift 809323
  have htrace : WordTrace (prefixWord ++ tailWord_809323) baseStart_809323 baseEnd_809323 := by
    simpa [prefixWord, tailWord_809323, baseEnd_809323] using wordTrace_append hprefix tailTrace_809323
  have hstable : (prefixWord ++ tailWord_809323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809323).length < 2 ^ (prefixWord ++ tailWord_809323).sum := by decide
  have hdescent : baseEnd_809323 < baseStart_809323 := by decide
  rcases family_descends (prefixWord ++ tailWord_809323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809400 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_809400 : Nat := 118140960795 + 809400 * 2 ^ 59
def prefixEnd_809400 : Nat := 4983230072969 + 3 ^ 40 * 809400 * 2
def baseEnd_809400 : Nat := 415611241749238452477643

theorem tailTrace_809400 : CollatzResearch.WordTrace tailWord_809400 prefixEnd_809400 415611241749238452477643 := by
  unfold tailWord_809400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760621633844754679848827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19680828845126339573131769 14760621633844754679848827)
  ·
    refine ⟨22140932450767132019773241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14760621633844754679848827 22140932450767132019773241)
    ·
      refine ⟨16605699338075349014829931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22140932450767132019773241 16605699338075349014829931)
      ·
        refine ⟨24908549007113023522244897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16605699338075349014829931 24908549007113023522244897)
        ·
          refine ⟨18681411755334767641683673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24908549007113023522244897 18681411755334767641683673)
          ·
            refine ⟨14011058816501075731262755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18681411755334767641683673 14011058816501075731262755)
            ·
              refine ⟨21016588224751613596894133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14011058816501075731262755 21016588224751613596894133)
              ·
                refine ⟨1970305146070463774708825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21016588224751613596894133 1970305146070463774708825)
                ·
                  refine ⟨1477728859552847831031619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970305146070463774708825 1477728859552847831031619)
                  ·
                    refine ⟨2216593289329271746547429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477728859552847831031619 2216593289329271746547429)
                    ·
                      refine ⟨415611241749238452477643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2216593289329271746547429 415611241749238452477643)
                      ·
                        rfl

theorem cell23_809400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_809400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809400 prefixEnd_809400 := by exact prefixLift 809400
  have htrace : WordTrace (prefixWord ++ tailWord_809400) baseStart_809400 baseEnd_809400 := by
    simpa [prefixWord, tailWord_809400, baseEnd_809400] using wordTrace_append hprefix tailTrace_809400
  have hstable : (prefixWord ++ tailWord_809400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809400).length < 2 ^ (prefixWord ++ tailWord_809400).sum := by decide
  have hdescent : baseEnd_809400 < baseStart_809400 := by decide
  rcases family_descends (prefixWord ++ tailWord_809400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809437 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_809437 : Nat := 118140960795 + 809437 * 2 ^ 59
def prefixEnd_809437 : Nat := 4983230072969 + 3 ^ 40 * 809437 * 2
def baseEnd_809437 : Nat := 415630240533454807714973

theorem tailTrace_809437 : CollatzResearch.WordTrace tailWord_809437 prefixEnd_809437 415630240533454807714973 := by
  unfold tailWord_809437
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522592768555464678794565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19681728512370309785863043 29522592768555464678794565)
  ·
    refine ⟨5535486144104149627273981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29522592768555464678794565 5535486144104149627273981)
    ·
      refine ⟨2075807304039056110227743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5535486144104149627273981 2075807304039056110227743)
      ·
        refine ⟨3113710956058584165341615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075807304039056110227743 3113710956058584165341615)
        ·
          refine ⟨4670566434087876248012423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113710956058584165341615 4670566434087876248012423)
          ·
            refine ⟨7005849651131814372018635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670566434087876248012423 7005849651131814372018635)
            ·
              refine ⟨10508774476697721558027953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005849651131814372018635 10508774476697721558027953)
              ·
                refine ⟨7881580857523291168520965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10508774476697721558027953 7881580857523291168520965)
                ·
                  refine ⟨1477796410785617094097681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7881580857523291168520965 1477796410785617094097681)
                  ·
                    refine ⟨1108347308089212820573261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477796410785617094097681 1108347308089212820573261)
                    ·
                      refine ⟨415630240533454807714973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108347308089212820573261 415630240533454807714973)
                      ·
                        rfl

theorem cell23_809437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_809437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809437 prefixEnd_809437 := by exact prefixLift 809437
  have htrace : WordTrace (prefixWord ++ tailWord_809437) baseStart_809437 baseEnd_809437 := by
    simpa [prefixWord, tailWord_809437, baseEnd_809437] using wordTrace_append hprefix tailTrace_809437
  have hstable : (prefixWord ++ tailWord_809437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809437).length < 2 ^ (prefixWord ++ tailWord_809437).sum := by decide
  have hdescent : baseEnd_809437 < baseStart_809437 := by decide
  rcases family_descends (prefixWord ++ tailWord_809437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809440 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 6]
def baseStart_809440 : Nat := 118140960795 + 809440 * 2 ^ 59
def prefixEnd_809440 : Nat := 4983230072969 + 3 ^ 40 * 809440 * 2
def baseEnd_809440 : Nat := 46181308997268699553051

theorem tailTrace_809440 : CollatzResearch.WordTrace tailWord_809440 prefixEnd_809440 46181308997268699553051 := by
  unfold tailWord_809440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761351093772298095576887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19681801458363064127435849 14761351093772298095576887)
  ·
    refine ⟨22142026640658447143365331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14761351093772298095576887 22142026640658447143365331)
    ·
      refine ⟨33213039960987670715047997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22142026640658447143365331 33213039960987670715047997)
      ·
        refine ⟨12454889985370376518142999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33213039960987670715047997 12454889985370376518142999)
        ·
          refine ⟨18682334978055564777214499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454889985370376518142999 18682334978055564777214499)
          ·
            refine ⟨28023502467083347165821749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682334978055564777214499 28023502467083347165821749)
            ·
              refine ⟨2627203356289063796795789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28023502467083347165821749 2627203356289063796795789)
              ·
                refine ⟨985201258608398923798421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2627203356289063796795789 985201258608398923798421)
                ·
                  refine ⟨46181308997268699553051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 985201258608398923798421 46181308997268699553051)
                  ·
                    rfl

theorem cell23_809440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 6].length) (baseStart_809440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809440 prefixEnd_809440 := by exact prefixLift 809440
  have htrace : WordTrace (prefixWord ++ tailWord_809440) baseStart_809440 baseEnd_809440 := by
    simpa [prefixWord, tailWord_809440, baseEnd_809440] using wordTrace_append hprefix tailTrace_809440
  have hstable : (prefixWord ++ tailWord_809440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809440).length < 2 ^ (prefixWord ++ tailWord_809440).sum := by decide
  have hdescent : baseEnd_809440 < baseStart_809440 := by decide
  rcases family_descends (prefixWord ++ tailWord_809440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809454 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_809454 : Nat := 118140960795 + 809454 * 2 ^ 59
def prefixEnd_809454 : Nat := 4983230072969 + 3 ^ 40 * 809454 * 2
def baseEnd_809454 : Nat := 415638969704581241202395

theorem tailTrace_809454 : CollatzResearch.WordTrace tailWord_809454 prefixEnd_809454 415638969704581241202395 := by
  unfold tailWord_809454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690401601186734572770427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19682141872995917721442277 3690401601186734572770427)
  ·
    refine ⟨5535602401780101859155641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3690401601186734572770427 5535602401780101859155641)
    ·
      refine ⟨4151701801335076394366731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5535602401780101859155641 4151701801335076394366731)
      ·
        refine ⟨6227552702002614591550097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151701801335076394366731 6227552702002614591550097)
        ·
          refine ⟨4670664526501960943662573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227552702002614591550097 4670664526501960943662573)
          ·
            refine ⟨1751499197438235353873465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4670664526501960943662573 1751499197438235353873465)
            ·
              refine ⟨1313624398078676515405099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751499197438235353873465 1313624398078676515405099)
              ·
                refine ⟨1970436597118014773107649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313624398078676515405099 1970436597118014773107649)
                ·
                  refine ⟨1477827447838511079830737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970436597118014773107649 1477827447838511079830737)
                  ·
                    refine ⟨1108370585878883309873053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477827447838511079830737 1108370585878883309873053)
                    ·
                      refine ⟨415638969704581241202395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108370585878883309873053 415638969704581241202395)
                      ·
                        rfl

theorem cell23_809454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_809454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809454 prefixEnd_809454 := by exact prefixLift 809454
  have htrace : WordTrace (prefixWord ++ tailWord_809454) baseStart_809454 baseEnd_809454 := by
    simpa [prefixWord, tailWord_809454, baseEnd_809454] using wordTrace_append hprefix tailTrace_809454
  have hstable : (prefixWord ++ tailWord_809454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809454).length < 2 ^ (prefixWord ++ tailWord_809454).sum := by decide
  have hdescent : baseEnd_809454 < baseStart_809454 := by decide
  rcases family_descends (prefixWord ++ tailWord_809454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809507 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4]
def baseStart_809507 : Nat := 118140960795 + 809507 * 2 ^ 59
def prefixEnd_809507 : Nat := 4983230072969 + 3 ^ 40 * 809507 * 2
def baseEnd_809507 : Nat := 415666184179269533839651

theorem tailTrace_809507 : CollatzResearch.WordTrace tailWord_809507 prefixEnd_809507 415666184179269533839651 := by
  unfold tailWord_809507
  simp only [CollatzResearch.WordTrace]
  refine ⟨29525145878301866633842775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19683430585534577755895183 29525145878301866633842775)
  ·
    refine ⟨44287718817452799950764163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29525145878301866633842775 44287718817452799950764163)
    ·
      refine ⟨66431578226179199926146245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44287718817452799950764163 66431578226179199926146245)
      ·
        refine ⟨12455920917408599986152421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66431578226179199926146245 12455920917408599986152421)
        ·
          refine ⟨2335485172014112497403579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12455920917408599986152421 2335485172014112497403579)
          ·
            refine ⟨3503227758021168746105369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335485172014112497403579 3503227758021168746105369)
            ·
              refine ⟨2627420818515876559579027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503227758021168746105369 2627420818515876559579027)
              ·
                refine ⟨3941131227773814839368541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627420818515876559579027 3941131227773814839368541)
                ·
                  refine ⟨1477924210415180564763203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3941131227773814839368541 1477924210415180564763203)
                  ·
                    refine ⟨2216886315622770847144805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477924210415180564763203 2216886315622770847144805)
                    ·
                      refine ⟨415666184179269533839651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2216886315622770847144805 415666184179269533839651)
                      ·
                        rfl

theorem cell23_809507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_809507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809507 prefixEnd_809507 := by exact prefixLift 809507
  have htrace : WordTrace (prefixWord ++ tailWord_809507) baseStart_809507 baseEnd_809507 := by
    simpa [prefixWord, tailWord_809507, baseEnd_809507] using wordTrace_append hprefix tailTrace_809507
  have hstable : (prefixWord ++ tailWord_809507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809507).length < 2 ^ (prefixWord ++ tailWord_809507).sum := by decide
  have hdescent : baseEnd_809507 < baseStart_809507 := by decide
  rcases family_descends (prefixWord ++ tailWord_809507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809530 : List Nat := [3, 1, 1, 1, 3, 4, 10]
def baseStart_809530 : Nat := 118140960795 + 809530 * 2 ^ 59
def prefixEnd_809530 : Nat := 4983230072969 + 3 ^ 40 * 809530 * 2
def baseEnd_809530 : Nat := 5131827089312628936445

theorem tailTrace_809530 : CollatzResearch.WordTrace tailWord_809530 prefixEnd_809530 5131827089312628936445 := by
  unfold tailWord_809530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7381496189304635390482511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19683989838145694374620029 7381496189304635390482511)
  ·
    refine ⟨11072244283956953085723767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7381496189304635390482511 11072244283956953085723767)
    ·
      refine ⟨16608366425935429628585651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11072244283956953085723767 16608366425935429628585651)
      ·
        refine ⟨24912549638903144442878477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16608366425935429628585651 24912549638903144442878477)
        ·
          refine ⟨9342206114588679166079429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24912549638903144442878477 9342206114588679166079429)
          ·
            refine ⟨1751663646485377343639893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9342206114588679166079429 1751663646485377343639893)
            ·
              refine ⟨5131827089312628936445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1751663646485377343639893 5131827089312628936445)
              ·
                rfl

theorem cell23_809530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 10].length) (baseStart_809530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809530 prefixEnd_809530 := by exact prefixLift 809530
  have htrace : WordTrace (prefixWord ++ tailWord_809530) baseStart_809530 baseEnd_809530 := by
    simpa [prefixWord, tailWord_809530, baseEnd_809530] using wordTrace_append hprefix tailTrace_809530
  have hstable : (prefixWord ++ tailWord_809530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809530).length < 2 ^ (prefixWord ++ tailWord_809530).sum := by decide
  have hdescent : baseEnd_809530 < baseStart_809530 := by decide
  rcases family_descends (prefixWord ++ tailWord_809530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809541 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_809541 : Nat := 118140960795 + 809541 * 2 ^ 59
def prefixEnd_809541 : Nat := 4983230072969 + 3 ^ 40 * 809541 * 2
def baseEnd_809541 : Nat := 415683642521522400814495

theorem tailTrace_809541 : CollatzResearch.WordTrace tailWord_809541 prefixEnd_809541 415683642521522400814495 := by
  unfold tailWord_809541
  simp only [CollatzResearch.WordTrace]
  refine ⟨29526385960178690440580477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19684257306785793627053651 29526385960178690440580477)
  ·
    refine ⟨11072394735067008915217679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29526385960178690440580477 11072394735067008915217679)
    ·
      refine ⟨16608592102600513372826519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11072394735067008915217679 16608592102600513372826519)
      ·
        refine ⟨24912888153900770059239779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16608592102600513372826519 24912888153900770059239779)
        ·
          refine ⟨37369332230851155088859669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24912888153900770059239779 37369332230851155088859669)
          ·
            refine ⟨1751687448321147894790297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37369332230851155088859669 1751687448321147894790297)
            ·
              refine ⟨1313765586240860921092723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751687448321147894790297 1313765586240860921092723)
              ·
                refine ⟨1970648379361291381639085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313765586240860921092723 1970648379361291381639085)
                ·
                  refine ⟨738993142260484268114657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1970648379361291381639085 738993142260484268114657)
                  ·
                    refine ⟨554244856695363201085993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738993142260484268114657 554244856695363201085993)
                    ·
                      refine ⟨415683642521522400814495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554244856695363201085993 415683642521522400814495)
                      ·
                        rfl

theorem cell23_809541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_809541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809541 prefixEnd_809541 := by exact prefixLift 809541
  have htrace : WordTrace (prefixWord ++ tailWord_809541) baseStart_809541 baseEnd_809541 := by
    simpa [prefixWord, tailWord_809541, baseEnd_809541] using wordTrace_append hprefix tailTrace_809541
  have hstable : (prefixWord ++ tailWord_809541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809541).length < 2 ^ (prefixWord ++ tailWord_809541).sum := by decide
  have hdescent : baseEnd_809541 < baseStart_809541 := by decide
  rcases family_descends (prefixWord ++ tailWord_809541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809560 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 2, 7]
def baseStart_809560 : Nat := 118140960795 + 809560 * 2 ^ 59
def prefixEnd_809560 : Nat := 4983230072969 + 3 ^ 40 * 809560 * 2
def baseEnd_809560 : Nat := 138564466217985942158969

theorem tailTrace_809560 : CollatzResearch.WordTrace tailWord_809560 prefixEnd_809560 138564466217985942158969 := by
  unfold tailWord_809560
  simp only [CollatzResearch.WordTrace]
  refine ⟨14763539473554928342761067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19684719298073237790348089 14763539473554928342761067)
  ·
    refine ⟨22145309210332392514141601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14763539473554928342761067 22145309210332392514141601)
    ·
      refine ⟨16608981907749294385606201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22145309210332392514141601 16608981907749294385606201)
      ·
        refine ⟨12456736430811970789204651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16608981907749294385606201 12456736430811970789204651)
        ·
          refine ⟨18685104646217956183806977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456736430811970789204651 18685104646217956183806977)
          ·
            refine ⟨14013828484663467137855233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18685104646217956183806977 14013828484663467137855233)
            ·
              refine ⟨10510371363497600353391425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14013828484663467137855233 10510371363497600353391425)
              ·
                refine ⟨7882778522623200265043569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10510371363497600353391425 7882778522623200265043569)
                ·
                  refine ⟨5912083891967400198782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7882778522623200265043569 5912083891967400198782677)
                  ·
                    refine ⟨138564466217985942158969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5912083891967400198782677 138564466217985942158969)
                    ·
                      rfl

theorem cell23_809560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_809560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809560 prefixEnd_809560 := by exact prefixLift 809560
  have htrace : WordTrace (prefixWord ++ tailWord_809560) baseStart_809560 baseEnd_809560 := by
    simpa [prefixWord, tailWord_809560, baseEnd_809560] using wordTrace_append hprefix tailTrace_809560
  have hstable : (prefixWord ++ tailWord_809560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809560).length < 2 ^ (prefixWord ++ tailWord_809560).sum := by decide
  have hdescent : baseEnd_809560 < baseStart_809560 := by decide
  rcases family_descends (prefixWord ++ tailWord_809560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809567 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 7, 2]
def baseStart_809567 : Nat := 118140960795 + 809567 * 2 ^ 59
def prefixEnd_809567 : Nat := 4983230072969 + 3 ^ 40 * 809567 * 2
def baseEnd_809567 : Nat := 415696993018539299089375

theorem tailTrace_809567 : CollatzResearch.WordTrace tailWord_809567 prefixEnd_809567 415696993018539299089375 := by
  unfold tailWord_809567
  simp only [CollatzResearch.WordTrace]
  refine ⟨29527334258084496881026955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19684889505389664587351303 29527334258084496881026955)
  ·
    refine ⟨44291001387126745321540433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29527334258084496881026955 44291001387126745321540433)
    ·
      refine ⟨33218251040345058991155325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44291001387126745321540433 33218251040345058991155325)
      ·
        refine ⟨12456844140129397121683247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33218251040345058991155325 12456844140129397121683247)
        ·
          refine ⟨18685266210194095682524871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456844140129397121683247 18685266210194095682524871)
          ·
            refine ⟨28027899315291143523787307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18685266210194095682524871 28027899315291143523787307)
            ·
              refine ⟨42041848972936715285680961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28027899315291143523787307 42041848972936715285680961)
              ·
                refine ⟨31531386729702536464260721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42041848972936715285680961 31531386729702536464260721)
                ·
                  refine ⟨23648540047276902348195541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31531386729702536464260721 23648540047276902348195541)
                  ·
                    refine ⟨554262657358052398785833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23648540047276902348195541 554262657358052398785833)
                    ·
                      refine ⟨415696993018539299089375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554262657358052398785833 415696993018539299089375)
                      ·
                        rfl

theorem cell23_809567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_809567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809567 prefixEnd_809567 := by exact prefixLift 809567
  have htrace : WordTrace (prefixWord ++ tailWord_809567) baseStart_809567 baseEnd_809567 := by
    simpa [prefixWord, tailWord_809567, baseEnd_809567] using wordTrace_append hprefix tailTrace_809567
  have hstable : (prefixWord ++ tailWord_809567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809567).length < 2 ^ (prefixWord ++ tailWord_809567).sum := by decide
  have hdescent : baseEnd_809567 < baseStart_809567 := by decide
  rcases family_descends (prefixWord ++ tailWord_809567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809618 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_809618 : Nat := 118140960795 + 809618 * 2 ^ 59
def prefixEnd_809618 : Nat := 4983230072969 + 3 ^ 40 * 809618 * 2
def baseEnd_809618 : Nat := 415723180531918599551641

theorem tailTrace_809618 : CollatzResearch.WordTrace tailWord_809618 prefixEnd_809618 415723180531918599551641 := by
  unfold tailWord_809618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7382298595224933147783377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19686129587266488394089005 7382298595224933147783377)
  ·
    refine ⟨5536723946418699860837533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7382298595224933147783377 5536723946418699860837533)
    ·
      refine ⟨2076271479907012447814075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5536723946418699860837533 2076271479907012447814075)
      ·
        refine ⟨3114407219860518671721113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076271479907012447814075 3114407219860518671721113)
        ·
          refine ⟨2335805414895389003790835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3114407219860518671721113 2335805414895389003790835)
          ·
            refine ⟨3503708122343083505686253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335805414895389003790835 3503708122343083505686253)
            ·
              refine ⟨1313890545878656314632345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3503708122343083505686253 1313890545878656314632345)
              ·
                refine ⟨985417909408992235974259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313890545878656314632345 985417909408992235974259)
                ·
                  refine ⟨1478126864113488353961389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985417909408992235974259 1478126864113488353961389)
                  ·
                    refine ⟨554297574042558132735521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478126864113488353961389 554297574042558132735521)
                    ·
                      refine ⟨415723180531918599551641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554297574042558132735521 415723180531918599551641)
                      ·
                        rfl

theorem cell23_809618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_809618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809618 prefixEnd_809618 := by exact prefixLift 809618
  have htrace : WordTrace (prefixWord ++ tailWord_809618) baseStart_809618 baseEnd_809618 := by
    simpa [prefixWord, tailWord_809618, baseEnd_809618] using wordTrace_append hprefix tailTrace_809618
  have hstable : (prefixWord ++ tailWord_809618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809618).length < 2 ^ (prefixWord ++ tailWord_809618).sum := by decide
  have hdescent : baseEnd_809618 < baseStart_809618 := by decide
  rcases family_descends (prefixWord ++ tailWord_809618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809664 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_809664 : Nat := 118140960795 + 809664 * 2 ^ 59
def prefixEnd_809664 : Nat := 4983230072969 + 3 ^ 40 * 809664 * 2
def baseEnd_809664 : Nat := 415746800642025419576429

theorem tailTrace_809664 : CollatzResearch.WordTrace tailWord_809664 prefixEnd_809664 415746800642025419576429 := by
  unfold tailWord_809664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765436069366541223654023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19687248092488721631538697 14765436069366541223654023)
  ·
    refine ⟨22148154104049811835481035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14765436069366541223654023 22148154104049811835481035)
    ·
      refine ⟨33222231156074717753221553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22148154104049811835481035 33222231156074717753221553)
      ·
        refine ⟨24916673367056038314916165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33222231156074717753221553 24916673367056038314916165)
        ·
          refine ⟨4671876256323007184046781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24916673367056038314916165 4671876256323007184046781)
          ·
            refine ⟨1751953596121127694017543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4671876256323007184046781 1751953596121127694017543)
            ·
              refine ⟨2627930394181691541026315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751953596121127694017543 2627930394181691541026315)
              ·
                refine ⟨3941895591272537311539473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627930394181691541026315 3941895591272537311539473)
                ·
                  refine ⟨2956421693454402983654605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941895591272537311539473 2956421693454402983654605)
                  ·
                    refine ⟨1108658135045401118870477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956421693454402983654605 1108658135045401118870477)
                    ·
                      refine ⟨415746800642025419576429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108658135045401118870477 415746800642025419576429)
                      ·
                        rfl

theorem cell23_809664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_809664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809664 prefixEnd_809664 := by exact prefixLift 809664
  have htrace : WordTrace (prefixWord ++ tailWord_809664) baseStart_809664 baseEnd_809664 := by
    simpa [prefixWord, tailWord_809664, baseEnd_809664] using wordTrace_append hprefix tailTrace_809664
  have hstable : (prefixWord ++ tailWord_809664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809664).length < 2 ^ (prefixWord ++ tailWord_809664).sum := by decide
  have hdescent : baseEnd_809664 < baseStart_809664 := by decide
  rcases family_descends (prefixWord ++ tailWord_809664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809665 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_809665 : Nat := 118140960795 + 809665 * 2 ^ 59
def prefixEnd_809665 : Nat := 4983230072969 + 3 ^ 40 * 809665 * 2
def baseEnd_809665 : Nat := 415747314122679915663925

theorem tailTrace_809665 : CollatzResearch.WordTrace tailWord_809665 prefixEnd_809665 415747314122679915663925 := by
  unfold tailWord_809665
  simp only [CollatzResearch.WordTrace]
  refine ⟨29530908611729459618094449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19687272407819639745396299 29530908611729459618094449)
  ·
    refine ⟨22148181458797094713570837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29530908611729459618094449 22148181458797094713570837)
    ·
      refine ⟨1038196005881113814698633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22148181458797094713570837 1038196005881113814698633)
      ·
        refine ⟨778647004410835361023975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038196005881113814698633 778647004410835361023975)
        ·
          refine ⟨1167970506616253041535963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778647004410835361023975 1167970506616253041535963)
          ·
            refine ⟨1751955759924379562303945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167970506616253041535963 1751955759924379562303945)
            ·
              refine ⟨1313966819943284671727959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751955759924379562303945 1313966819943284671727959)
              ·
                refine ⟨1970950229914927007591939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313966819943284671727959 1970950229914927007591939)
                ·
                  refine ⟨2956425344872390511387909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970950229914927007591939 2956425344872390511387909)
                  ·
                    refine ⟨554329752163573220885233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956425344872390511387909 554329752163573220885233)
                    ·
                      refine ⟨415747314122679915663925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554329752163573220885233 415747314122679915663925)
                      ·
                        rfl

theorem cell23_809665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_809665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809665 prefixEnd_809665 := by exact prefixLift 809665
  have htrace : WordTrace (prefixWord ++ tailWord_809665) baseStart_809665 baseEnd_809665 := by
    simpa [prefixWord, tailWord_809665, baseEnd_809665] using wordTrace_append hprefix tailTrace_809665
  have hstable : (prefixWord ++ tailWord_809665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809665).length < 2 ^ (prefixWord ++ tailWord_809665).sum := by decide
  have hdescent : baseEnd_809665 < baseStart_809665 := by decide
  rcases family_descends (prefixWord ++ tailWord_809665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809724 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_809724 : Nat := 118140960795 + 809724 * 2 ^ 59
def prefixEnd_809724 : Nat := 4983230072969 + 3 ^ 40 * 809724 * 2
def baseEnd_809724 : Nat := 415777609481295184826153

theorem tailTrace_809724 : CollatzResearch.WordTrace tailWord_809724 prefixEnd_809724 415777609481295184826153 := by
  unfold tailWord_809724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766530259257856347246113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19688707012343808462994817 14766530259257856347246113)
  ·
    refine ⟨11074897694443392260434585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14766530259257856347246113 11074897694443392260434585)
    ·
      refine ⟨8306173270832544195325939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11074897694443392260434585 8306173270832544195325939)
      ·
        refine ⟨12459259906248816292988909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8306173270832544195325939 12459259906248816292988909)
        ·
          refine ⟨4672222464843306109870841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12459259906248816292988909 4672222464843306109870841)
          ·
            refine ⟨3504166848632479582403131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672222464843306109870841 3504166848632479582403131)
            ·
              refine ⟨5256250272948719373604697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504166848632479582403131 5256250272948719373604697)
              ·
                refine ⟨3942187704711539530203523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256250272948719373604697 3942187704711539530203523)
                ·
                  refine ⟨5913281557067309295305285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942187704711539530203523 5913281557067309295305285)
                  ·
                    refine ⟨1108740291950120492869741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913281557067309295305285 1108740291950120492869741)
                    ·
                      refine ⟨415777609481295184826153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108740291950120492869741 415777609481295184826153)
                      ·
                        rfl

theorem cell23_809724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_809724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809724 prefixEnd_809724 := by exact prefixLift 809724
  have htrace : WordTrace (prefixWord ++ tailWord_809724) baseStart_809724 baseEnd_809724 := by
    simpa [prefixWord, tailWord_809724, baseEnd_809724] using wordTrace_append hprefix tailTrace_809724
  have hstable : (prefixWord ++ tailWord_809724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809724).length < 2 ^ (prefixWord ++ tailWord_809724).sum := by decide
  have hdescent : baseEnd_809724 < baseStart_809724 := by decide
  rcases family_descends (prefixWord ++ tailWord_809724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809791 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 1, 5]
def baseStart_809791 : Nat := 118140960795 + 809791 * 2 ^ 59
def prefixEnd_809791 : Nat := 4983230072969 + 3 ^ 40 * 809791 * 2
def baseEnd_809791 : Nat := 138604004228382140896115

theorem tailTrace_809791 : CollatzResearch.WordTrace tailWord_809791 prefixEnd_809791 138604004228382140896115 := by
  unfold tailWord_809791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29535504209272983137181227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19690336139515322091454151 29535504209272983137181227)
  ·
    refine ⟨44303256313909474705771841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29535504209272983137181227 44303256313909474705771841)
    ·
      refine ⟨33227442235432106029328881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44303256313909474705771841 33227442235432106029328881)
      ·
        refine ⟨24920581676574079521996661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33227442235432106029328881 24920581676574079521996661)
        ·
          refine ⟨2336304532178819955187187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24920581676574079521996661 2336304532178819955187187)
          ·
            refine ⟨3504456798268229932780781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336304532178819955187187 3504456798268229932780781)
            ·
              refine ⟨1314171299350586224792793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3504456798268229932780781 1314171299350586224792793)
              ·
                refine ⟨985628474512939668594595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314171299350586224792793 985628474512939668594595)
                ·
                  refine ⟨1478442711769409502891893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985628474512939668594595 1478442711769409502891893)
                  ·
                    refine ⟨138604004228382140896115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1478442711769409502891893 138604004228382140896115)
                    ·
                      rfl

theorem cell23_809791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_809791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809791 prefixEnd_809791 := by exact prefixLift 809791
  have htrace : WordTrace (prefixWord ++ tailWord_809791) baseStart_809791 baseEnd_809791 := by
    simpa [prefixWord, tailWord_809791, baseEnd_809791] using wordTrace_append hprefix tailTrace_809791
  have hstable : (prefixWord ++ tailWord_809791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809791).length < 2 ^ (prefixWord ++ tailWord_809791).sum := by decide
  have hdescent : baseEnd_809791 < baseStart_809791 := by decide
  rcases family_descends (prefixWord ++ tailWord_809791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809804 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_809804 : Nat := 118140960795 + 809804 * 2 ^ 59
def prefixEnd_809804 : Nat := 4983230072969 + 3 ^ 40 * 809804 * 2
def baseEnd_809804 : Nat := 138606229311218290608595

theorem tailTrace_809804 : CollatzResearch.WordTrace tailWord_809804 prefixEnd_809804 138606229311218290608595 := by
  unfold tailWord_809804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767989179112943178702233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19690652238817257571602977 14767989179112943178702233)
  ·
    refine ⟨11075991884334707384026675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14767989179112943178702233 11075991884334707384026675)
    ·
      refine ⟨16613987826502061076040013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075991884334707384026675 16613987826502061076040013)
      ·
        refine ⟨6230245434938272903515005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16613987826502061076040013 6230245434938272903515005)
        ·
          refine ⟨2336342038101852338818127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6230245434938272903515005 2336342038101852338818127)
          ·
            refine ⟨3504513057152778508227191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336342038101852338818127 3504513057152778508227191)
            ·
              refine ⟨5256769585729167762340787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504513057152778508227191 5256769585729167762340787)
              ·
                refine ⟨7885154378593751643511181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256769585729167762340787 7885154378593751643511181)
                ·
                  refine ⟨2956932891972656866316693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7885154378593751643511181 2956932891972656866316693)
                  ·
                    refine ⟨138606229311218290608595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2956932891972656866316693 138606229311218290608595)
                    ·
                      rfl

theorem cell23_809804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_809804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809804 prefixEnd_809804 := by exact prefixLift 809804
  have htrace : WordTrace (prefixWord ++ tailWord_809804) baseStart_809804 baseEnd_809804 := by
    simpa [prefixWord, tailWord_809804, baseEnd_809804] using wordTrace_append hprefix tailTrace_809804
  have hstable : (prefixWord ++ tailWord_809804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809804).length < 2 ^ (prefixWord ++ tailWord_809804).sum := by decide
  have hdescent : baseEnd_809804 < baseStart_809804 := by decide
  rcases family_descends (prefixWord ++ tailWord_809804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809807 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_809807 : Nat := 118140960795 + 809807 * 2 ^ 59
def prefixEnd_809807 : Nat := 4983230072969 + 3 ^ 40 * 809807 * 2
def baseEnd_809807 : Nat := 415820228375618360088271

theorem tailTrace_809807 : CollatzResearch.WordTrace tailWord_809807 prefixEnd_809807 415820228375618360088271 := by
  unfold tailWord_809807
  simp only [CollatzResearch.WordTrace]
  refine ⟨29536087777215017869763675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19690725184810011913175783 29536087777215017869763675)
  ·
    refine ⟨44304131665822526804645513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29536087777215017869763675 44304131665822526804645513)
    ·
      refine ⟨33228098749366895103484135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44304131665822526804645513 33228098749366895103484135)
      ·
        refine ⟨49842148124050342655226203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33228098749366895103484135 49842148124050342655226203)
        ·
          refine ⟨74763222186075513982839305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49842148124050342655226203 74763222186075513982839305)
          ·
            refine ⟨56072416639556635487129479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74763222186075513982839305 56072416639556635487129479)
            ·
              refine ⟨84108624959334953230694219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56072416639556635487129479 84108624959334953230694219)
              ·
                refine ⟨126162937439002429846041329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84108624959334953230694219 126162937439002429846041329)
                ·
                  refine ⟨94622203079251822384530997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126162937439002429846041329 94622203079251822384530997)
                  ·
                    refine ⟨8870831538679858348549781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94622203079251822384530997 8870831538679858348549781)
                    ·
                      refine ⟨415820228375618360088271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8870831538679858348549781 415820228375618360088271)
                      ·
                        rfl

theorem cell23_809807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_809807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809807 prefixEnd_809807 := by exact prefixLift 809807
  have htrace : WordTrace (prefixWord ++ tailWord_809807) baseStart_809807 baseEnd_809807 := by
    simpa [prefixWord, tailWord_809807, baseEnd_809807] using wordTrace_append hprefix tailTrace_809807
  have hstable : (prefixWord ++ tailWord_809807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809807).length < 2 ^ (prefixWord ++ tailWord_809807).sum := by decide
  have hdescent : baseEnd_809807 < baseStart_809807 := by decide
  rcases family_descends (prefixWord ++ tailWord_809807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809817 : List Nat := [1, 2, 1, 2, 2, 15]
def baseStart_809817 : Nat := 118140960795 + 809817 * 2 ^ 59
def prefixEnd_809817 : Nat := 4983230072969 + 3 ^ 40 * 809817 * 2
def baseEnd_809817 : Nat := 1711215486346351115075

theorem tailTrace_809817 : CollatzResearch.WordTrace tailWord_809817 prefixEnd_809817 1711215486346351115075 := by
  unfold tailWord_809817
  simp only [CollatzResearch.WordTrace]
  refine ⟨29536452507178789577627705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19690968338119193051751803 29536452507178789577627705)
  ·
    refine ⟨22152339380384092183220779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29536452507178789577627705 22152339380384092183220779)
    ·
      refine ⟨33228509070576138274831169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22152339380384092183220779 33228509070576138274831169)
      ·
        refine ⟨24921381802932103706123377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33228509070576138274831169 24921381802932103706123377)
        ·
          refine ⟨18691036352199077779592533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24921381802932103706123377 18691036352199077779592533)
          ·
            refine ⟨1711215486346351115075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 18691036352199077779592533 1711215486346351115075)
            ·
              rfl

theorem cell23_809817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 15].length) (baseStart_809817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809817 prefixEnd_809817 := by exact prefixLift 809817
  have htrace : WordTrace (prefixWord ++ tailWord_809817) baseStart_809817 baseEnd_809817 := by
    simpa [prefixWord, tailWord_809817, baseEnd_809817] using wordTrace_append hprefix tailTrace_809817
  have hstable : (prefixWord ++ tailWord_809817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809817).length < 2 ^ (prefixWord ++ tailWord_809817).sum := by decide
  have hdescent : baseEnd_809817 < baseStart_809817 := by decide
  rcases family_descends (prefixWord ++ tailWord_809817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809824 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_809824 : Nat := 118140960795 + 809824 * 2 ^ 59
def prefixEnd_809824 : Nat := 4983230072969 + 3 ^ 40 * 809824 * 2
def baseEnd_809824 : Nat := 415828957546744793575693

theorem tailTrace_809824 : CollatzResearch.WordTrace tailWord_809824 prefixEnd_809824 415828957546744793575693 := by
  unfold tailWord_809824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768353909076714886566263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19691138545435619848755017 14768353909076714886566263)
  ·
    refine ⟨22152530863615072329849395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14768353909076714886566263 22152530863615072329849395)
    ·
      refine ⟨33228796295422608494774093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22152530863615072329849395 33228796295422608494774093)
      ·
        refine ⟨12460798610783478185540285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33228796295422608494774093 12460798610783478185540285)
        ·
          refine ⟨4672799479043804319577607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12460798610783478185540285 4672799479043804319577607)
          ·
            refine ⟨7009199218565706479366411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672799479043804319577607 7009199218565706479366411)
            ·
              refine ⟨10513798827848559719049617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009199218565706479366411 10513798827848559719049617)
              ·
                refine ⟨7885349120886419789287213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10513798827848559719049617 7885349120886419789287213)
                ·
                  refine ⟨2957005920332407420982705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7885349120886419789287213 2957005920332407420982705)
                  ·
                    refine ⟨2217754440249305565737029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957005920332407420982705 2217754440249305565737029)
                    ·
                      refine ⟨415828957546744793575693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2217754440249305565737029 415828957546744793575693)
                      ·
                        rfl

theorem cell23_809824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_809824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809824 prefixEnd_809824 := by exact prefixLift 809824
  have htrace : WordTrace (prefixWord ++ tailWord_809824) baseStart_809824 baseEnd_809824 := by
    simpa [prefixWord, tailWord_809824, baseEnd_809824] using wordTrace_append hprefix tailTrace_809824
  have hstable : (prefixWord ++ tailWord_809824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809824).length < 2 ^ (prefixWord ++ tailWord_809824).sum := by decide
  have hdescent : baseEnd_809824 < baseStart_809824 := by decide
  rcases family_descends (prefixWord ++ tailWord_809824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809831 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_809831 : Nat := 118140960795 + 809831 * 2 ^ 59
def prefixEnd_809831 : Nat := 4983230072969 + 3 ^ 40 * 809831 * 2
def baseEnd_809831 : Nat := 415832551911326266188161

theorem tailTrace_809831 : CollatzResearch.WordTrace tailWord_809831 prefixEnd_809831 415832551911326266188161 := by
  unfold tailWord_809831
  simp only [CollatzResearch.WordTrace]
  refine ⟨29536963129128069968637347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19691308752752046645758231 29536963129128069968637347)
  ·
    refine ⟨44305444693692104952956021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29536963129128069968637347 44305444693692104952956021)
    ·
      refine ⟨4153635440033634839339627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44305444693692104952956021 4153635440033634839339627)
      ·
        refine ⟨6230453160050452259009441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153635440033634839339627 6230453160050452259009441)
        ·
          refine ⟨4672839870037839194257081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230453160050452259009441 4672839870037839194257081)
          ·
            refine ⟨3504629902528379395692811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672839870037839194257081 3504629902528379395692811)
            ·
              refine ⟨5256944853792569093539217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504629902528379395692811 5256944853792569093539217)
              ·
                refine ⟨3942708640344426820154413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256944853792569093539217 3942708640344426820154413)
                ·
                  refine ⟨1478515740129160057557905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942708640344426820154413 1478515740129160057557905)
                  ·
                    refine ⟨1108886805096870043168429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478515740129160057557905 1108886805096870043168429)
                    ·
                      refine ⟨415832551911326266188161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108886805096870043168429 415832551911326266188161)
                      ·
                        rfl

theorem cell23_809831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_809831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809831 prefixEnd_809831 := by exact prefixLift 809831
  have htrace : WordTrace (prefixWord ++ tailWord_809831) baseStart_809831 baseEnd_809831 := by
    simpa [prefixWord, tailWord_809831, baseEnd_809831] using wordTrace_append hprefix tailTrace_809831
  have hstable : (prefixWord ++ tailWord_809831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809831).length < 2 ^ (prefixWord ++ tailWord_809831).sum := by decide
  have hdescent : baseEnd_809831 < baseStart_809831 := by decide
  rcases family_descends (prefixWord ++ tailWord_809831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809838 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_809838 : Nat := 118140960795 + 809838 * 2 ^ 59
def prefixEnd_809838 : Nat := 4983230072969 + 3 ^ 40 * 809838 * 2
def baseEnd_809838 : Nat := 138612048758635912933543

theorem tailTrace_809838 : CollatzResearch.WordTrace tailWord_809838 prefixEnd_809838 138612048758635912933543 := by
  unfold tailWord_809838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692152305012838770517771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19691478960068473442761445 3692152305012838770517771)
  ·
    refine ⟨5538228457519258155776657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3692152305012838770517771 5538228457519258155776657)
    ·
      refine ⟨4153671343139443616832493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5538228457519258155776657 4153671343139443616832493)
      ·
        refine ⟨1557626753677291356312185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4153671343139443616832493 1557626753677291356312185)
        ·
          refine ⟨1168220065257968517234139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557626753677291356312185 1168220065257968517234139)
          ·
            refine ⟨1752330097886952775851209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168220065257968517234139 1752330097886952775851209)
            ·
              refine ⟨1314247573415214581888407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752330097886952775851209 1314247573415214581888407)
              ·
                refine ⟨1971371360122821872832611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314247573415214581888407 1971371360122821872832611)
                ·
                  refine ⟨2957057040184232809248917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971371360122821872832611 2957057040184232809248917)
                  ·
                    refine ⟨138612048758635912933543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2957057040184232809248917 138612048758635912933543)
                    ·
                      rfl

theorem cell23_809838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_809838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809838 prefixEnd_809838 := by exact prefixLift 809838
  have htrace : WordTrace (prefixWord ++ tailWord_809838) baseStart_809838 baseEnd_809838 := by
    simpa [prefixWord, tailWord_809838, baseEnd_809838] using wordTrace_append hprefix tailTrace_809838
  have hstable : (prefixWord ++ tailWord_809838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809838).length < 2 ^ (prefixWord ++ tailWord_809838).sum := by decide
  have hdescent : baseEnd_809838 < baseStart_809838 := by decide
  rcases family_descends (prefixWord ++ tailWord_809838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809841 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_809841 : Nat := 118140960795 + 809841 * 2 ^ 59
def prefixEnd_809841 : Nat := 4983230072969 + 3 ^ 40 * 809841 * 2
def baseEnd_809841 : Nat := 415837686717871227063115

theorem tailTrace_809841 : CollatzResearch.WordTrace tailWord_809841 prefixEnd_809841 415837686717871227063115 := by
  unfold tailWord_809841
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537327859091841676501377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19691551906061227784334251 29537327859091841676501377)
  ·
    refine ⟨22152995894318881257376033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29537327859091841676501377 22152995894318881257376033)
    ·
      refine ⟨16614746920739160943032025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22152995894318881257376033 16614746920739160943032025)
      ·
        refine ⟨12461060190554370707274019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16614746920739160943032025 12461060190554370707274019)
        ·
          refine ⟨18691590285831556060911029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461060190554370707274019 18691590285831556060911029)
          ·
            refine ⟨1752336589296708380710409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18691590285831556060911029 1752336589296708380710409)
            ·
              refine ⟨1314252441972531285532807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752336589296708380710409 1314252441972531285532807)
              ·
                refine ⟨1971378662958796928299211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314252441972531285532807 1971378662958796928299211)
                ·
                  refine ⟨2957067994438195392448817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971378662958796928299211 2957067994438195392448817)
                  ·
                    refine ⟨2217800995828646544336613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957067994438195392448817 2217800995828646544336613)
                    ·
                      refine ⟨415837686717871227063115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2217800995828646544336613 415837686717871227063115)
                      ·
                        rfl

theorem cell23_809841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_809841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809841 prefixEnd_809841 := by exact prefixLift 809841
  have htrace : WordTrace (prefixWord ++ tailWord_809841) baseStart_809841 baseEnd_809841 := by
    simpa [prefixWord, tailWord_809841, baseEnd_809841] using wordTrace_append hprefix tailTrace_809841
  have hstable : (prefixWord ++ tailWord_809841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809841).length < 2 ^ (prefixWord ++ tailWord_809841).sum := by decide
  have hdescent : baseEnd_809841 < baseStart_809841 := by decide
  rcases family_descends (prefixWord ++ tailWord_809841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809845 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_809845 : Nat := 118140960795 + 809845 * 2 ^ 59
def prefixEnd_809845 : Nat := 4983230072969 + 3 ^ 40 * 809845 * 2
def baseEnd_809845 : Nat := 415839740640489211413097

theorem tailTrace_809845 : CollatzResearch.WordTrace tailWord_809845 prefixEnd_809845 415839740640489211413097 := by
  unfold tailWord_809845
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537473751077350359646989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19691649167384900239764659 29537473751077350359646989)
  ·
    refine ⟨11076552656654006384867621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29537473751077350359646989 11076552656654006384867621)
    ·
      refine ⟨2076853623122626197162679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11076552656654006384867621 2076853623122626197162679)
      ·
        refine ⟨3115280434683939295744019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076853623122626197162679 3115280434683939295744019)
        ·
          refine ⟨4672920652025908943616029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115280434683939295744019 4672920652025908943616029)
          ·
            refine ⟨1752345244509715853856011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672920652025908943616029 1752345244509715853856011)
            ·
              refine ⟨2628517866764573780784017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752345244509715853856011 2628517866764573780784017)
              ·
                refine ⟨1971388400073430335588013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628517866764573780784017 1971388400073430335588013)
                ·
                  refine ⟨739270650027536375845505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1971388400073430335588013 739270650027536375845505)
                  ·
                    refine ⟨554452987520652281884129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 739270650027536375845505 554452987520652281884129)
                    ·
                      refine ⟨415839740640489211413097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554452987520652281884129 415839740640489211413097)
                      ·
                        rfl

theorem cell23_809845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_809845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809845 prefixEnd_809845 := by exact prefixLift 809845
  have htrace : WordTrace (prefixWord ++ tailWord_809845) baseStart_809845 baseEnd_809845 := by
    simpa [prefixWord, tailWord_809845, baseEnd_809845] using wordTrace_append hprefix tailTrace_809845
  have hstable : (prefixWord ++ tailWord_809845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809845).length < 2 ^ (prefixWord ++ tailWord_809845).sum := by decide
  have hdescent : baseEnd_809845 < baseStart_809845 := by decide
  rcases family_descends (prefixWord ++ tailWord_809845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809861 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_809861 : Nat := 118140960795 + 809861 * 2 ^ 59
def prefixEnd_809861 : Nat := 4983230072969 + 3 ^ 40 * 809861 * 2
def baseEnd_809861 : Nat := 415847956330961148813023

theorem tailTrace_809861 : CollatzResearch.WordTrace tailWord_809861 prefixEnd_809861 415847956330961148813023 := by
  unfold tailWord_809861
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538057319019385092229437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19692038212679590061486291 29538057319019385092229437)
  ·
    refine ⟨11076771494632269409586039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29538057319019385092229437 11076771494632269409586039)
    ·
      refine ⟨16615157241948404114379059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11076771494632269409586039 16615157241948404114379059)
      ·
        refine ⟨24922735862922606171568589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16615157241948404114379059 24922735862922606171568589)
        ·
          refine ⟨9346025948595977314338221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24922735862922606171568589 9346025948595977314338221)
          ·
            refine ⟨3504759730723491492876833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9346025948595977314338221 3504759730723491492876833)
            ·
              refine ⟨2628569798042618619657625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504759730723491492876833 2628569798042618619657625)
              ·
                refine ⟨1971427348531963964743219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628569798042618619657625 1971427348531963964743219)
                ·
                  refine ⟨2957141022797945947114829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971427348531963964743219 2957141022797945947114829)
                  ·
                    refine ⟨1108927883549229730168061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957141022797945947114829 1108927883549229730168061)
                    ·
                      refine ⟨415847956330961148813023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108927883549229730168061 415847956330961148813023)
                      ·
                        rfl

theorem cell23_809861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_809861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809861 prefixEnd_809861 := by exact prefixLift 809861
  have htrace : WordTrace (prefixWord ++ tailWord_809861) baseStart_809861 baseEnd_809861 := by
    simpa [prefixWord, tailWord_809861, baseEnd_809861] using wordTrace_append hprefix tailTrace_809861
  have hstable : (prefixWord ++ tailWord_809861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809861).length < 2 ^ (prefixWord ++ tailWord_809861).sum := by decide
  have hdescent : baseEnd_809861 < baseStart_809861 := by decide
  rcases family_descends (prefixWord ++ tailWord_809861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809865 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 1, 2, 3]
def baseStart_809865 : Nat := 118140960795 + 809865 * 2 ^ 59
def prefixEnd_809865 : Nat := 4983230072969 + 3 ^ 40 * 809865 * 2
def baseEnd_809865 : Nat := 415850010253579133163005

theorem tailTrace_809865 : CollatzResearch.WordTrace tailWord_809865 prefixEnd_809865 415850010253579133163005 := by
  unfold tailWord_809865
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538203211004893775375049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19692135474003262516916699 29538203211004893775375049)
  ·
    refine ⟨22153652408253670331531287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29538203211004893775375049 22153652408253670331531287)
    ·
      refine ⟨33230478612380505497296931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22153652408253670331531287 33230478612380505497296931)
      ·
        refine ⟨49845717918570758245945397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33230478612380505497296931 49845717918570758245945397)
        ·
          refine ⟨4673036054866008585557381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49845717918570758245945397 4673036054866008585557381)
          ·
            refine ⟨876194260287376609792009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4673036054866008585557381 876194260287376609792009)
            ·
              refine ⟨657145695215532457344007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876194260287376609792009 657145695215532457344007)
              ·
                refine ⟨985718542823298686016011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657145695215532457344007 985718542823298686016011)
                ·
                  refine ⟨1478577814234948029024017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985718542823298686016011 1478577814234948029024017)
                  ·
                    refine ⟨1108933360676211021768013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478577814234948029024017 1108933360676211021768013)
                    ·
                      refine ⟨415850010253579133163005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108933360676211021768013 415850010253579133163005)
                      ·
                        rfl

theorem cell23_809865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 2, 3].length) (baseStart_809865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809865 prefixEnd_809865 := by exact prefixLift 809865
  have htrace : WordTrace (prefixWord ++ tailWord_809865) baseStart_809865 baseEnd_809865 := by
    simpa [prefixWord, tailWord_809865, baseEnd_809865] using wordTrace_append hprefix tailTrace_809865
  have hstable : (prefixWord ++ tailWord_809865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809865).length < 2 ^ (prefixWord ++ tailWord_809865).sum := by decide
  have hdescent : baseEnd_809865 < baseStart_809865 := by decide
  rcases family_descends (prefixWord ++ tailWord_809865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809895 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_809895 : Nat := 118140960795 + 809895 * 2 ^ 59
def prefixEnd_809895 : Nat := 4983230072969 + 3 ^ 40 * 809895 * 2
def baseEnd_809895 : Nat := 415865414673214015787867

theorem tailTrace_809895 : CollatzResearch.WordTrace tailWord_809895 prefixEnd_809895 415865414673214015787867 := by
  unfold tailWord_809895
  simp only [CollatzResearch.WordTrace]
  refine ⟨29539297400896208898967139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19692864933930805932644759 29539297400896208898967139)
  ·
    refine ⟨44308946101344313348450709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29539297400896208898967139 44308946101344313348450709)
    ·
      refine ⟨2076981848500514688208627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44308946101344313348450709 2076981848500514688208627)
      ·
        refine ⟨3115472772750772032312941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076981848500514688208627 3115472772750772032312941)
        ·
          refine ⟨1168302289781539512117353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3115472772750772032312941 1168302289781539512117353)
          ·
            refine ⟨876226717336154634088015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168302289781539512117353 876226717336154634088015)
            ·
              refine ⟨1314340076004231951132023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876226717336154634088015 1314340076004231951132023)
              ·
                refine ⟨1971510114006347926698035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314340076004231951132023 1971510114006347926698035)
                ·
                  refine ⟨2957265171009521890047053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971510114006347926698035 2957265171009521890047053)
                  ·
                    refine ⟨1108974439128570708767645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957265171009521890047053 1108974439128570708767645)
                    ·
                      refine ⟨415865414673214015787867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1108974439128570708767645 415865414673214015787867)
                      ·
                        rfl

theorem cell23_809895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_809895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809895 prefixEnd_809895 := by exact prefixLift 809895
  have htrace : WordTrace (prefixWord ++ tailWord_809895) baseStart_809895 baseEnd_809895 := by
    simpa [prefixWord, tailWord_809895, baseEnd_809895] using wordTrace_append hprefix tailTrace_809895
  have hstable : (prefixWord ++ tailWord_809895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809895).length < 2 ^ (prefixWord ++ tailWord_809895).sum := by decide
  have hdescent : baseEnd_809895 < baseStart_809895 := by decide
  rcases family_descends (prefixWord ++ tailWord_809895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809908 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_809908 : Nat := 118140960795 + 809908 * 2 ^ 59
def prefixEnd_809908 : Nat := 4983230072969 + 3 ^ 40 * 809908 * 2
def baseEnd_809908 : Nat := 415872089921722464925307

theorem tailTrace_809908 : CollatzResearch.WordTrace tailWord_809908 prefixEnd_809908 415872089921722464925307 := by
  unfold tailWord_809908
  simp only [CollatzResearch.WordTrace]
  refine ⟨14769885774924556059595189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19693181033232741412793585 14769885774924556059595189)
  ·
    refine ⟨1384676791399177130587049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14769885774924556059595189 1384676791399177130587049)
    ·
      refine ⟨1038507593549382847940287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1384676791399177130587049 1038507593549382847940287)
      ·
        refine ⟨1557761390324074271910431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038507593549382847940287 1557761390324074271910431)
        ·
          refine ⟨2336642085486111407865647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557761390324074271910431 2336642085486111407865647)
          ·
            refine ⟨3504963128229167111798471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336642085486111407865647 3504963128229167111798471)
            ·
              refine ⟨5257444692343750667697707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504963128229167111798471 5257444692343750667697707)
              ·
                refine ⟨7886167038515626001546561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257444692343750667697707 7886167038515626001546561)
                ·
                  refine ⟨5914625278886719501159921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886167038515626001546561 5914625278886719501159921)
                  ·
                    refine ⟨4435968959165039625869941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5914625278886719501159921 4435968959165039625869941)
                    ·
                      refine ⟨415872089921722464925307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4435968959165039625869941 415872089921722464925307)
                      ·
                        rfl

theorem cell23_809908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_809908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809908 prefixEnd_809908 := by exact prefixLift 809908
  have htrace : WordTrace (prefixWord ++ tailWord_809908) baseStart_809908 baseEnd_809908 := by
    simpa [prefixWord, tailWord_809908, baseEnd_809908] using wordTrace_append hprefix tailTrace_809908
  have hstable : (prefixWord ++ tailWord_809908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809908).length < 2 ^ (prefixWord ++ tailWord_809908).sum := by decide
  have hdescent : baseEnd_809908 < baseStart_809908 := by decide
  rcases family_descends (prefixWord ++ tailWord_809908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809918 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_809918 : Nat := 118140960795 + 809918 * 2 ^ 59
def prefixEnd_809918 : Nat := 4983230072969 + 3 ^ 40 * 809918 * 2
def baseEnd_809918 : Nat := 415877224728267425800261

theorem tailTrace_809918 : CollatzResearch.WordTrace tailWord_809918 prefixEnd_809918 415877224728267425800261 := by
  unfold tailWord_809918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692517034976610478381801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19693424186541922551369605 3692517034976610478381801)
  ·
    refine ⟨2769387776232457858786351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3692517034976610478381801 2769387776232457858786351)
    ·
      refine ⟨4154081664348686788179527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769387776232457858786351 4154081664348686788179527)
      ·
        refine ⟨6231122496523030182269291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154081664348686788179527 6231122496523030182269291)
        ·
          refine ⟨9346683744784545273403937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231122496523030182269291 9346683744784545273403937)
          ·
            refine ⟨7010012808588408955052953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9346683744784545273403937 7010012808588408955052953)
            ·
              refine ⟨5257509606441306716289715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010012808588408955052953 5257509606441306716289715)
              ·
                refine ⟨7886264409661960074434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257509606441306716289715 7886264409661960074434573)
                ·
                  refine ⟨2957349153623235027912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7886264409661960074434573 2957349153623235027912965)
                  ·
                    refine ⟨554502966304356567733681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2957349153623235027912965 554502966304356567733681)
                    ·
                      refine ⟨415877224728267425800261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554502966304356567733681 415877224728267425800261)
                      ·
                        rfl

theorem cell23_809918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_809918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809918 prefixEnd_809918 := by exact prefixLift 809918
  have htrace : WordTrace (prefixWord ++ tailWord_809918) baseStart_809918 baseEnd_809918 := by
    simpa [prefixWord, tailWord_809918, baseEnd_809918] using wordTrace_append hprefix tailTrace_809918
  have hstable : (prefixWord ++ tailWord_809918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809918).length < 2 ^ (prefixWord ++ tailWord_809918).sum := by decide
  have hdescent : baseEnd_809918 < baseStart_809918 := by decide
  rcases family_descends (prefixWord ++ tailWord_809918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809984 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_809984 : Nat := 118140960795 + 809984 * 2 ^ 59
def prefixEnd_809984 : Nat := 4983230072969 + 3 ^ 40 * 809984 * 2
def baseEnd_809984 : Nat := 138637038150488055858319

theorem tailTrace_809984 : CollatzResearch.WordTrace tailWord_809984 prefixEnd_809984 138637038150488055858319 := by
  unfold tailWord_809984
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771271748786888549478503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19695028998382518065971337 14771271748786888549478503)
  ·
    refine ⟨22156907623180332824217755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14771271748786888549478503 22156907623180332824217755)
    ·
      refine ⟨33235361434770499236326633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22156907623180332824217755 33235361434770499236326633)
      ·
        refine ⟨24926521076077874427244975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33235361434770499236326633 24926521076077874427244975)
        ·
          refine ⟨37389781614116811640867463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24926521076077874427244975 37389781614116811640867463)
          ·
            refine ⟨56084672421175217461301195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37389781614116811640867463 56084672421175217461301195)
            ·
              refine ⟨84127008631762826191951793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56084672421175217461301195 84127008631762826191951793)
              ·
                refine ⟨63095256473822119643963845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84127008631762826191951793 63095256473822119643963845)
                ·
                  refine ⟨11830360588841647433243221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63095256473822119643963845 11830360588841647433243221)
                  ·
                    refine ⟨138637038150488055858319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11830360588841647433243221 138637038150488055858319)
                    ·
                      rfl

theorem cell23_809984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_809984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809984 prefixEnd_809984 := by exact prefixLift 809984
  have htrace : WordTrace (prefixWord ++ tailWord_809984) baseStart_809984 baseEnd_809984 := by
    simpa [prefixWord, tailWord_809984, baseEnd_809984] using wordTrace_append hprefix tailTrace_809984
  have hstable : (prefixWord ++ tailWord_809984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809984).length < 2 ^ (prefixWord ++ tailWord_809984).sum := by decide
  have hdescent : baseEnd_809984 < baseStart_809984 := by decide
  rcases family_descends (prefixWord ++ tailWord_809984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809986 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_809986 : Nat := 118140960795 + 809986 * 2 ^ 59
def prefixEnd_809986 : Nat := 4983230072969 + 3 ^ 40 * 809986 * 2
def baseEnd_809986 : Nat := 415912141412773159749949

theorem tailTrace_809986 : CollatzResearch.WordTrace tailWord_809986 prefixEnd_809986 415912141412773159749949 := by
  unfold tailWord_809986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7385654110891632860132453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19695077629044354293686541 7385654110891632860132453)
  ·
    refine ⟨1384810145792181161274835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7385654110891632860132453 1384810145792181161274835)
    ·
      refine ⟨2077215218688271741912253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384810145792181161274835 2077215218688271741912253)
      ·
        refine ⟨778955707008101903217095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2077215218688271741912253 778955707008101903217095)
        ·
          refine ⟨1168433560512152854825643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778955707008101903217095 1168433560512152854825643)
          ·
            refine ⟨1752650340768229282238465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168433560512152854825643 1752650340768229282238465)
            ·
              refine ⟨1314487755576171961678849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752650340768229282238465 1314487755576171961678849)
              ·
                refine ⟨985865816682128971259137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314487755576171961678849 985865816682128971259137)
                ·
                  refine ⟨739399362511596728444353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 985865816682128971259137 739399362511596728444353)
                  ·
                    refine ⟨554549521883697546333265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 739399362511596728444353 554549521883697546333265)
                    ·
                      refine ⟨415912141412773159749949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554549521883697546333265 415912141412773159749949)
                      ·
                        rfl

theorem cell23_809986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_809986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_809986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_809986 prefixEnd_809986 := by exact prefixLift 809986
  have htrace : WordTrace (prefixWord ++ tailWord_809986) baseStart_809986 baseEnd_809986 := by
    simpa [prefixWord, tailWord_809986, baseEnd_809986] using wordTrace_append hprefix tailTrace_809986
  have hstable : (prefixWord ++ tailWord_809986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809986).length < 2 ^ (prefixWord ++ tailWord_809986).sum := by decide
  have hdescent : baseEnd_809986 < baseStart_809986 := by decide
  rcases family_descends (prefixWord ++ tailWord_809986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810001 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_810001 : Nat := 118140960795 + 810001 * 2 ^ 59
def prefixEnd_810001 : Nat := 4983230072969 + 3 ^ 40 * 810001 * 2
def baseEnd_810001 : Nat := 138639947874196867020793

theorem tailTrace_810001 : CollatzResearch.WordTrace tailWord_810001 prefixEnd_810001 138639947874196867020793 := by
  unfold tailWord_810001
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543163538512189002325857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19695442359008126001550571 29543163538512189002325857)
  ·
    refine ⟨22157372653884141751744393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29543163538512189002325857 22157372653884141751744393)
    ·
      refine ⟨16618029490413106313808295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22157372653884141751744393 16618029490413106313808295)
      ·
        refine ⟨24927044235619659470712443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16618029490413106313808295 24927044235619659470712443)
        ·
          refine ⟨37390566353429489206068665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24927044235619659470712443 37390566353429489206068665)
          ·
            refine ⟨28042924765072116904551499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37390566353429489206068665 28042924765072116904551499)
            ·
              refine ⟨42064387147608175356827249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28042924765072116904551499 42064387147608175356827249)
              ·
                refine ⟨31548290360706131517620437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42064387147608175356827249 31548290360706131517620437)
                ·
                  refine ⟨739413055329049957444229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31548290360706131517620437 739413055329049957444229)
                  ·
                    refine ⟨138639947874196867020793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739413055329049957444229 138639947874196867020793)
                    ·
                      rfl

theorem cell23_810001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_810001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810001 prefixEnd_810001 := by exact prefixLift 810001
  have htrace : WordTrace (prefixWord ++ tailWord_810001) baseStart_810001 baseEnd_810001 := by
    simpa [prefixWord, tailWord_810001, baseEnd_810001] using wordTrace_append hprefix tailTrace_810001
  have hstable : (prefixWord ++ tailWord_810001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810001).length < 2 ^ (prefixWord ++ tailWord_810001).sum := by decide
  have hdescent : baseEnd_810001 < baseStart_810001 := by decide
  rcases family_descends (prefixWord ++ tailWord_810001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810008 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_810008 : Nat := 118140960795 + 810008 * 2 ^ 59
def prefixEnd_810008 : Nat := 4983230072969 + 3 ^ 40 * 810008 * 2
def baseEnd_810008 : Nat := 415923437987172073674847

theorem tailTrace_810008 : CollatzResearch.WordTrace tailWord_810008 prefixEnd_810008 415923437987172073674847 := by
  unfold tailWord_810008
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771709424743414598915339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19695612566324552798553785 14771709424743414598915339)
  ·
    refine ⟨22157564137115121898373009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14771709424743414598915339 22157564137115121898373009)
    ·
      refine ⟨16618173102836341423779757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22157564137115121898373009 16618173102836341423779757)
      ·
        refine ⟨6231814913563628033917409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16618173102836341423779757 6231814913563628033917409)
        ·
          refine ⟨4673861185172721025438057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6231814913563628033917409 4673861185172721025438057)
          ·
            refine ⟨3505395888879540769078543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4673861185172721025438057 3505395888879540769078543)
            ·
              refine ⟨5258093833319311153617815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505395888879540769078543 5258093833319311153617815)
              ·
                refine ⟨7887140749978966730426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258093833319311153617815 7887140749978966730426723)
                ·
                  refine ⟨11830711124968450095640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7887140749978966730426723 11830711124968450095640085)
                  ·
                    refine ⟨554564583982896098233129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11830711124968450095640085 554564583982896098233129)
                    ·
                      refine ⟨415923437987172073674847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554564583982896098233129 415923437987172073674847)
                      ·
                        rfl

theorem cell23_810008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_810008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810008 prefixEnd_810008 := by exact prefixLift 810008
  have htrace : WordTrace (prefixWord ++ tailWord_810008) baseStart_810008 baseEnd_810008 := by
    simpa [prefixWord, tailWord_810008, baseEnd_810008] using wordTrace_append hprefix tailTrace_810008
  have hstable : (prefixWord ++ tailWord_810008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810008).length < 2 ^ (prefixWord ++ tailWord_810008).sum := by decide
  have hdescent : baseEnd_810008 < baseStart_810008 := by decide
  rcases family_descends (prefixWord ++ tailWord_810008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810018 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_810018 : Nat := 118140960795 + 810018 * 2 ^ 59
def prefixEnd_810018 : Nat := 4983230072969 + 3 ^ 40 * 810018 * 2
def baseEnd_810018 : Nat := 138642857597905678183267

theorem tailTrace_810018 : CollatzResearch.WordTrace tailWord_810018 prefixEnd_810018 138642857597905678183267 := by
  unfold tailWord_810018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7385945894862650226423677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19695855719633733937129805 7385945894862650226423677)
  ·
    refine ⟨2769729710573493834908879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7385945894862650226423677 2769729710573493834908879)
    ·
      refine ⟨4154594565860240752363319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769729710573493834908879 4154594565860240752363319)
      ·
        refine ⟨6231891848790361128544979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154594565860240752363319 6231891848790361128544979)
        ·
          refine ⟨9347837773185541692817469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231891848790361128544979 9347837773185541692817469)
          ·
            refine ⟨3505439164944578134806551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9347837773185541692817469 3505439164944578134806551)
            ·
              refine ⟨5258158747416867202209827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505439164944578134806551 5258158747416867202209827)
              ·
                refine ⟨7887238121125300803314741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258158747416867202209827 7887238121125300803314741)
                ·
                  refine ⟨739428573855496950310757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7887238121125300803314741 739428573855496950310757)
                  ·
                    refine ⟨138642857597905678183267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739428573855496950310757 138642857597905678183267)
                    ·
                      rfl

theorem cell23_810018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_810018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810018 prefixEnd_810018 := by exact prefixLift 810018
  have htrace : WordTrace (prefixWord ++ tailWord_810018) baseStart_810018 baseEnd_810018 := by
    simpa [prefixWord, tailWord_810018, baseEnd_810018] using wordTrace_append hprefix tailTrace_810018
  have hstable : (prefixWord ++ tailWord_810018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810018).length < 2 ^ (prefixWord ++ tailWord_810018).sum := by decide
  have hdescent : baseEnd_810018 < baseStart_810018 := by decide
  rcases family_descends (prefixWord ++ tailWord_810018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810038 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_810038 : Nat := 118140960795 + 810038 * 2 ^ 59
def prefixEnd_810038 : Nat := 4983230072969 + 3 ^ 40 * 810038 * 2
def baseEnd_810038 : Nat := 415938842406806956299709

theorem tailTrace_810038 : CollatzResearch.WordTrace tailWord_810038 prefixEnd_810038 415938842406806956299709 := by
  unfold tailWord_810038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846532064961134020088923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19696342026252096214281845 1846532064961134020088923)
  ·
    refine ⟨2769798097441701030133385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846532064961134020088923 2769798097441701030133385)
    ·
      refine ⟨2077348573081275772600039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2769798097441701030133385 2077348573081275772600039)
      ·
        refine ⟨3116022859621913658900059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077348573081275772600039 3116022859621913658900059)
        ·
          refine ⟨4674034289432870488350089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116022859621913658900059 4674034289432870488350089)
          ·
            refine ⟨3505525717074652866262567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674034289432870488350089 3505525717074652866262567)
            ·
              refine ⟨5258288575611979299393851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505525717074652866262567 5258288575611979299393851)
              ·
                refine ⟨7887432863417968949090777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258288575611979299393851 7887432863417968949090777)
                ·
                  refine ⟨5915574647563476711818083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7887432863417968949090777 5915574647563476711818083)
                  ·
                    refine ⟨8873361971345215067727125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5915574647563476711818083 8873361971345215067727125)
                    ·
                      refine ⟨415938842406806956299709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8873361971345215067727125 415938842406806956299709)
                      ·
                        rfl

theorem cell23_810038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_810038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810038 prefixEnd_810038 := by exact prefixLift 810038
  have htrace : WordTrace (prefixWord ++ tailWord_810038) baseStart_810038 baseEnd_810038 := by
    simpa [prefixWord, tailWord_810038, baseEnd_810038] using wordTrace_append hprefix tailTrace_810038
  have hstable : (prefixWord ++ tailWord_810038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810038).length < 2 ^ (prefixWord ++ tailWord_810038).sum := by decide
  have hdescent : baseEnd_810038 < baseStart_810038 := by decide
  rcases family_descends (prefixWord ++ tailWord_810038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810085 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_810085 : Nat := 118140960795 + 810085 * 2 ^ 59
def prefixEnd_810085 : Nat := 4983230072969 + 3 ^ 40 * 810085 * 2
def baseEnd_810085 : Nat := 415962975997568272411993

theorem tailTrace_810085 : CollatzResearch.WordTrace tailWord_810085 prefixEnd_810085 415962975997568272411993 := by
  unfold tailWord_810085
  simp only [CollatzResearch.WordTrace]
  refine ⟨29546227270207871348383709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19697484846805247565589139 29546227270207871348383709)
  ·
    refine ⟨11079835226327951755643891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29546227270207871348383709 11079835226327951755643891)
    ·
      refine ⟨16619752839491927633465837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11079835226327951755643891 16619752839491927633465837)
      ·
        refine ⟨6232407314809472862549689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16619752839491927633465837 6232407314809472862549689)
        ·
          refine ⟨4674305486107104646912267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6232407314809472862549689 4674305486107104646912267)
          ·
            refine ⟨7011458229160656970368401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674305486107104646912267 7011458229160656970368401)
            ·
              refine ⟨5258593671870492727776301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7011458229160656970368401 5258593671870492727776301)
              ·
                refine ⟨1971972626951434772916113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5258593671870492727776301 1971972626951434772916113)
                ·
                  refine ⟨1478979470213576079687085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971972626951434772916113 1478979470213576079687085)
                  ·
                    refine ⟨554617301330091029882657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478979470213576079687085 554617301330091029882657)
                    ·
                      refine ⟨415962975997568272411993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554617301330091029882657 415962975997568272411993)
                      ·
                        rfl

theorem cell23_810085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_810085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810085 prefixEnd_810085 := by exact prefixLift 810085
  have htrace : WordTrace (prefixWord ++ tailWord_810085) baseStart_810085 baseEnd_810085 := by
    simpa [prefixWord, tailWord_810085, baseEnd_810085] using wordTrace_append hprefix tailTrace_810085
  have hstable : (prefixWord ++ tailWord_810085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810085).length < 2 ^ (prefixWord ++ tailWord_810085).sum := by decide
  have hdescent : baseEnd_810085 < baseStart_810085 := by decide
  rcases family_descends (prefixWord ++ tailWord_810085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810102 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_810102 : Nat := 118140960795 + 810102 * 2 ^ 59
def prefixEnd_810102 : Nat := 4983230072969 + 3 ^ 40 * 810102 * 2
def baseEnd_810102 : Nat := 415971705168694705899415

theorem tailTrace_810102 : CollatzResearch.WordTrace tailWord_810102 prefixEnd_810102 415971705168694705899415 := by
  unfold tailWord_810102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846677956946642703234535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19697898207430855501168373 1846677956946642703234535)
  ·
    refine ⟨2770016935419964054851803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846677956946642703234535 2770016935419964054851803)
    ·
      refine ⟨4155025403129946082277705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770016935419964054851803 4155025403129946082277705)
      ·
        refine ⟨3116269052347459561708279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4155025403129946082277705 3116269052347459561708279)
        ·
          refine ⟨4674403578521189342562419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116269052347459561708279 4674403578521189342562419)
          ·
            refine ⟨7011605367781784013843629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674403578521189342562419 7011605367781784013843629)
            ·
              refine ⟨2629352012918169005191361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7011605367781784013843629 2629352012918169005191361)
              ·
                refine ⟨1972014009688626753893521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629352012918169005191361 1972014009688626753893521)
                ·
                  refine ⟨1479010507266470065420141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972014009688626753893521 1479010507266470065420141)
                  ·
                    refine ⟨554628940224926274532553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479010507266470065420141 554628940224926274532553)
                    ·
                      refine ⟨415971705168694705899415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554628940224926274532553 415971705168694705899415)
                      ·
                        rfl

theorem cell23_810102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_810102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810102 prefixEnd_810102 := by exact prefixLift 810102
  have htrace : WordTrace (prefixWord ++ tailWord_810102) baseStart_810102 baseEnd_810102 := by
    simpa [prefixWord, tailWord_810102, baseEnd_810102] using wordTrace_append hprefix tailTrace_810102
  have hstable : (prefixWord ++ tailWord_810102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810102).length < 2 ^ (prefixWord ++ tailWord_810102).sum := by decide
  have hdescent : baseEnd_810102 < baseStart_810102 := by decide
  rcases family_descends (prefixWord ++ tailWord_810102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810108 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_810108 : Nat := 118140960795 + 810108 * 2 ^ 59
def prefixEnd_810108 : Nat := 4983230072969 + 3 ^ 40 * 810108 * 2
def baseEnd_810108 : Nat := 138658262017540560808129

theorem tailTrace_810108 : CollatzResearch.WordTrace tailWord_810108 prefixEnd_810108 138658262017540560808129 := by
  unfold tailWord_810108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773533074562273138235489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19698044099416364184313985 14773533074562273138235489)
  ·
    refine ⟨11080149805921704853676617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14773533074562273138235489 11080149805921704853676617)
    ·
      refine ⟨8310112354441278640257463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11080149805921704853676617 8310112354441278640257463)
      ·
        refine ⟨12465168531661917960386195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310112354441278640257463 12465168531661917960386195)
        ·
          refine ⟨18697752797492876940579293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465168531661917960386195 18697752797492876940579293)
          ·
            refine ⟨7011657299059828852717235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18697752797492876940579293 7011657299059828852717235)
            ·
              refine ⟨10517485948589743279075853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011657299059828852717235 10517485948589743279075853)
              ·
                refine ⟨3944057230721153729653445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10517485948589743279075853 3944057230721153729653445)
                ·
                  refine ⟨739510730760216324310021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3944057230721153729653445 739510730760216324310021)
                  ·
                    refine ⟨138658262017540560808129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739510730760216324310021 138658262017540560808129)
                    ·
                      rfl

theorem cell23_810108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_810108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810108 prefixEnd_810108 := by exact prefixLift 810108
  have htrace : WordTrace (prefixWord ++ tailWord_810108) baseStart_810108 baseEnd_810108 := by
    simpa [prefixWord, tailWord_810108, baseEnd_810108] using wordTrace_append hprefix tailTrace_810108
  have hstable : (prefixWord ++ tailWord_810108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810108).length < 2 ^ (prefixWord ++ tailWord_810108).sum := by decide
  have hdescent : baseEnd_810108 < baseStart_810108 := by decide
  rcases family_descends (prefixWord ++ tailWord_810108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810109 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_810109 : Nat := 118140960795 + 810109 * 2 ^ 59
def prefixEnd_810109 : Nat := 4983230072969 + 3 ^ 40 * 810109 * 2
def baseEnd_810109 : Nat := 415975299533276178511883

theorem tailTrace_810109 : CollatzResearch.WordTrace tailWord_810109 prefixEnd_810109 415975299533276178511883 := by
  unfold tailWord_810109
  simp only [CollatzResearch.WordTrace]
  refine ⟨29547102622120923447257381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19698068414747282298171587 29547102622120923447257381)
  ·
    refine ⟨5540081741647673146360759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29547102622120923447257381 5540081741647673146360759)
    ·
      refine ⟨8310122612471509719541139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540081741647673146360759 8310122612471509719541139)
      ·
        refine ⟨12465183918707264579311709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310122612471509719541139 12465183918707264579311709)
        ·
          refine ⟨4674443969515224217241891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12465183918707264579311709 4674443969515224217241891)
          ·
            refine ⟨7011665954272836325862837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674443969515224217241891 7011665954272836325862837)
            ·
              refine ⟨657343683213078405549641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7011665954272836325862837 657343683213078405549641)
              ·
                refine ⟨493007762409808804162231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657343683213078405549641 493007762409808804162231)
                ·
                  refine ⟨739511643614713206243347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493007762409808804162231 739511643614713206243347)
                  ·
                    refine ⟨1109267465422069809365021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 739511643614713206243347 1109267465422069809365021)
                    ·
                      refine ⟨415975299533276178511883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1109267465422069809365021 415975299533276178511883)
                      ·
                        rfl

theorem cell23_810109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_810109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810109 prefixEnd_810109 := by exact prefixLift 810109
  have htrace : WordTrace (prefixWord ++ tailWord_810109) baseStart_810109 baseEnd_810109 := by
    simpa [prefixWord, tailWord_810109, baseEnd_810109] using wordTrace_append hprefix tailTrace_810109
  have hstable : (prefixWord ++ tailWord_810109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810109).length < 2 ^ (prefixWord ++ tailWord_810109).sum := by decide
  have hdescent : baseEnd_810109 < baseStart_810109 := by decide
  rcases family_descends (prefixWord ++ tailWord_810109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810121 : List Nat := [1, 2, 1, 1, 4, 3, 1, 10]
def baseStart_810121 : Nat := 118140960795 + 810121 * 2 ^ 59
def prefixEnd_810121 : Nat := 4983230072969 + 3 ^ 40 * 810121 * 2
def baseEnd_810121 : Nat := 15406720788930745613401

theorem tailTrace_810121 : CollatzResearch.WordTrace tailWord_810121 prefixEnd_810121 15406720788930745613401 := by
  unfold tailWord_810121
  simp only [CollatzResearch.WordTrace]
  refine ⟨29547540298077449496694217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19698360198718299664462811 29547540298077449496694217)
  ·
    refine ⟨22160655223558087122520663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29547540298077449496694217 22160655223558087122520663)
    ·
      refine ⟨33240982835337130683780995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22160655223558087122520663 33240982835337130683780995)
      ·
        refine ⟨49861474253005696025671493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33240982835337130683780995 49861474253005696025671493)
        ·
          refine ⟨9349026422438568004813405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49861474253005696025671493 9349026422438568004813405)
          ·
            refine ⟨3505884908414463001805027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9349026422438568004813405 3505884908414463001805027)
            ·
              refine ⟨5258827362621694502707541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505884908414463001805027 5258827362621694502707541)
              ·
                refine ⟨15406720788930745613401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5258827362621694502707541 15406720788930745613401)
                ·
                  rfl

theorem cell23_810121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 10].length) (baseStart_810121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810121 prefixEnd_810121 := by exact prefixLift 810121
  have htrace : WordTrace (prefixWord ++ tailWord_810121) baseStart_810121 baseEnd_810121 := by
    simpa [prefixWord, tailWord_810121, baseEnd_810121] using wordTrace_append hprefix tailTrace_810121
  have hstable : (prefixWord ++ tailWord_810121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810121).length < 2 ^ (prefixWord ++ tailWord_810121).sum := by decide
  have hdescent : baseEnd_810121 < baseStart_810121 := by decide
  rcases family_descends (prefixWord ++ tailWord_810121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810135 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_810135 : Nat := 118140960795 + 810135 * 2 ^ 59
def prefixEnd_810135 : Nat := 4983230072969 + 3 ^ 40 * 810135 * 2
def baseEnd_810135 : Nat := 415988650030293076786763

theorem tailTrace_810135 : CollatzResearch.WordTrace tailWord_810135 prefixEnd_810135 415988650030293076786763 := by
  unfold tailWord_810135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29548050920026729887703859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19698700613351153258469239 29548050920026729887703859)
  ·
    refine ⟨44322076380040094831555789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29548050920026729887703859 44322076380040094831555789)
    ·
      refine ⟨16620778642515035561833421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44322076380040094831555789 16620778642515035561833421)
      ·
        refine ⟨6232791990943138335687533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16620778642515035561833421 6232791990943138335687533)
        ·
          refine ⟨2337296996603676875882825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6232791990943138335687533 2337296996603676875882825)
          ·
            refine ⟨1752972747452757656912119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337296996603676875882825 1752972747452757656912119)
            ·
              refine ⟨2629459121179136485368179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752972747452757656912119 2629459121179136485368179)
              ·
                refine ⟨3944188681768704728052269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629459121179136485368179 3944188681768704728052269)
                ·
                  refine ⟨1479070755663264273019601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3944188681768704728052269 1479070755663264273019601)
                  ·
                    refine ⟨1109303066747448204764701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479070755663264273019601 1109303066747448204764701)
                    ·
                      refine ⟨415988650030293076786763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1109303066747448204764701 415988650030293076786763)
                      ·
                        rfl

theorem cell23_810135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_810135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810135 prefixEnd_810135 := by exact prefixLift 810135
  have htrace : WordTrace (prefixWord ++ tailWord_810135) baseStart_810135 baseEnd_810135 := by
    simpa [prefixWord, tailWord_810135, baseEnd_810135] using wordTrace_append hprefix tailTrace_810135
  have hstable : (prefixWord ++ tailWord_810135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810135).length < 2 ^ (prefixWord ++ tailWord_810135).sum := by decide
  have hdescent : baseEnd_810135 < baseStart_810135 := by decide
  rcases family_descends (prefixWord ++ tailWord_810135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810138 : List Nat := [3, 1, 1, 5, 1, 1, 2, 9]
def baseStart_810138 : Nat := 118140960795 + 810138 * 2 ^ 59
def prefixEnd_810138 : Nat := 4983230072969 + 3 ^ 40 * 810138 * 2
def baseEnd_810138 : Nat := 15407044091565057964787

theorem tailTrace_810138 : CollatzResearch.WordTrace tailWord_810138 prefixEnd_810138 15407044091565057964787 := by
  unfold tailWord_810138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387040084753965350015767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19698773559343907600042045 7387040084753965350015767)
  ·
    refine ⟨11080560127130948025023651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7387040084753965350015767 11080560127130948025023651)
    ·
      refine ⟨16620840190696422037535477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11080560127130948025023651 16620840190696422037535477)
      ·
        refine ⟨1558203767877789566018951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16620840190696422037535477 1558203767877789566018951)
        ·
          refine ⟨2337305651816684349028427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558203767877789566018951 2337305651816684349028427)
          ·
            refine ⟨3505958477725026523542641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337305651816684349028427 3505958477725026523542641)
            ·
              refine ⟨2629468858293769892656981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505958477725026523542641 2629468858293769892656981)
              ·
                refine ⟨15407044091565057964787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2629468858293769892656981 15407044091565057964787)
                ·
                  rfl

theorem cell23_810138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_810138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810138 prefixEnd_810138 := by exact prefixLift 810138
  have htrace : WordTrace (prefixWord ++ tailWord_810138) baseStart_810138 baseEnd_810138 := by
    simpa [prefixWord, tailWord_810138, baseEnd_810138] using wordTrace_append hprefix tailTrace_810138
  have hstable : (prefixWord ++ tailWord_810138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810138).length < 2 ^ (prefixWord ++ tailWord_810138).sum := by decide
  have hdescent : baseEnd_810138 < baseStart_810138 := by decide
  rcases family_descends (prefixWord ++ tailWord_810138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810175 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 3, 3, 2]
def baseStart_810175 : Nat := 118140960795 + 810175 * 2 ^ 59
def prefixEnd_810175 : Nat := 4983230072969 + 3 ^ 40 * 810175 * 2
def baseEnd_810175 : Nat := 416009189256472920286579

theorem tailTrace_810175 : CollatzResearch.WordTrace tailWord_810175 prefixEnd_810175 416009189256472920286579 := by
  unfold tailWord_810175
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549509839881816719159979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19699673226587877812773319 29549509839881816719159979)
  ·
    refine ⟨44324264759822725078739969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29549509839881816719159979 44324264759822725078739969)
    ·
      refine ⟨33243198569867043809054977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44324264759822725078739969 33243198569867043809054977)
      ·
        refine ⟨24932398927400282856791233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33243198569867043809054977 24932398927400282856791233)
        ·
          refine ⟨18699299195550212142593425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24932398927400282856791233 18699299195550212142593425)
          ·
            refine ⟨14024474396662659106945069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18699299195550212142593425 14024474396662659106945069)
            ·
              refine ⟨5259177898748497165104401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14024474396662659106945069 5259177898748497165104401)
              ·
                refine ⟨3944383424061372873828301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5259177898748497165104401 3944383424061372873828301)
                ·
                  refine ⟨1479143784023014827685613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3944383424061372873828301 1479143784023014827685613)
                  ·
                    refine ⟨554678919008630560382105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479143784023014827685613 554678919008630560382105)
                    ·
                      refine ⟨416009189256472920286579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554678919008630560382105 416009189256472920286579)
                      ·
                        rfl

theorem cell23_810175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_810175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810175 prefixEnd_810175 := by exact prefixLift 810175
  have htrace : WordTrace (prefixWord ++ tailWord_810175) baseStart_810175 baseEnd_810175 := by
    simpa [prefixWord, tailWord_810175, baseEnd_810175] using wordTrace_append hprefix tailTrace_810175
  have hstable : (prefixWord ++ tailWord_810175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810175).length < 2 ^ (prefixWord ++ tailWord_810175).sum := by decide
  have hdescent : baseEnd_810175 < baseStart_810175 := by decide
  rcases family_descends (prefixWord ++ tailWord_810175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810189 : List Nat := [1, 6, 2, 2, 1, 1, 3, 7]
def baseStart_810189 : Nat := 118140960795 + 810189 * 2 ^ 59
def prefixEnd_810189 : Nat := 4983230072969 + 3 ^ 40 * 810189 * 2
def baseEnd_810189 : Nat := 15408013999467995018945

theorem tailTrace_810189 : CollatzResearch.WordTrace tailWord_810189 prefixEnd_810189 15408013999467995018945 := by
  unfold tailWord_810189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550020461831097110169621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700013641220731406779747 29550020461831097110169621)
  ·
    refine ⟨1385157209148332677039201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29550020461831097110169621 1385157209148332677039201)
    ·
      refine ⟨1038867906861249507779401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385157209148332677039201 1038867906861249507779401)
      ·
        refine ⟨779150930145937130834551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038867906861249507779401 779150930145937130834551)
        ·
          refine ⟨1168726395218905696251827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779150930145937130834551 1168726395218905696251827)
          ·
            refine ⟨1753089592828358544377741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168726395218905696251827 1753089592828358544377741)
            ·
              refine ⟨657408597310634454141653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753089592828358544377741 657408597310634454141653)
              ·
                refine ⟨15408013999467995018945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 657408597310634454141653 15408013999467995018945)
                ·
                  rfl

theorem cell23_810189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 7].length) (baseStart_810189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810189 prefixEnd_810189 := by exact prefixLift 810189
  have htrace : WordTrace (prefixWord ++ tailWord_810189) baseStart_810189 baseEnd_810189 := by
    simpa [prefixWord, tailWord_810189, baseEnd_810189] using wordTrace_append hprefix tailTrace_810189
  have hstable : (prefixWord ++ tailWord_810189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810189).length < 2 ^ (prefixWord ++ tailWord_810189).sum := by decide
  have hdescent : baseEnd_810189 < baseStart_810189 := by decide
  rcases family_descends (prefixWord ++ tailWord_810189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810209 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_810209 : Nat := 118140960795 + 810209 * 2 ^ 59
def prefixEnd_810209 : Nat := 4983230072969 + 3 ^ 40 * 810209 * 2
def baseEnd_810209 : Nat := 416026647598725787261423

theorem tailTrace_810209 : CollatzResearch.WordTrace tailWord_810209 prefixEnd_810209 416026647598725787261423 := by
  unfold tailWord_810209
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550749921758640525897681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700499947839093683931787 29550749921758640525897681)
  ·
    refine ⟨22163062441318980394423261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29550749921758640525897681 22163062441318980394423261)
    ·
      refine ⟨8311148415494617647908723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22163062441318980394423261 8311148415494617647908723)
      ·
        refine ⟨12466722623241926471863085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311148415494617647908723 12466722623241926471863085)
        ·
          refine ⟨4675020983715722426948657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12466722623241926471863085 4675020983715722426948657)
          ·
            refine ⟨3506265737786791820211493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4675020983715722426948657 3506265737786791820211493)
            ·
              refine ⟨657424825835023466289655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3506265737786791820211493 657424825835023466289655)
              ·
                refine ⟨986137238752535199434483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657424825835023466289655 986137238752535199434483)
                ·
                  refine ⟨1479205858128802799151725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986137238752535199434483 1479205858128802799151725)
                  ·
                    refine ⟨554702196798301049681897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479205858128802799151725 554702196798301049681897)
                    ·
                      refine ⟨416026647598725787261423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554702196798301049681897 416026647598725787261423)
                      ·
                        rfl

theorem cell23_810209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_810209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810209 prefixEnd_810209 := by exact prefixLift 810209
  have htrace : WordTrace (prefixWord ++ tailWord_810209) baseStart_810209 baseEnd_810209 := by
    simpa [prefixWord, tailWord_810209, baseEnd_810209] using wordTrace_append hprefix tailTrace_810209
  have hstable : (prefixWord ++ tailWord_810209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810209).length < 2 ^ (prefixWord ++ tailWord_810209).sum := by decide
  have hdescent : baseEnd_810209 < baseStart_810209 := by decide
  rcases family_descends (prefixWord ++ tailWord_810209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810275 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 2, 5]
def baseStart_810275 : Nat := 118140960795 + 810275 * 2 ^ 59
def prefixEnd_810275 : Nat := 4983230072969 + 3 ^ 40 * 810275 * 2
def baseEnd_810275 : Nat := 138686845773974176345373

theorem tailTrace_810275 : CollatzResearch.WordTrace tailWord_810275 prefixEnd_810275 138686845773974176345373 := by
  unfold tailWord_810275
  simp only [CollatzResearch.WordTrace]
  refine ⟨29553157139519533797800279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19702104759679689198533519 29553157139519533797800279)
  ·
    refine ⟨44329735709279300696700419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29553157139519533797800279 44329735709279300696700419)
    ·
      refine ⟨66494603563918951045050629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44329735709279300696700419 66494603563918951045050629)
      ·
        refine ⟨12467738168234803320946993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66494603563918951045050629 12467738168234803320946993)
        ·
          refine ⟨9350803626176102490710245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12467738168234803320946993 9350803626176102490710245)
          ·
            refine ⟨1753275679908019217008171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9350803626176102490710245 1753275679908019217008171)
            ·
              refine ⟨2629913519862028825512257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753275679908019217008171 2629913519862028825512257)
              ·
                refine ⟨1972435139896521619134193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629913519862028825512257 1972435139896521619134193)
                ·
                  refine ⟨1479326354922391214350645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972435139896521619134193 1479326354922391214350645)
                  ·
                    refine ⟨138686845773974176345373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1479326354922391214350645 138686845773974176345373)
                    ·
                      rfl

theorem cell23_810275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 5].length) (baseStart_810275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810275 prefixEnd_810275 := by exact prefixLift 810275
  have htrace : WordTrace (prefixWord ++ tailWord_810275) baseStart_810275 baseEnd_810275 := by
    simpa [prefixWord, tailWord_810275, baseEnd_810275] using wordTrace_append hprefix tailTrace_810275
  have hstable : (prefixWord ++ tailWord_810275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810275).length < 2 ^ (prefixWord ++ tailWord_810275).sum := by decide
  have hdescent : baseEnd_810275 < baseStart_810275 := by decide
  rcases family_descends (prefixWord ++ tailWord_810275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810339 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 1, 4]
def baseStart_810339 : Nat := 118140960795 + 810339 * 2 ^ 59
def prefixEnd_810339 : Nat := 4983230072969 + 3 ^ 40 * 810339 * 2
def baseEnd_810339 : Nat := 138697800027936759545275

theorem tailTrace_810339 : CollatzResearch.WordTrace tailWord_810339 prefixEnd_810339 138697800027936759545275 := by
  unfold tailWord_810339
  simp only [CollatzResearch.WordTrace]
  refine ⟨29555491411287672728130071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19703660940858448485420047 29555491411287672728130071)
  ·
    refine ⟨44333237116931509092195107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29555491411287672728130071 44333237116931509092195107)
    ·
      refine ⟨66499855675397263638292661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44333237116931509092195107 66499855675397263638292661)
      ·
        refine ⟨6234361469568493466089937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66499855675397263638292661 6234361469568493466089937)
        ·
          refine ⟨4675771102176370099567453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6234361469568493466089937 4675771102176370099567453)
          ·
            refine ⟨1753414163316138787337795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4675771102176370099567453 1753414163316138787337795)
            ·
              refine ⟨2630121244974208181006693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753414163316138787337795 2630121244974208181006693)
              ·
                refine ⟨493147733432664033938755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2630121244974208181006693 493147733432664033938755)
                ·
                  refine ⟨739721600148996050908133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493147733432664033938755 739721600148996050908133)
                  ·
                    refine ⟨138697800027936759545275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739721600148996050908133 138697800027936759545275)
                    ·
                      rfl

theorem cell23_810339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 1, 4].length) (baseStart_810339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810339 prefixEnd_810339 := by exact prefixLift 810339
  have htrace : WordTrace (prefixWord ++ tailWord_810339) baseStart_810339 baseEnd_810339 := by
    simpa [prefixWord, tailWord_810339, baseEnd_810339] using wordTrace_append hprefix tailTrace_810339
  have hstable : (prefixWord ++ tailWord_810339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810339).length < 2 ^ (prefixWord ++ tailWord_810339).sum := by decide
  have hdescent : baseEnd_810339 < baseStart_810339 := by decide
  rcases family_descends (prefixWord ++ tailWord_810339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810362 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_810362 : Nat := 118140960795 + 810362 * 2 ^ 59
def prefixEnd_810362 : Nat := 4983230072969 + 3 ^ 40 * 810362 * 2
def baseEnd_810362 : Nat := 416105210138863688648219

theorem tailTrace_810362 : CollatzResearch.WordTrace tailWord_810362 prefixEnd_810362 416105210138863688648219 := by
  unfold tailWord_810362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389082572551086914054335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19704220193469565104144893 7389082572551086914054335)
  ·
    refine ⟨11083623858826630371081503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7389082572551086914054335 11083623858826630371081503)
    ·
      refine ⟨16625435788239945556622255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11083623858826630371081503 16625435788239945556622255)
      ·
        refine ⟨24938153682359918334933383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16625435788239945556622255 24938153682359918334933383)
        ·
          refine ⟨37407230523539877502400075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24938153682359918334933383 37407230523539877502400075)
          ·
            refine ⟨56110845785309816253600113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37407230523539877502400075 56110845785309816253600113)
            ·
              refine ⟨42083134338982362190200085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56110845785309816253600113 42083134338982362190200085)
              ·
                refine ⟨1972646922139798227665629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42083134338982362190200085 1972646922139798227665629)
                ·
                  refine ⟨739742595802424335374611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1972646922139798227665629 739742595802424335374611)
                  ·
                    refine ⟨1109613893703636503061917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 739742595802424335374611 1109613893703636503061917)
                    ·
                      refine ⟨416105210138863688648219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1109613893703636503061917 416105210138863688648219)
                      ·
                        rfl

theorem cell23_810362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_810362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810362 prefixEnd_810362 := by exact prefixLift 810362
  have htrace : WordTrace (prefixWord ++ tailWord_810362) baseStart_810362 baseEnd_810362 := by
    simpa [prefixWord, tailWord_810362, baseEnd_810362] using wordTrace_append hprefix tailTrace_810362
  have hstable : (prefixWord ++ tailWord_810362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810362).length < 2 ^ (prefixWord ++ tailWord_810362).sum := by decide
  have hdescent : baseEnd_810362 < baseStart_810362 := by decide
  rcases family_descends (prefixWord ++ tailWord_810362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810365 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_810365 : Nat := 118140960795 + 810365 * 2 ^ 59
def prefixEnd_810365 : Nat := 4983230072969 + 3 ^ 40 * 810365 * 2
def baseEnd_810365 : Nat := 138702250193609058970235

theorem tailTrace_810365 : CollatzResearch.WordTrace tailWord_810365 prefixEnd_810365 138702250193609058970235 := by
  unfold tailWord_810365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29556439709193479168576549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19704293139462319445717699 29556439709193479168576549)
  ·
    refine ⟨5541832445473777344108103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29556439709193479168576549 5541832445473777344108103)
    ·
      refine ⟨8312748668210666016162155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541832445473777344108103 8312748668210666016162155)
      ·
        refine ⟨12469123002315999024243233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312748668210666016162155 12469123002315999024243233)
        ·
          refine ⟨9351842251736999268182425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12469123002315999024243233 9351842251736999268182425)
          ·
            refine ⟨7013881688802749451136819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351842251736999268182425 7013881688802749451136819)
            ·
              refine ⟨10520822533204124176705229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013881688802749451136819 10520822533204124176705229)
              ·
                refine ⟨3945308449951546566264461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10520822533204124176705229 3945308449951546566264461)
                ·
                  refine ⟨1479490668731829962349173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3945308449951546566264461 1479490668731829962349173)
                  ·
                    refine ⟨138702250193609058970235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1479490668731829962349173 138702250193609058970235)
                    ·
                      rfl

theorem cell23_810365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_810365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810365 prefixEnd_810365 := by exact prefixLift 810365
  have htrace : WordTrace (prefixWord ++ tailWord_810365) baseStart_810365 baseEnd_810365 := by
    simpa [prefixWord, tailWord_810365, baseEnd_810365] using wordTrace_append hprefix tailTrace_810365
  have hstable : (prefixWord ++ tailWord_810365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810365).length < 2 ^ (prefixWord ++ tailWord_810365).sum := by decide
  have hdescent : baseEnd_810365 < baseStart_810365 := by decide
  rcases family_descends (prefixWord ++ tailWord_810365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810366 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_810366 : Nat := 118140960795 + 810366 * 2 ^ 59
def prefixEnd_810366 : Nat := 4983230072969 + 3 ^ 40 * 810366 * 2
def baseEnd_810366 : Nat := 416107264061481672998201

theorem tailTrace_810366 : CollatzResearch.WordTrace tailWord_810366 prefixEnd_810366 416107264061481672998201 := by
  unfold tailWord_810366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694559522773732042420369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19704317454793237559575301 3694559522773732042420369)
  ·
    refine ⟨2770919642080299031815277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3694559522773732042420369 2770919642080299031815277)
    ·
      refine ⟨1039094865780112136930729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2770919642080299031815277 1039094865780112136930729)
      ·
        refine ⟨779321149335084102698047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1039094865780112136930729 779321149335084102698047)
        ·
          refine ⟨1168981724002626154047071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779321149335084102698047 1168981724002626154047071)
          ·
            refine ⟨1753472586003939231070607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168981724002626154047071 1753472586003939231070607)
            ·
              refine ⟨2630208879005908846605911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753472586003939231070607 2630208879005908846605911)
              ·
                refine ⟨3945313318508863269908867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630208879005908846605911 3945313318508863269908867)
                ·
                  refine ⟨5917969977763294904863301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945313318508863269908867 5917969977763294904863301)
                  ·
                    refine ⟨1109619370830617794661869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5917969977763294904863301 1109619370830617794661869)
                    ·
                      refine ⟨416107264061481672998201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1109619370830617794661869 416107264061481672998201)
                      ·
                        rfl

theorem cell23_810366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_810366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810366 prefixEnd_810366 := by exact prefixLift 810366
  have htrace : WordTrace (prefixWord ++ tailWord_810366) baseStart_810366 baseEnd_810366 := by
    simpa [prefixWord, tailWord_810366, baseEnd_810366] using wordTrace_append hprefix tailTrace_810366
  have hstable : (prefixWord ++ tailWord_810366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810366).length < 2 ^ (prefixWord ++ tailWord_810366).sum := by decide
  have hdescent : baseEnd_810366 < baseStart_810366 := by decide
  rcases family_descends (prefixWord ++ tailWord_810366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810386 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_810386 : Nat := 118140960795 + 810386 * 2 ^ 59
def prefixEnd_810386 : Nat := 4983230072969 + 3 ^ 40 * 810386 * 2
def baseEnd_810386 : Nat := 46235281519396843860901

theorem tailTrace_810386 : CollatzResearch.WordTrace tailWord_810386 prefixEnd_810386 46235281519396843860901 := by
  unfold tailWord_810386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389301410529349938772753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19704803761411599836727341 7389301410529349938772753)
  ·
    refine ⟨5541976057897012454079565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7389301410529349938772753 5541976057897012454079565)
    ·
      refine ⟨2078241021711379670279837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5541976057897012454079565 2078241021711379670279837)
      ·
        refine ⟨779340383141767376354939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2078241021711379670279837 779340383141767376354939)
        ·
          refine ⟨1169010574712651064532409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779340383141767376354939 1169010574712651064532409)
          ·
            refine ⟨876757931034488298399307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169010574712651064532409 876757931034488298399307)
            ·
              refine ⟨1315136896551732447598961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876757931034488298399307 1315136896551732447598961)
              ·
                refine ⟨986352672413799335699221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315136896551732447598961 986352672413799335699221)
                ·
                  refine ⟨46235281519396843860901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 986352672413799335699221 46235281519396843860901)
                  ·
                    rfl

theorem cell23_810386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_810386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810386 prefixEnd_810386 := by exact prefixLift 810386
  have htrace : WordTrace (prefixWord ++ tailWord_810386) baseStart_810386 baseEnd_810386 := by
    simpa [prefixWord, tailWord_810386, baseEnd_810386] using wordTrace_append hprefix tailTrace_810386
  have hstable : (prefixWord ++ tailWord_810386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810386).length < 2 ^ (prefixWord ++ tailWord_810386).sum := by decide
  have hdescent : baseEnd_810386 < baseStart_810386 := by decide
  rcases family_descends (prefixWord ++ tailWord_810386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810395 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 10, 4]
def baseStart_810395 : Nat := 118140960795 + 810395 * 2 ^ 59
def prefixEnd_810395 : Nat := 4983230072969 + 3 ^ 40 * 810395 * 2
def baseEnd_810395 : Nat := 138707385000154019845189

theorem tailTrace_810395 : CollatzResearch.WordTrace tailWord_810395 prefixEnd_810395 138707385000154019845189 := by
  unfold tailWord_810395
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557533899084794292168639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19705022599389862861445759 29557533899084794292168639)
  ·
    refine ⟨44336300848627191438252959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29557533899084794292168639 44336300848627191438252959)
    ·
      refine ⟨66504451272940787157379439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44336300848627191438252959 66504451272940787157379439)
      ·
        refine ⟨99756676909411180736069159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66504451272940787157379439 99756676909411180736069159)
        ·
          refine ⟨149635015364116771104103739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99756676909411180736069159 149635015364116771104103739)
          ·
            refine ⟨224452523046175156656155609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149635015364116771104103739 224452523046175156656155609)
            ·
              refine ⟨168339392284631367492116707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224452523046175156656155609 168339392284631367492116707)
              ·
                refine ⟨252509088426947051238175061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168339392284631367492116707 252509088426947051238175061)
                ·
                  refine ⟨739772720000821439174341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 252509088426947051238175061 739772720000821439174341)
                  ·
                    refine ⟨138707385000154019845189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739772720000821439174341 138707385000154019845189)
                    ·
                      rfl

theorem cell23_810395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 4].length) (baseStart_810395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810395 prefixEnd_810395 := by exact prefixLift 810395
  have htrace : WordTrace (prefixWord ++ tailWord_810395) baseStart_810395 baseEnd_810395 := by
    simpa [prefixWord, tailWord_810395, baseEnd_810395] using wordTrace_append hprefix tailTrace_810395
  have hstable : (prefixWord ++ tailWord_810395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810395).length < 2 ^ (prefixWord ++ tailWord_810395).sum := by decide
  have hdescent : baseEnd_810395 < baseStart_810395 := by decide
  rcases family_descends (prefixWord ++ tailWord_810395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810405 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_810405 : Nat := 118140960795 + 810405 * 2 ^ 59
def prefixEnd_810405 : Nat := 4983230072969 + 3 ^ 40 * 810405 * 2
def baseEnd_810405 : Nat := 416127289807007020410521

theorem tailTrace_810405 : CollatzResearch.WordTrace tailWord_810405 prefixEnd_810405 416127289807007020410521 := by
  unfold tailWord_810405
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557898629048566000032669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19705265752699044000021779 29557898629048566000032669)
  ·
    refine ⟨11084211985893212250012251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29557898629048566000032669 11084211985893212250012251)
    ·
      refine ⟨16626317978839818375018377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11084211985893212250012251 16626317978839818375018377)
      ·
        refine ⟨12469738484129863781263783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16626317978839818375018377 12469738484129863781263783)
        ·
          refine ⟨18704607726194795671895675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469738484129863781263783 18704607726194795671895675)
          ·
            refine ⟨28056911589292193507843513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18704607726194795671895675 28056911589292193507843513)
            ·
              refine ⟨21042683691969145130882635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28056911589292193507843513 21042683691969145130882635)
              ·
                refine ⟨31564025537953717696323953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21042683691969145130882635 31564025537953717696323953)
                ·
                  refine ⟨23673019153465288272242965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31564025537953717696323953 23673019153465288272242965)
                  ·
                    refine ⟨1109672772818685387761389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23673019153465288272242965 1109672772818685387761389)
                    ·
                      refine ⟨416127289807007020410521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1109672772818685387761389 416127289807007020410521)
                      ·
                        rfl

theorem cell23_810405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_810405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810405 prefixEnd_810405 := by exact prefixLift 810405
  have htrace : WordTrace (prefixWord ++ tailWord_810405) baseStart_810405 baseEnd_810405 := by
    simpa [prefixWord, tailWord_810405, baseEnd_810405] using wordTrace_append hprefix tailTrace_810405
  have hstable : (prefixWord ++ tailWord_810405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810405).length < 2 ^ (prefixWord ++ tailWord_810405).sum := by decide
  have hdescent : baseEnd_810405 < baseStart_810405 := by decide
  rcases family_descends (prefixWord ++ tailWord_810405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810412 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_810412 : Nat := 118140960795 + 810412 * 2 ^ 59
def prefixEnd_810412 : Nat := 4983230072969 + 3 ^ 40 * 810412 * 2
def baseEnd_810412 : Nat := 138710294723862831007663

theorem tailTrace_810412 : CollatzResearch.WordTrace tailWord_810412 prefixEnd_810412 138710294723862831007663 := by
  unfold tailWord_810412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779076970011603097768745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19705435960015470797024993 14779076970011603097768745)
  ·
    refine ⟨11084307727508702323326559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14779076970011603097768745 11084307727508702323326559)
    ·
      refine ⟨16626461591263053484989839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11084307727508702323326559 16626461591263053484989839)
      ·
        refine ⟨24939692386894580227484759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16626461591263053484989839 24939692386894580227484759)
        ·
          refine ⟨37409538580341870341227139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24939692386894580227484759 37409538580341870341227139)
          ·
            refine ⟨56114307870512805511840709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37409538580341870341227139 56114307870512805511840709)
            ·
              refine ⟨10521432725721151033470133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56114307870512805511840709 10521432725721151033470133)
              ·
                refine ⟨986384318036357909387825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10521432725721151033470133 986384318036357909387825)
                ·
                  refine ⟨739788238527268432040869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 986384318036357909387825 739788238527268432040869)
                  ·
                    refine ⟨138710294723862831007663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 739788238527268432040869 138710294723862831007663)
                    ·
                      rfl

theorem cell23_810412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_810412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810412 prefixEnd_810412 := by exact prefixLift 810412
  have htrace : WordTrace (prefixWord ++ tailWord_810412) baseStart_810412 baseEnd_810412 := by
    simpa [prefixWord, tailWord_810412, baseEnd_810412] using wordTrace_append hprefix tailTrace_810412
  have hstable : (prefixWord ++ tailWord_810412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810412).length < 2 ^ (prefixWord ++ tailWord_810412).sum := by decide
  have hdescent : baseEnd_810412 < baseStart_810412 := by decide
  rcases family_descends (prefixWord ++ tailWord_810412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810475 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_810475 : Nat := 118140960795 + 810475 * 2 ^ 59
def prefixEnd_810475 : Nat := 4983230072969 + 3 ^ 40 * 810475 * 2
def baseEnd_810475 : Nat := 416163233452821746535199

theorem tailTrace_810475 : CollatzResearch.WordTrace tailWord_810475 prefixEnd_810475 416163233452821746535199 := by
  unfold tailWord_810475
  simp only [CollatzResearch.WordTrace]
  refine ⟨29560451738794967955080879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19706967825863311970053919 29560451738794967955080879)
  ·
    refine ⟨44340677608192451932621319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29560451738794967955080879 44340677608192451932621319)
    ·
      refine ⟨66511016412288677898931979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44340677608192451932621319 66511016412288677898931979)
      ·
        refine ⟨99766524618433016848397969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66511016412288677898931979 99766524618433016848397969)
        ·
          refine ⟨74824893463824762636298477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99766524618433016848397969 74824893463824762636298477)
          ·
            refine ⟨28059335048934285988611929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74824893463824762636298477 28059335048934285988611929)
            ·
              refine ⟨21044501286700714491458947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28059335048934285988611929 21044501286700714491458947)
              ·
                refine ⟨31566751930051071737188421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21044501286700714491458947 31566751930051071737188421)
                ·
                  refine ⟨5918765986884575950722829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31566751930051071737188421 5918765986884575950722829)
                  ·
                    refine ⟨2219537245081715981521061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5918765986884575950722829 2219537245081715981521061)
                    ·
                      refine ⟨416163233452821746535199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2219537245081715981521061 416163233452821746535199)
                      ·
                        rfl

theorem cell23_810475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_810475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810475 prefixEnd_810475 := by exact prefixLift 810475
  have htrace : WordTrace (prefixWord ++ tailWord_810475) baseStart_810475 baseEnd_810475 := by
    simpa [prefixWord, tailWord_810475, baseEnd_810475] using wordTrace_append hprefix tailTrace_810475
  have hstable : (prefixWord ++ tailWord_810475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810475).length < 2 ^ (prefixWord ++ tailWord_810475).sum := by decide
  have hdescent : baseEnd_810475 < baseStart_810475 := by decide
  rcases family_descends (prefixWord ++ tailWord_810475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810495 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_810495 : Nat := 118140960795 + 810495 * 2 ^ 59
def prefixEnd_810495 : Nat := 4983230072969 + 3 ^ 40 * 810495 * 2
def baseEnd_810495 : Nat := 416173503065911668285107

theorem tailTrace_810495 : CollatzResearch.WordTrace tailWord_810495 prefixEnd_810495 416173503065911668285107 := by
  unfold tailWord_810495
  simp only [CollatzResearch.WordTrace]
  refine ⟨29561181198722511370808939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19707454132481674247205959 29561181198722511370808939)
  ·
    refine ⟨44341771798083767056213409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29561181198722511370808939 44341771798083767056213409)
    ·
      refine ⟨33256328848562825292160057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44341771798083767056213409 33256328848562825292160057)
      ·
        refine ⟨24942246636422118969120043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33256328848562825292160057 24942246636422118969120043)
        ·
          refine ⟨37413369954633178453680065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24942246636422118969120043 37413369954633178453680065)
          ·
            refine ⟨28060027465974883840260049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37413369954633178453680065 28060027465974883840260049)
            ·
              refine ⟨21045020599481162880195037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28060027465974883840260049 21045020599481162880195037)
              ·
                refine ⟨7891882724805436080073139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21045020599481162880195037 7891882724805436080073139)
                ·
                  refine ⟨11837824087208154120109709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891882724805436080073139 11837824087208154120109709)
                  ·
                    refine ⟨4439184032703057795041141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11837824087208154120109709 4439184032703057795041141)
                    ·
                      refine ⟨416173503065911668285107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4439184032703057795041141 416173503065911668285107)
                      ·
                        rfl

theorem cell23_810495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_810495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810495 prefixEnd_810495 := by exact prefixLift 810495
  have htrace : WordTrace (prefixWord ++ tailWord_810495) baseStart_810495 baseEnd_810495 := by
    simpa [prefixWord, tailWord_810495, baseEnd_810495] using wordTrace_append hprefix tailTrace_810495
  have hstable : (prefixWord ++ tailWord_810495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810495).length < 2 ^ (prefixWord ++ tailWord_810495).sum := by decide
  have hdescent : baseEnd_810495 < baseStart_810495 := by decide
  rcases family_descends (prefixWord ++ tailWord_810495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810549 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 5]
def baseStart_810549 : Nat := 118140960795 + 810549 * 2 ^ 59
def prefixEnd_810549 : Nat := 4983230072969 + 3 ^ 40 * 810549 * 2
def baseEnd_810549 : Nat := 46244581224583828556651

theorem tailTrace_810549 : CollatzResearch.WordTrace tailWord_810549 prefixEnd_810549 46244581224583828556651 := by
  unfold tailWord_810549
  simp only [CollatzResearch.WordTrace]
  refine ⟨29563150740526878593274701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19708767160351252395516467 29563150740526878593274701)
  ·
    refine ⟨11086181527697579472478013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29563150740526878593274701 11086181527697579472478013)
    ·
      refine ⟨4157318072886592302179255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11086181527697579472478013 4157318072886592302179255)
      ·
        refine ⟨6235977109329888453268883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157318072886592302179255 6235977109329888453268883)
        ·
          refine ⟨9353965663994832679903325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235977109329888453268883 9353965663994832679903325)
          ·
            refine ⟨3507737123998062254963747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9353965663994832679903325 3507737123998062254963747)
            ·
              refine ⟨5261605685997093382445621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507737123998062254963747 5261605685997093382445621)
              ·
                refine ⟨493275533062227504604277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5261605685997093382445621 493275533062227504604277)
                ·
                  refine ⟨46244581224583828556651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493275533062227504604277 46244581224583828556651)
                  ·
                    rfl

theorem cell23_810549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_810549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810549 prefixEnd_810549 := by exact prefixLift 810549
  have htrace : WordTrace (prefixWord ++ tailWord_810549) baseStart_810549 baseEnd_810549 := by
    simpa [prefixWord, tailWord_810549, baseEnd_810549] using wordTrace_append hprefix tailTrace_810549
  have hstable : (prefixWord ++ tailWord_810549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810549).length < 2 ^ (prefixWord ++ tailWord_810549).sum := by decide
  have hdescent : baseEnd_810549 < baseStart_810549 := by decide
  rcases family_descends (prefixWord ++ tailWord_810549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810599 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_810599 : Nat := 118140960795 + 810599 * 2 ^ 59
def prefixEnd_810599 : Nat := 4983230072969 + 3 ^ 40 * 810599 * 2
def baseEnd_810599 : Nat := 416226905053979261384629

theorem tailTrace_810599 : CollatzResearch.WordTrace tailWord_810599 prefixEnd_810599 416226905053979261384629 := by
  unfold tailWord_810599
  simp only [CollatzResearch.WordTrace]
  refine ⟨29564974390345737132594851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19709982926897158088396567 29564974390345737132594851)
  ·
    refine ⟨44347461585518605698892277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29564974390345737132594851 44347461585518605698892277)
    ·
      refine ⟨4157574523642369284271151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44347461585518605698892277 4157574523642369284271151)
      ·
        refine ⟨6236361785463553926406727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157574523642369284271151 6236361785463553926406727)
        ·
          refine ⟨9354542678195330889610091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236361785463553926406727 9354542678195330889610091)
          ·
            refine ⟨14031814017292996334415137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354542678195330889610091 14031814017292996334415137)
            ·
              refine ⟨10523860512969747250811353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14031814017292996334415137 10523860512969747250811353)
              ·
                refine ⟨7892895384727310438108515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10523860512969747250811353 7892895384727310438108515)
                ·
                  refine ⟨11839343077090965657162773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7892895384727310438108515 11839343077090965657162773)
                  ·
                    refine ⟨554969206738639015179505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11839343077090965657162773 554969206738639015179505)
                    ·
                      refine ⟨416226905053979261384629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 554969206738639015179505 416226905053979261384629)
                      ·
                        rfl

theorem cell23_810599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_810599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810599 prefixEnd_810599 := by exact prefixLift 810599
  have htrace : WordTrace (prefixWord ++ tailWord_810599) baseStart_810599 baseEnd_810599 := by
    simpa [prefixWord, tailWord_810599, baseEnd_810599] using wordTrace_append hprefix tailTrace_810599
  have hstable : (prefixWord ++ tailWord_810599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810599).length < 2 ^ (prefixWord ++ tailWord_810599).sum := by decide
  have hdescent : baseEnd_810599 < baseStart_810599 := by decide
  rcases family_descends (prefixWord ++ tailWord_810599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810619 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3]
def baseStart_810619 : Nat := 118140960795 + 810619 * 2 ^ 59
def prefixEnd_810619 : Nat := 4983230072969 + 3 ^ 40 * 810619 * 2
def baseEnd_810619 : Nat := 416237174667069183134537

theorem tailTrace_810619 : CollatzResearch.WordTrace tailWord_810619 prefixEnd_810619 416237174667069183134537 := by
  unfold tailWord_810619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565703850273280548322911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19710469233515520365548607 29565703850273280548322911)
  ·
    refine ⟨44348555775409920822484367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29565703850273280548322911 44348555775409920822484367)
    ·
      refine ⟨66522833663114881233726551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44348555775409920822484367 66522833663114881233726551)
      ·
        refine ⟨99784250494672321850589827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66522833663114881233726551 99784250494672321850589827)
        ·
          refine ⟨149676375742008482775884741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99784250494672321850589827 149676375742008482775884741)
          ·
            refine ⟨28064320451626590520478389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149676375742008482775884741 28064320451626590520478389)
            ·
              refine ⟨2631030042339992861294849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28064320451626590520478389 2631030042339992861294849)
              ·
                refine ⟨1973272531754994645971137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631030042339992861294849 1973272531754994645971137)
                ·
                  refine ⟨1479954398816245984478353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973272531754994645971137 1479954398816245984478353)
                  ·
                    refine ⟨1109965799112184488358765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479954398816245984478353 1109965799112184488358765)
                    ·
                      refine ⟨416237174667069183134537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1109965799112184488358765 416237174667069183134537)
                      ·
                        rfl

theorem cell23_810619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3].length) (baseStart_810619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810619 prefixEnd_810619 := by exact prefixLift 810619
  have htrace : WordTrace (prefixWord ++ tailWord_810619) baseStart_810619 baseEnd_810619 := by
    simpa [prefixWord, tailWord_810619, baseEnd_810619] using wordTrace_append hprefix tailTrace_810619
  have hstable : (prefixWord ++ tailWord_810619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810619).length < 2 ^ (prefixWord ++ tailWord_810619).sum := by decide
  have hdescent : baseEnd_810619 < baseStart_810619 := by decide
  rcases family_descends (prefixWord ++ tailWord_810619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810677 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_810677 : Nat := 118140960795 + 810677 * 2 ^ 59
def prefixEnd_810677 : Nat := 4983230072969 + 3 ^ 40 * 810677 * 2
def baseEnd_810677 : Nat := 138755652181676652069757

theorem tailTrace_810677 : CollatzResearch.WordTrace tailWord_810677 prefixEnd_810677 138755652181676652069757 := by
  unfold tailWord_810677
  simp only [CollatzResearch.WordTrace]
  refine ⟨29567819284063156453934285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19711879522708770969289523 29567819284063156453934285)
  ·
    refine ⟨11087932231523683670225357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29567819284063156453934285 11087932231523683670225357)
    ·
      refine ⟨4157974586821381376334509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11087932231523683670225357 4157974586821381376334509)
      ·
        refine ⟨1559240470058018016125441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4157974586821381376334509 1559240470058018016125441)
        ·
          refine ⟨1169430352543513512094081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559240470058018016125441 1169430352543513512094081)
          ·
            refine ⟨877072764407635134070561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169430352543513512094081 877072764407635134070561)
            ·
              refine ⟨657804573305726350552921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877072764407635134070561 657804573305726350552921)
              ·
                refine ⟨493353429979294762914691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657804573305726350552921 493353429979294762914691)
                ·
                  refine ⟨740030144968942144372037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493353429979294762914691 740030144968942144372037)
                  ·
                    refine ⟨138755652181676652069757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 740030144968942144372037 138755652181676652069757)
                    ·
                      rfl

theorem cell23_810677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_810677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810677 prefixEnd_810677 := by exact prefixLift 810677
  have htrace : WordTrace (prefixWord ++ tailWord_810677) baseStart_810677 baseEnd_810677 := by
    simpa [prefixWord, tailWord_810677, baseEnd_810677] using wordTrace_append hprefix tailTrace_810677
  have hstable : (prefixWord ++ tailWord_810677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810677).length < 2 ^ (prefixWord ++ tailWord_810677).sum := by decide
  have hdescent : baseEnd_810677 < baseStart_810677 := by decide
  rcases family_descends (prefixWord ++ tailWord_810677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810706 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_810706 : Nat := 118140960795 + 810706 * 2 ^ 59
def prefixEnd_810706 : Nat := 4983230072969 + 3 ^ 40 * 810706 * 2
def baseEnd_810706 : Nat := 416281847484010342746637

theorem tailTrace_810706 : CollatzResearch.WordTrace tailWord_810706 prefixEnd_810706 416281847484010342746637 := by
  unfold tailWord_810706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7392219250239523601684993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19712584667305396271159981 7392219250239523601684993)
  ·
    refine ⟨5544164437679642701263745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7392219250239523601684993 5544164437679642701263745)
    ·
      refine ⟨4158123328259732025947809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5544164437679642701263745 4158123328259732025947809)
      ·
        refine ⟨3118592496194799019460857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4158123328259732025947809 3118592496194799019460857)
        ·
          refine ⟨2338944372146099264595643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118592496194799019460857 2338944372146099264595643)
          ·
            refine ⟨3508416558219148896893465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338944372146099264595643 3508416558219148896893465)
            ·
              refine ⟨2631312418664361672670099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508416558219148896893465 2631312418664361672670099)
              ·
                refine ⟨3946968627996542509005149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631312418664361672670099 3946968627996542509005149)
                ·
                  refine ⟨1480113235498703440876931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3946968627996542509005149 1480113235498703440876931)
                  ·
                    refine ⟨2220169853248055161315397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1480113235498703440876931 2220169853248055161315397)
                    ·
                      refine ⟨416281847484010342746637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2220169853248055161315397 416281847484010342746637)
                      ·
                        rfl

theorem cell23_810706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_810706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810706 prefixEnd_810706 := by exact prefixLift 810706
  have htrace : WordTrace (prefixWord ++ tailWord_810706) baseStart_810706 baseEnd_810706 := by
    simpa [prefixWord, tailWord_810706, baseEnd_810706] using wordTrace_append hprefix tailTrace_810706
  have hstable : (prefixWord ++ tailWord_810706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810706).length < 2 ^ (prefixWord ++ tailWord_810706).sum := by decide
  have hdescent : baseEnd_810706 < baseStart_810706 := by decide
  rcases family_descends (prefixWord ++ tailWord_810706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810719 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_810719 : Nat := 118140960795 + 810719 * 2 ^ 59
def prefixEnd_810719 : Nat := 4983230072969 + 3 ^ 40 * 810719 * 2
def baseEnd_810719 : Nat := 416288522732518791884077

theorem tailTrace_810719 : CollatzResearch.WordTrace tailWord_810719 prefixEnd_810719 416288522732518791884077 := by
  unfold tailWord_810719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569351149910997626963211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19712900766607331751308807 29569351149910997626963211)
  ·
    refine ⟨44354026724866496440444817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29569351149910997626963211 44354026724866496440444817)
    ·
      refine ⟨33265520043649872330333613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44354026724866496440444817 33265520043649872330333613)
      ·
        refine ⟨12474570016368702123875105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33265520043649872330333613 12474570016368702123875105)
        ·
          refine ⟨9355927512276526592906329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12474570016368702123875105 9355927512276526592906329)
          ·
            refine ⟨7016945634207394944679747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9355927512276526592906329 7016945634207394944679747)
            ·
              refine ⟨10525418451311092417019621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016945634207394944679747 10525418451311092417019621)
              ·
                refine ⟨1973515959620829828191179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10525418451311092417019621 1973515959620829828191179)
                ·
                  refine ⟨2960273939431244742286769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973515959620829828191179 2960273939431244742286769)
                  ·
                    refine ⟨2220205454573433556715077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2960273939431244742286769 2220205454573433556715077)
                    ·
                      refine ⟨416288522732518791884077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2220205454573433556715077 416288522732518791884077)
                      ·
                        rfl

theorem cell23_810719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_810719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810719 prefixEnd_810719 := by exact prefixLift 810719
  have htrace : WordTrace (prefixWord ++ tailWord_810719) baseStart_810719 baseEnd_810719 := by
    simpa [prefixWord, tailWord_810719, baseEnd_810719] using wordTrace_append hprefix tailTrace_810719
  have hstable : (prefixWord ++ tailWord_810719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810719).length < 2 ^ (prefixWord ++ tailWord_810719).sum := by decide
  have hdescent : baseEnd_810719 < baseStart_810719 := by decide
  rcases family_descends (prefixWord ++ tailWord_810719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810723 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 4]
def baseStart_810723 : Nat := 118140960795 + 810723 * 2 ^ 59
def prefixEnd_810723 : Nat := 4983230072969 + 3 ^ 40 * 810723 * 2
def baseEnd_810723 : Nat := 416290576655136776234059

theorem tailTrace_810723 : CollatzResearch.WordTrace tailWord_810723 prefixEnd_810723 416290576655136776234059 := by
  unfold tailWord_810723
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569497041896506310108823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19712998027931004206739215 29569497041896506310108823)
  ·
    refine ⟨44354245562844759465163235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29569497041896506310108823 44354245562844759465163235)
    ·
      refine ⟨66531368344267139197744853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44354245562844759465163235 66531368344267139197744853)
      ·
        refine ⟨1559328945568761074947145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 66531368344267139197744853 1559328945568761074947145)
        ·
          refine ⟨1169496709176570806210359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559328945568761074947145 1169496709176570806210359)
          ·
            refine ⟨1754245063764856209315539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169496709176570806210359 1754245063764856209315539)
            ·
              refine ⟨2631367595647284313973309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754245063764856209315539 2631367595647284313973309)
              ·
                refine ⟨986762848367731617739991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631367595647284313973309 986762848367731617739991)
                ·
                  refine ⟨1480144272551597426609987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986762848367731617739991 1480144272551597426609987)
                  ·
                    refine ⟨2220216408827396139914981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1480144272551597426609987 2220216408827396139914981)
                    ·
                      refine ⟨416290576655136776234059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2220216408827396139914981 416290576655136776234059)
                      ·
                        rfl

theorem cell23_810723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_810723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810723 prefixEnd_810723 := by exact prefixLift 810723
  have htrace : WordTrace (prefixWord ++ tailWord_810723) baseStart_810723 baseEnd_810723 := by
    simpa [prefixWord, tailWord_810723, baseEnd_810723] using wordTrace_append hprefix tailTrace_810723
  have hstable : (prefixWord ++ tailWord_810723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810723).length < 2 ^ (prefixWord ++ tailWord_810723).sum := by decide
  have hdescent : baseEnd_810723 < baseStart_810723 := by decide
  rcases family_descends (prefixWord ++ tailWord_810723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810733 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_810733 : Nat := 118140960795 + 810733 * 2 ^ 59
def prefixEnd_810733 : Nat := 4983230072969 + 3 ^ 40 * 810733 * 2
def baseEnd_810733 : Nat := 138765237153893912369671

theorem tailTrace_810733 : CollatzResearch.WordTrace tailWord_810733 prefixEnd_810733 138765237153893912369671 := by
  unfold tailWord_810733
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569861771860278017972853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19713241181240185345315235 29569861771860278017972853)
  ·
    refine ⟨2772174541111901064184955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29569861771860278017972853 2772174541111901064184955)
    ·
      refine ⟨4158261811667851596277433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772174541111901064184955 4158261811667851596277433)
      ·
        refine ⟨3118696358750888697208075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4158261811667851596277433 3118696358750888697208075)
        ·
          refine ⟨4678044538126333045812113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118696358750888697208075 4678044538126333045812113)
          ·
            refine ⟨3508533403594749784359085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4678044538126333045812113 3508533403594749784359085)
            ·
              refine ⟨1315700026348031169134657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3508533403594749784359085 1315700026348031169134657)
              ·
                refine ⟨986775019761023376850993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315700026348031169134657 986775019761023376850993)
                ·
                  refine ⟨740081264820767532638245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 986775019761023376850993 740081264820767532638245)
                  ·
                    refine ⟨138765237153893912369671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 740081264820767532638245 138765237153893912369671)
                    ·
                      rfl

theorem cell23_810733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_810733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810733 prefixEnd_810733 := by exact prefixLift 810733
  have htrace : WordTrace (prefixWord ++ tailWord_810733) baseStart_810733 baseEnd_810733 := by
    simpa [prefixWord, tailWord_810733, baseEnd_810733] using wordTrace_append hprefix tailTrace_810733
  have hstable : (prefixWord ++ tailWord_810733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810733).length < 2 ^ (prefixWord ++ tailWord_810733).sum := by decide
  have hdescent : baseEnd_810733 < baseStart_810733 := by decide
  rcases family_descends (prefixWord ++ tailWord_810733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810739 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3]
def baseStart_810739 : Nat := 118140960795 + 810739 * 2 ^ 59
def prefixEnd_810739 : Nat := 4983230072969 + 3 ^ 40 * 810739 * 2
def baseEnd_810739 : Nat := 416298792345608713633985

theorem tailTrace_810739 : CollatzResearch.WordTrace tailWord_810739 prefixEnd_810739 416298792345608713633985 := by
  unfold tailWord_810739
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570080609838541042691271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19713387073225694028460847 29570080609838541042691271)
  ·
    refine ⟨44355120914757811564036907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29570080609838541042691271 44355120914757811564036907)
    ·
      refine ⟨66532681372136717346055361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44355120914757811564036907 66532681372136717346055361)
      ·
        refine ⟨49899511029102538009541521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66532681372136717346055361 49899511029102538009541521)
        ·
          refine ⟨37424633271826903507156141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49899511029102538009541521 37424633271826903507156141)
          ·
            refine ⟨14034237476935088815183553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37424633271826903507156141 14034237476935088815183553)
            ·
              refine ⟨10525678107701316611387665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14034237476935088815183553 10525678107701316611387665)
              ·
                refine ⟨7894258580775987458540749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10525678107701316611387665 7894258580775987458540749)
                ·
                  refine ⟨2960346967790995296952781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7894258580775987458540749 2960346967790995296952781)
                  ·
                    refine ⟨1110130112921623236357293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960346967790995296952781 1110130112921623236357293)
                    ·
                      refine ⟨416298792345608713633985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110130112921623236357293 416298792345608713633985)
                      ·
                        rfl

theorem cell23_810739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_810739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810739 prefixEnd_810739 := by exact prefixLift 810739
  have htrace : WordTrace (prefixWord ++ tailWord_810739) baseStart_810739 baseEnd_810739 := by
    simpa [prefixWord, tailWord_810739, baseEnd_810739] using wordTrace_append hprefix tailTrace_810739
  have hstable : (prefixWord ++ tailWord_810739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810739).length < 2 ^ (prefixWord ++ tailWord_810739).sum := by decide
  have hdescent : baseEnd_810739 < baseStart_810739 := by decide
  rcases family_descends (prefixWord ++ tailWord_810739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810750 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_810750 : Nat := 118140960795 + 810750 * 2 ^ 59
def prefixEnd_810750 : Nat := 4983230072969 + 3 ^ 40 * 810750 * 2
def baseEnd_810750 : Nat := 138768146877602723532145

theorem tailTrace_810750 : CollatzResearch.WordTrace tailWord_810750 prefixEnd_810750 138768146877602723532145 := by
  unfold tailWord_810750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696310226599836240167713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19713654541865793280894469 3696310226599836240167713)
  ·
    refine ⟨2772232669949877180125785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3696310226599836240167713 2772232669949877180125785)
    ·
      refine ⟨2079174502462407885094339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772232669949877180125785 2079174502462407885094339)
      ·
        refine ⟨3118761753693611827641509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079174502462407885094339 3118761753693611827641509)
        ·
          refine ⟨584767828817552217682783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3118761753693611827641509 584767828817552217682783)
          ·
            refine ⟨877151743226328326524175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584767828817552217682783 877151743226328326524175)
            ·
              refine ⟨1315727614839492489786263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877151743226328326524175 1315727614839492489786263)
              ·
                refine ⟨1973591422259238734679395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315727614839492489786263 1973591422259238734679395)
                ·
                  refine ⟨2960387133388858102019093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973591422259238734679395 2960387133388858102019093)
                  ·
                    refine ⟨138768146877602723532145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2960387133388858102019093 138768146877602723532145)
                    ·
                      rfl

theorem cell23_810750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_810750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810750 prefixEnd_810750 := by exact prefixLift 810750
  have htrace : WordTrace (prefixWord ++ tailWord_810750) baseStart_810750 baseEnd_810750 := by
    simpa [prefixWord, tailWord_810750, baseEnd_810750] using wordTrace_append hprefix tailTrace_810750
  have hstable : (prefixWord ++ tailWord_810750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810750).length < 2 ^ (prefixWord ++ tailWord_810750).sum := by decide
  have hdescent : baseEnd_810750 < baseStart_810750 := by decide
  rcases family_descends (prefixWord ++ tailWord_810750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810783 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 1, 3, 2]
def baseStart_810783 : Nat := 118140960795 + 810783 * 2 ^ 59
def prefixEnd_810783 : Nat := 4983230072969 + 3 ^ 40 * 810783 * 2
def baseEnd_810783 : Nat := 416321385494406541483783

theorem tailTrace_810783 : CollatzResearch.WordTrace tailWord_810783 prefixEnd_810783 416321385494406541483783 := by
  unfold tailWord_810783
  simp only [CollatzResearch.WordTrace]
  refine ⟨29571685421679136557293003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19714456947786091038195335 29571685421679136557293003)
  ·
    refine ⟨44357528132518704835939505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29571685421679136557293003 44357528132518704835939505)
    ·
      refine ⟨33268146099389028626954629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44357528132518704835939505 33268146099389028626954629)
      ·
        refine ⟨6237777393635442867553993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33268146099389028626954629 6237777393635442867553993)
        ·
          refine ⟨4678333045226582150665495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6237777393635442867553993 4678333045226582150665495)
          ·
            refine ⟨7017499567839873225998243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678333045226582150665495 7017499567839873225998243)
            ·
              refine ⟨10526249351759809838997365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7017499567839873225998243 10526249351759809838997365)
              ·
                refine ⟨986835876727482172406003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10526249351759809838997365 986835876727482172406003)
                ·
                  refine ⟨1480253815091223258609005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986835876727482172406003 1480253815091223258609005)
                  ·
                    refine ⟨555095180659208721978377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480253815091223258609005 555095180659208721978377)
                    ·
                      refine ⟨416321385494406541483783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555095180659208721978377 416321385494406541483783)
                      ·
                        rfl

theorem cell23_810783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_810783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810783 prefixEnd_810783 := by exact prefixLift 810783
  have htrace : WordTrace (prefixWord ++ tailWord_810783) baseStart_810783 baseEnd_810783 := by
    simpa [prefixWord, tailWord_810783, baseEnd_810783] using wordTrace_append hprefix tailTrace_810783
  have hstable : (prefixWord ++ tailWord_810783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810783).length < 2 ^ (prefixWord ++ tailWord_810783).sum := by decide
  have hdescent : baseEnd_810783 < baseStart_810783 := by decide
  rcases family_descends (prefixWord ++ tailWord_810783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810799 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_810799 : Nat := 118140960795 + 810799 * 2 ^ 59
def prefixEnd_810799 : Nat := 4983230072969 + 3 ^ 40 * 810799 * 2
def baseEnd_810799 : Nat := 416329601184878478883709

theorem tailTrace_810799 : CollatzResearch.WordTrace tailWord_810799 prefixEnd_810799 416329601184878478883709 := by
  unfold tailWord_810799
  simp only [CollatzResearch.WordTrace]
  refine ⟨29572268989621171289875451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19714845993080780859916967 29572268989621171289875451)
  ·
    refine ⟨44358403484431756934813177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29572268989621171289875451 44358403484431756934813177)
    ·
      refine ⟨33268802613323817701109883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44358403484431756934813177 33268802613323817701109883)
      ·
        refine ⟨49903203919985726551664825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33268802613323817701109883 49903203919985726551664825)
        ·
          refine ⟨37427402939989294913748619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49903203919985726551664825 37427402939989294913748619)
          ·
            refine ⟨56141104409983942370622929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37427402939989294913748619 56141104409983942370622929)
            ·
              refine ⟨42105828307487956777967197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56141104409983942370622929 42105828307487956777967197)
              ·
                refine ⟨15789685615307983791737699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42105828307487956777967197 15789685615307983791737699)
                ·
                  refine ⟨23684528422961975687606549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15789685615307983791737699 23684528422961975687606549)
                  ·
                    refine ⟨1110212269826342610356557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23684528422961975687606549 1110212269826342610356557)
                    ·
                      refine ⟨416329601184878478883709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110212269826342610356557 416329601184878478883709)
                      ·
                        rfl

theorem cell23_810799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_810799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810799 prefixEnd_810799 := by exact prefixLift 810799
  have htrace : WordTrace (prefixWord ++ tailWord_810799) baseStart_810799 baseEnd_810799 := by
    simpa [prefixWord, tailWord_810799, baseEnd_810799] using wordTrace_append hprefix tailTrace_810799
  have hstable : (prefixWord ++ tailWord_810799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810799).length < 2 ^ (prefixWord ++ tailWord_810799).sum := by decide
  have hdescent : baseEnd_810799 < baseStart_810799 := by decide
  rcases family_descends (prefixWord ++ tailWord_810799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810883 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 2, 5]
def baseStart_810883 : Nat := 118140960795 + 810883 * 2 ^ 59
def prefixEnd_810883 : Nat := 4983230072969 + 3 ^ 40 * 810883 * 2
def baseEnd_810883 : Nat := 138790911186618716744441

theorem tailTrace_810883 : CollatzResearch.WordTrace tailWord_810883 prefixEnd_810883 138790911186618716744441 := by
  unfold tailWord_810883
  simp only [CollatzResearch.WordTrace]
  refine ⟨29575332721316853635933303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19716888480877902423955535 29575332721316853635933303)
  ·
    refine ⟨44362999081975280453899955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29575332721316853635933303 44362999081975280453899955)
    ·
      refine ⟨66544498622962920680849933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44362999081975280453899955 66544498622962920680849933)
      ·
        refine ⟨24954186983611095255318725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66544498622962920680849933 24954186983611095255318725)
        ·
          refine ⟨4678910059427080360372261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24954186983611095255318725 4678910059427080360372261)
          ·
            refine ⟨877295636142577567569799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4678910059427080360372261 877295636142577567569799)
            ·
              refine ⟨1315943454213866351354699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877295636142577567569799 1315943454213866351354699)
              ·
                refine ⟨1973915181320799527032049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315943454213866351354699 1973915181320799527032049)
                ·
                  refine ⟨1480436385990599645274037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973915181320799527032049 1480436385990599645274037)
                  ·
                    refine ⟨138790911186618716744441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1480436385990599645274037 138790911186618716744441)
                    ·
                      rfl

theorem cell23_810883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 5].length) (baseStart_810883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810883 prefixEnd_810883 := by exact prefixLift 810883
  have htrace : WordTrace (prefixWord ++ tailWord_810883) baseStart_810883 baseEnd_810883 := by
    simpa [prefixWord, tailWord_810883, baseEnd_810883] using wordTrace_append hprefix tailTrace_810883
  have hstable : (prefixWord ++ tailWord_810883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810883).length < 2 ^ (prefixWord ++ tailWord_810883).sum := by decide
  have hdescent : baseEnd_810883 < baseStart_810883 := by decide
  rcases family_descends (prefixWord ++ tailWord_810883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
