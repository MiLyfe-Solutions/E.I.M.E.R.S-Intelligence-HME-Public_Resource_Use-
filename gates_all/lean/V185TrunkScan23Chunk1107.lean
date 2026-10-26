import V185TrunkScan23Chunk1106

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6555469 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6555469 : Nat := 118140960795 + 6555469 * 2 ^ 59
def prefixEnd_6555469 : Nat := 4983230072969 + 3 ^ 40 * 6555469 * 2
def baseEnd_6555469 : Nat := 1122035504216305810363151

theorem tailTrace_6555469 : CollatzResearch.WordTrace tailWord_6555469 prefixEnd_6555469 1122035504216305810363151 := by
  unfold tailWord_6555469
  simp only [CollatzResearch.WordTrace]
  refine ⟨239097597087662872815597461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159398398058441915210398307 239097597087662872815597461)
  ·
    refine ⟨11207699863484197163231131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239097597087662872815597461 11207699863484197163231131)
    ·
      refine ⟨16811549795226295744846697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11207699863484197163231131 16811549795226295744846697)
      ·
        refine ⟨12608662346419721808635023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16811549795226295744846697 12608662346419721808635023)
        ·
          refine ⟨18912993519629582712952535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12608662346419721808635023 18912993519629582712952535)
          ·
            refine ⟨28369490279444374069428803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18912993519629582712952535 28369490279444374069428803)
            ·
              refine ⟨42554235419166561104143205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28369490279444374069428803 42554235419166561104143205)
              ·
                refine ⟨7978919141093730207026851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42554235419166561104143205 7978919141093730207026851)
                ·
                  refine ⟨11968378711640595310540277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978919141093730207026851 11968378711640595310540277)
                  ·
                    refine ⟨1122035504216305810363151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11968378711640595310540277 1122035504216305810363151)
                    ·
                      rfl

theorem cell23_6555469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6555469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555469 prefixEnd_6555469 := by exact prefixLift 6555469
  have htrace : WordTrace (prefixWord ++ tailWord_6555469) baseStart_6555469 baseEnd_6555469 := by
    simpa [prefixWord, tailWord_6555469, baseEnd_6555469] using wordTrace_append hprefix tailTrace_6555469
  have hstable : (prefixWord ++ tailWord_6555469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555469).length < 2 ^ (prefixWord ++ tailWord_6555469).sum := by decide
  have hdescent : baseEnd_6555469 < baseStart_6555469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555502 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6555502 : Nat := 118140960795 + 6555502 * 2 ^ 59
def prefixEnd_6555502 : Nat := 4983230072969 + 3 ^ 40 * 6555502 * 2
def baseEnd_6555502 : Nat := 3366123457510515801976801

theorem tailTrace_6555502 : CollatzResearch.WordTrace tailWord_6555502 prefixEnd_6555502 3366123457510515801976801 := by
  unfold tailWord_6555502
  simp only [CollatzResearch.WordTrace]
  refine ⟨29887350087067914931443595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159399200464362212967699173 29887350087067914931443595)
  ·
    refine ⟨44831025130601872397165393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29887350087067914931443595 44831025130601872397165393)
    ·
      refine ⟨33623268847951404297874045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44831025130601872397165393 33623268847951404297874045)
      ·
        refine ⟨12608725817981776611702767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33623268847951404297874045 12608725817981776611702767)
        ·
          refine ⟨18913088726972664917554151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12608725817981776611702767 18913088726972664917554151)
          ·
            refine ⟨28369633090458997376331227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18913088726972664917554151 28369633090458997376331227)
            ·
              refine ⟨42554449635688496064496841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28369633090458997376331227 42554449635688496064496841)
              ·
                refine ⟨31915837226766372048372631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42554449635688496064496841 31915837226766372048372631)
                ·
                  refine ⟨47873755840149558072558947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31915837226766372048372631 47873755840149558072558947)
                  ·
                    refine ⟨71810633760224337108838421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47873755840149558072558947 71810633760224337108838421)
                    ·
                      refine ⟨3366123457510515801976801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71810633760224337108838421 3366123457510515801976801)
                      ·
                        rfl

theorem cell23_6555502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6555502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555502 prefixEnd_6555502 := by exact prefixLift 6555502
  have htrace : WordTrace (prefixWord ++ tailWord_6555502) baseStart_6555502 baseEnd_6555502 := by
    simpa [prefixWord, tailWord_6555502, baseEnd_6555502] using wordTrace_append hprefix tailTrace_6555502
  have hstable : (prefixWord ++ tailWord_6555502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555502).length < 2 ^ (prefixWord ++ tailWord_6555502).sum := by decide
  have hdescent : baseEnd_6555502 < baseStart_6555502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555555 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 2, 6]
def baseStart_6555555 : Nat := 118140960795 + 6555555 * 2 ^ 59
def prefixEnd_6555555 : Nat := 4983230072969 + 3 ^ 40 * 6555555 * 2
def baseEnd_6555555 : Nat := 1122050223995068031538019

theorem tailTrace_6555555 : CollatzResearch.WordTrace tailWord_6555555 prefixEnd_6555555 1122050223995068031538019 := by
  unfold tailWord_6555555
  simp only [CollatzResearch.WordTrace]
  refine ⟨239100733765351309503228119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159400489176900873002152079 239100733765351309503228119)
  ·
    refine ⟨358651100648026964254842179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239100733765351309503228119 358651100648026964254842179)
    ·
      refine ⟨537976650972040446382263269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358651100648026964254842179 537976650972040446382263269)
      ·
        refine ⟨100870622057257583696674363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 537976650972040446382263269 100870622057257583696674363)
        ·
          refine ⟨151305933085886375545011545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100870622057257583696674363 151305933085886375545011545)
          ·
            refine ⟨113479449814414781658758659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151305933085886375545011545 113479449814414781658758659)
            ·
              refine ⟨170219174721622172488137989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113479449814414781658758659 170219174721622172488137989)
              ·
                refine ⟨31916095260304157341525873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170219174721622172488137989 31916095260304157341525873)
                ·
                  refine ⟨23937071445228118006144405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31916095260304157341525873 23937071445228118006144405)
                  ·
                    refine ⟨1122050223995068031538019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23937071445228118006144405 1122050223995068031538019)
                    ·
                      rfl

theorem cell23_6555555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_6555555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555555 prefixEnd_6555555 := by exact prefixLift 6555555
  have htrace : WordTrace (prefixWord ++ tailWord_6555555) baseStart_6555555 baseEnd_6555555 := by
    simpa [prefixWord, tailWord_6555555, baseEnd_6555555] using wordTrace_append hprefix tailTrace_6555555
  have hstable : (prefixWord ++ tailWord_6555555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555555).length < 2 ^ (prefixWord ++ tailWord_6555555).sum := by decide
  have hdescent : baseEnd_6555555 < baseStart_6555555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555556 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_6555556 : Nat := 118140960795 + 6555556 * 2 ^ 59
def prefixEnd_6555556 : Nat := 4983230072969 + 3 ^ 40 * 6555556 * 2
def baseEnd_6555556 : Nat := 3366151185465858590701553

theorem tailTrace_6555556 : CollatzResearch.WordTrace tailWord_6555556 prefixEnd_6555556 3366151185465858590701553 := by
  unfold tailWord_6555556
  simp only [CollatzResearch.WordTrace]
  refine ⟨119550385119173843337007261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159400513492231791116009681 119550385119173843337007261)
  ·
    refine ⟨44831394419690191251377723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119550385119173843337007261 44831394419690191251377723)
    ·
      refine ⟨67247091629535286877066585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44831394419690191251377723 67247091629535286877066585)
      ·
        refine ⟨50435318722151465157799939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67247091629535286877066585 50435318722151465157799939)
        ·
          refine ⟨75652978083227197736699909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50435318722151465157799939 75652978083227197736699909)
          ·
            refine ⟨14184933390605099575631233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75652978083227197736699909 14184933390605099575631233)
            ·
              refine ⟨10638700042953824681723425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14184933390605099575631233 10638700042953824681723425)
              ·
                refine ⟨7979025032215368511292569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10638700042953824681723425 7979025032215368511292569)
                ·
                  refine ⟨5984268774161526383469427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7979025032215368511292569 5984268774161526383469427)
                  ·
                    refine ⟨8976403161242289575204141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5984268774161526383469427 8976403161242289575204141)
                    ·
                      refine ⟨3366151185465858590701553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8976403161242289575204141 3366151185465858590701553)
                      ·
                        rfl

theorem cell23_6555556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_6555556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555556 prefixEnd_6555556 := by exact prefixLift 6555556
  have htrace : WordTrace (prefixWord ++ tailWord_6555556) baseStart_6555556 baseEnd_6555556 := by
    simpa [prefixWord, tailWord_6555556, baseEnd_6555556] using wordTrace_append hprefix tailTrace_6555556
  have hstable : (prefixWord ++ tailWord_6555556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555556).length < 2 ^ (prefixWord ++ tailWord_6555556).sum := by decide
  have hdescent : baseEnd_6555556 < baseStart_6555556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555613 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_6555613 : Nat := 118140960795 + 6555613 * 2 ^ 59
def prefixEnd_6555613 : Nat := 4983230072969 + 3 ^ 40 * 6555613 * 2
def baseEnd_6555613 : Nat := 3366180453863164867688791

theorem tailTrace_6555613 : CollatzResearch.WordTrace tailWord_6555613 prefixEnd_6555613 3366180453863164867688791 := by
  unfold tailWord_6555613
  simp only [CollatzResearch.WordTrace]
  refine ⟨239102849199141185408839493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159401899466094123605892995 239102849199141185408839493)
  ·
    refine ⟨44831784224838972264157405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239102849199141185408839493 44831784224838972264157405)
    ·
      refine ⟨16811919084314614599059027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44831784224838972264157405 16811919084314614599059027)
      ·
        refine ⟨25217878626471921898588541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16811919084314614599059027 25217878626471921898588541)
        ·
          refine ⟨9456704484926970711970703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25217878626471921898588541 9456704484926970711970703)
          ·
            refine ⟨14185056727390456067956055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456704484926970711970703 14185056727390456067956055)
            ·
              refine ⟨21277585091085684101934083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185056727390456067956055 21277585091085684101934083)
              ·
                refine ⟨31916377636628526152901125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21277585091085684101934083 31916377636628526152901125)
                ·
                  refine ⟨5984320806867848653668961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31916377636628526152901125 5984320806867848653668961)
                  ·
                    refine ⟨4488240605150886490251721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984320806867848653668961 4488240605150886490251721)
                    ·
                      refine ⟨3366180453863164867688791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488240605150886490251721 3366180453863164867688791)
                      ·
                        rfl

theorem cell23_6555613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_6555613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555613 prefixEnd_6555613 := by exact prefixLift 6555613
  have htrace : WordTrace (prefixWord ++ tailWord_6555613) baseStart_6555613 baseEnd_6555613 := by
    simpa [prefixWord, tailWord_6555613, baseEnd_6555613] using wordTrace_append hprefix tailTrace_6555613
  have hstable : (prefixWord ++ tailWord_6555613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555613).length < 2 ^ (prefixWord ++ tailWord_6555613).sum := by decide
  have hdescent : baseEnd_6555613 < baseStart_6555613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555619 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 5]
def baseStart_6555619 : Nat := 118140960795 + 6555619 * 2 ^ 59
def prefixEnd_6555619 : Nat := 4983230072969 + 3 ^ 40 * 6555619 * 2
def baseEnd_6555619 : Nat := 374020392749676871579307

theorem tailTrace_6555619 : CollatzResearch.WordTrace tailWord_6555619 prefixEnd_6555619 374020392749676871579307 := by
  unfold tailWord_6555619
  simp only [CollatzResearch.WordTrace]
  refine ⟨239103068037119448433557911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159402045358079632289038607 239103068037119448433557911)
  ·
    refine ⟨358654602055679172650336867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239103068037119448433557911 358654602055679172650336867)
    ·
      refine ⟨537981903083518758975505301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358654602055679172650336867 537981903083518758975505301)
      ·
        refine ⟨25217901707039941826976811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 537981903083518758975505301 25217901707039941826976811)
        ·
          refine ⟨37826852560559912740465217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25217901707039941826976811 37826852560559912740465217)
          ·
            refine ⟨28370139420419934555348913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37826852560559912740465217 28370139420419934555348913)
            ·
              refine ⟨21277604565314950916511685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28370139420419934555348913 21277604565314950916511685)
              ·
                refine ⟨3989550855996553296845941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21277604565314950916511685 3989550855996553296845941)
                ·
                  refine ⟨374020392749676871579307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3989550855996553296845941 374020392749676871579307)
                  ·
                    rfl

theorem cell23_6555619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 5].length) (baseStart_6555619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555619 prefixEnd_6555619 := by exact prefixLift 6555619
  have htrace : WordTrace (prefixWord ++ tailWord_6555619) baseStart_6555619 baseEnd_6555619 := by
    simpa [prefixWord, tailWord_6555619, baseEnd_6555619] using wordTrace_append hprefix tailTrace_6555619
  have hstable : (prefixWord ++ tailWord_6555619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555619).length < 2 ^ (prefixWord ++ tailWord_6555619).sum := by decide
  have hdescent : baseEnd_6555619 < baseStart_6555619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555630 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_6555630 : Nat := 118140960795 + 6555630 * 2 ^ 59
def prefixEnd_6555630 : Nat := 4983230072969 + 3 ^ 40 * 6555630 * 2
def baseEnd_6555630 : Nat := 3366189183034291301176213

theorem tailTrace_6555630 : CollatzResearch.WordTrace tailWord_6555630 prefixEnd_6555630 3366189183034291301176213 := by
  unfold tailWord_6555630
  simp only [CollatzResearch.WordTrace]
  refine ⟨29887933655009949664026043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159402312826719731541472229 29887933655009949664026043)
  ·
    refine ⟨44831900482514924496039065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29887933655009949664026043 44831900482514924496039065)
    ·
      refine ⟨33623925361886193372029299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44831900482514924496039065 33623925361886193372029299)
      ·
        refine ⟨50435888042829290058043949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33623925361886193372029299 50435888042829290058043949)
        ·
          refine ⟨18913458016060983771766481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50435888042829290058043949 18913458016060983771766481)
          ·
            refine ⟨14185093512045737828824861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18913458016060983771766481 14185093512045737828824861)
            ·
              refine ⟨5319410067017151685809323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14185093512045737828824861 5319410067017151685809323)
              ·
                refine ⟨7979115100525727528713985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319410067017151685809323 7979115100525727528713985)
                ·
                  refine ⟨5984336325394295646535489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7979115100525727528713985 5984336325394295646535489)
                  ·
                    refine ⟨4488252244045721734901617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984336325394295646535489 4488252244045721734901617)
                    ·
                      refine ⟨3366189183034291301176213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488252244045721734901617 3366189183034291301176213)
                      ·
                        rfl

theorem cell23_6555630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_6555630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555630 prefixEnd_6555630 := by exact prefixLift 6555630
  have htrace : WordTrace (prefixWord ++ tailWord_6555630) baseStart_6555630 baseEnd_6555630 := by
    simpa [prefixWord, tailWord_6555630, baseEnd_6555630] using wordTrace_append hprefix tailTrace_6555630
  have hstable : (prefixWord ++ tailWord_6555630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555630).length < 2 ^ (prefixWord ++ tailWord_6555630).sum := by decide
  have hdescent : baseEnd_6555630 < baseStart_6555630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555729 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_6555729 : Nat := 118140960795 + 6555729 * 2 ^ 59
def prefixEnd_6555729 : Nat := 4983230072969 + 3 ^ 40 * 6555729 * 2
def baseEnd_6555729 : Nat := 3366240017619086413838257

theorem tailTrace_6555729 : CollatzResearch.WordTrace tailWord_6555729 prefixEnd_6555729 3366240017619086413838257 := by
  unfold tailWord_6555729
  simp only [CollatzResearch.WordTrace]
  refine ⟨239107080066720937220062241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159404720044480624813374827 239107080066720937220062241)
  ·
    refine ⟨179330310050040702915046681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239107080066720937220062241 179330310050040702915046681)
    ·
      refine ⟨134497732537530527186285011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179330310050040702915046681 134497732537530527186285011)
      ·
        refine ⟨201746598806295790779427517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134497732537530527186285011 201746598806295790779427517)
        ·
          refine ⟨75654974552360921542285319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201746598806295790779427517 75654974552360921542285319)
          ·
            refine ⟨113482461828541382313427979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75654974552360921542285319 113482461828541382313427979)
            ·
              refine ⟨170223692742812073470141969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113482461828541382313427979 170223692742812073470141969)
              ·
                refine ⟨127667769557109055102606477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170223692742812073470141969 127667769557109055102606477)
                ·
                  refine ⟨47875413583915895663477429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127667769557109055102606477 47875413583915895663477429)
                  ·
                    refine ⟨4488320023492115218451009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47875413583915895663477429 4488320023492115218451009)
                    ·
                      refine ⟨3366240017619086413838257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488320023492115218451009 3366240017619086413838257)
                      ·
                        rfl

theorem cell23_6555729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_6555729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555729 prefixEnd_6555729 := by exact prefixLift 6555729
  have htrace : WordTrace (prefixWord ++ tailWord_6555729) baseStart_6555729 baseEnd_6555729 := by
    simpa [prefixWord, tailWord_6555729, baseEnd_6555729] using wordTrace_append hprefix tailTrace_6555729
  have hstable : (prefixWord ++ tailWord_6555729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555729).length < 2 ^ (prefixWord ++ tailWord_6555729).sum := by decide
  have hdescent : baseEnd_6555729 < baseStart_6555729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555759 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_6555759 : Nat := 118140960795 + 6555759 * 2 ^ 59
def prefixEnd_6555759 : Nat := 4983230072969 + 3 ^ 40 * 6555759 * 2
def baseEnd_6555759 : Nat := 3366255422038721296463119

theorem tailTrace_6555759 : CollatzResearch.WordTrace tailWord_6555759 prefixEnd_6555759 3366255422038721296463119 := by
  unfold tailWord_6555759
  simp only [CollatzResearch.WordTrace]
  refine ⟨239108174256612252343654331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159405449504408168229102887 239108174256612252343654331)
  ·
    refine ⟨358662261384918378515481497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239108174256612252343654331 358662261384918378515481497)
    ·
      refine ⟨268996696038688783886611123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358662261384918378515481497 268996696038688783886611123)
      ·
        refine ⟨403495044058033175829916685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268996696038688783886611123 403495044058033175829916685)
        ·
          refine ⟨151310641521762440936218757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403495044058033175829916685 151310641521762440936218757)
          ·
            refine ⟨28370745285330457675541017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151310641521762440936218757 28370745285330457675541017)
            ·
              refine ⟨21278058963997843256655763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28370745285330457675541017 21278058963997843256655763)
              ·
                refine ⟨31917088445996764884983645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278058963997843256655763 31917088445996764884983645)
                ·
                  refine ⟨11968908167248786831868867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31917088445996764884983645 11968908167248786831868867)
                  ·
                    refine ⟨17953362250873180247803301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11968908167248786831868867 17953362250873180247803301)
                    ·
                      refine ⟨3366255422038721296463119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17953362250873180247803301 3366255422038721296463119)
                      ·
                        rfl

theorem cell23_6555759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_6555759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555759 prefixEnd_6555759 := by exact prefixLift 6555759
  have htrace : WordTrace (prefixWord ++ tailWord_6555759) baseStart_6555759 baseEnd_6555759 := by
    simpa [prefixWord, tailWord_6555759, baseEnd_6555759] using wordTrace_append hprefix tailTrace_6555759
  have hstable : (prefixWord ++ tailWord_6555759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555759).length < 2 ^ (prefixWord ++ tailWord_6555759).sum := by decide
  have hdescent : baseEnd_6555759 < baseStart_6555759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555769 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_6555769 : Nat := 118140960795 + 6555769 * 2 ^ 59
def prefixEnd_6555769 : Nat := 4983230072969 + 3 ^ 40 * 6555769 * 2
def baseEnd_6555769 : Nat := 1122086852281755419112691

theorem tailTrace_6555769 : CollatzResearch.WordTrace tailWord_6555769 prefixEnd_6555769 1122086852281755419112691 := by
  unfold tailWord_6555769
  simp only [CollatzResearch.WordTrace]
  refine ⟨239108538986576024051518361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159405692657717349367678907 239108538986576024051518361)
  ·
    refine ⟨179331404239932018038638771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239108538986576024051518361 179331404239932018038638771)
    ·
      refine ⟨268997106359898027057958157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179331404239932018038638771 268997106359898027057958157)
      ·
        refine ⟨100873914884961760146734309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268997106359898027057958157 100873914884961760146734309)
        ·
          refine ⟨18913859040930330027512683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100873914884961760146734309 18913859040930330027512683)
          ·
            refine ⟨28370788561395495041269025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18913859040930330027512683 28370788561395495041269025)
            ·
              refine ⟨21278091421046621280951769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28370788561395495041269025 21278091421046621280951769)
              ·
                refine ⟨15958568565784965960713827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21278091421046621280951769 15958568565784965960713827)
                ·
                  refine ⟨23937852848677448941070741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15958568565784965960713827 23937852848677448941070741)
                  ·
                    refine ⟨1122086852281755419112691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23937852848677448941070741 1122086852281755419112691)
                    ·
                      rfl

theorem cell23_6555769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_6555769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555769 prefixEnd_6555769 := by exact prefixLift 6555769
  have htrace : WordTrace (prefixWord ++ tailWord_6555769) baseStart_6555769 baseEnd_6555769 := by
    simpa [prefixWord, tailWord_6555769, baseEnd_6555769] using wordTrace_append hprefix tailTrace_6555769
  have hstable : (prefixWord ++ tailWord_6555769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555769).length < 2 ^ (prefixWord ++ tailWord_6555769).sum := by decide
  have hdescent : baseEnd_6555769 < baseStart_6555769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555773 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_6555773 : Nat := 118140960795 + 6555773 * 2 ^ 59
def prefixEnd_6555773 : Nat := 4983230072969 + 3 ^ 40 * 6555773 * 2
def baseEnd_6555773 : Nat := 1122087536922628080562685

theorem tailTrace_6555773 : CollatzResearch.WordTrace tailWord_6555773 prefixEnd_6555773 1122087536922628080562685 := by
  unfold tailWord_6555773
  simp only [CollatzResearch.WordTrace]
  refine ⟨239108684878561532734663973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159405789919041021823109315 239108684878561532734663973)
  ·
    refine ⟨44832878414730287387749495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239108684878561532734663973 44832878414730287387749495)
    ·
      refine ⟨67249317622095431081624243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44832878414730287387749495 67249317622095431081624243)
      ·
        refine ⟨100873976433143146622436365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67249317622095431081624243 100873976433143146622436365)
        ·
          refine ⟨37827741162428679983413637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100873976433143146622436365 37827741162428679983413637)
          ·
            refine ⟨7092701467955377496890057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37827741162428679983413637 7092701467955377496890057)
            ·
              refine ⟨5319526100966533122667543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7092701467955377496890057 5319526100966533122667543)
              ·
                refine ⟨7979289151449799684001315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319526100966533122667543 7979289151449799684001315)
                ·
                  refine ⟨11968933727174699526001973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7979289151449799684001315 11968933727174699526001973)
                  ·
                    refine ⟨1122087536922628080562685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11968933727174699526001973 1122087536922628080562685)
                    ·
                      rfl

theorem cell23_6555773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_6555773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555773 prefixEnd_6555773 := by exact prefixLift 6555773
  have htrace : WordTrace (prefixWord ++ tailWord_6555773) baseStart_6555773 baseEnd_6555773 := by
    simpa [prefixWord, tailWord_6555773, baseEnd_6555773] using wordTrace_append hprefix tailTrace_6555773
  have hstable : (prefixWord ++ tailWord_6555773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555773).length < 2 ^ (prefixWord ++ tailWord_6555773).sum := by decide
  have hdescent : baseEnd_6555773 < baseStart_6555773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555776 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2]
def baseStart_6555776 : Nat := 118140960795 + 6555776 * 2 ^ 59
def prefixEnd_6555776 : Nat := 4983230072969 + 3 ^ 40 * 6555776 * 2
def baseEnd_6555776 : Nat := 3366264151209847729950541

theorem tailTrace_6555776 : CollatzResearch.WordTrace tailWord_6555776 prefixEnd_6555776 3366264151209847729950541 := by
  unfold tailWord_6555776
  simp only [CollatzResearch.WordTrace]
  refine ⟨119554397148775332123511591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159405862865033776164682121 119554397148775332123511591)
  ·
    refine ⟨179331595723162998185267387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119554397148775332123511591 179331595723162998185267387)
    ·
      refine ⟨268997393584744497277901081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179331595723162998185267387 268997393584744497277901081)
      ·
        refine ⟨201748045188558372958425811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268997393584744497277901081 201748045188558372958425811)
        ·
          refine ⟨302622067782837559437638717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201748045188558372958425811 302622067782837559437638717)
          ·
            refine ⟨113483275418564084789114519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302622067782837559437638717 113483275418564084789114519)
            ·
              refine ⟨170224913127846127183671779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113483275418564084789114519 170224913127846127183671779)
              ·
                refine ⟨255337369691769190775507669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170224913127846127183671779 255337369691769190775507669)
                ·
                  refine ⟨5984469602150840408800961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 255337369691769190775507669 5984469602150840408800961)
                  ·
                    refine ⟨4488352201613130306600721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984469602150840408800961 4488352201613130306600721)
                    ·
                      refine ⟨3366264151209847729950541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488352201613130306600721 3366264151209847729950541)
                      ·
                        rfl

theorem cell23_6555776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_6555776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555776 prefixEnd_6555776 := by exact prefixLift 6555776
  have htrace : WordTrace (prefixWord ++ tailWord_6555776) baseStart_6555776 baseEnd_6555776 := by
    simpa [prefixWord, tailWord_6555776, baseEnd_6555776] using wordTrace_append hprefix tailTrace_6555776
  have hstable : (prefixWord ++ tailWord_6555776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555776).length < 2 ^ (prefixWord ++ tailWord_6555776).sum := by decide
  have hdescent : baseEnd_6555776 < baseStart_6555776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555786 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_6555786 : Nat := 118140960795 + 6555786 * 2 ^ 59
def prefixEnd_6555786 : Nat := 4983230072969 + 3 ^ 40 * 6555786 * 2
def baseEnd_6555786 : Nat := 1122089762005464230275165

theorem tailTrace_6555786 : CollatzResearch.WordTrace tailWord_6555786 prefixEnd_6555786 1122089762005464230275165 := by
  unfold tailWord_6555786
  simp only [CollatzResearch.WordTrace]
  refine ⟨59777289756878608988721803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159406106018342957303258141 59777289756878608988721803)
  ·
    refine ⟨89665934635317913483082705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59777289756878608988721803 89665934635317913483082705)
    ·
      refine ⟨67249450976488435112312029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89665934635317913483082705 67249450976488435112312029)
      ·
        refine ⟨25218544116183163167117011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67249450976488435112312029 25218544116183163167117011)
        ·
          refine ⟨37827816174274744750675517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25218544116183163167117011 37827816174274744750675517)
          ·
            refine ⟨14185431065353029281503319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37827816174274744750675517 14185431065353029281503319)
            ·
              refine ⟨21278146598029543922254979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185431065353029281503319 21278146598029543922254979)
              ·
                refine ⟨31917219897044315883382469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278146598029543922254979 31917219897044315883382469)
                ·
                  refine ⟨5984478730695809228134213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31917219897044315883382469 5984478730695809228134213)
                  ·
                    refine ⟨1122089762005464230275165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5984478730695809228134213 1122089762005464230275165)
                    ·
                      rfl

theorem cell23_6555786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_6555786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555786 prefixEnd_6555786 := by exact prefixLift 6555786
  have htrace : WordTrace (prefixWord ++ tailWord_6555786) baseStart_6555786 baseEnd_6555786 := by
    simpa [prefixWord, tailWord_6555786, baseEnd_6555786] using wordTrace_append hprefix tailTrace_6555786
  have hstable : (prefixWord ++ tailWord_6555786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555786).length < 2 ^ (prefixWord ++ tailWord_6555786).sum := by decide
  have hdescent : baseEnd_6555786 < baseStart_6555786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555810 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_6555810 : Nat := 118140960795 + 6555810 * 2 ^ 59
def prefixEnd_6555810 : Nat := 4983230072969 + 3 ^ 40 * 6555810 * 2
def baseEnd_6555810 : Nat := 3366281609552100596925385

theorem tailTrace_6555810 : CollatzResearch.WordTrace tailWord_6555810 prefixEnd_6555810 3366281609552100596925385 := by
  unfold tailWord_6555810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59777508594856872013440221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159406689586284992035840589 59777508594856872013440221)
  ·
    refine ⟨22416565723071327005040083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59777508594856872013440221 22416565723071327005040083)
    ·
      refine ⟨33624848584606990507560125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22416565723071327005040083 33624848584606990507560125)
      ·
        refine ⟨12609318219227621440335047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33624848584606990507560125 12609318219227621440335047)
        ·
          refine ⟨18913977328841432160502571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12609318219227621440335047 18913977328841432160502571)
          ·
            refine ⟨28370965993262148240753857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18913977328841432160502571 28370965993262148240753857)
            ·
              refine ⟨21278224494946611180565393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28370965993262148240753857 21278224494946611180565393)
              ·
                refine ⟨15958668371209958385424045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21278224494946611180565393 15958668371209958385424045)
                ·
                  refine ⟨5984500639203734394534017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15958668371209958385424045 5984500639203734394534017)
                  ·
                    refine ⟨4488375479402800795900513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984500639203734394534017 4488375479402800795900513)
                    ·
                      refine ⟨3366281609552100596925385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488375479402800795900513 3366281609552100596925385)
                      ·
                        rfl

theorem cell23_6555810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_6555810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555810 prefixEnd_6555810 := by exact prefixLift 6555810
  have htrace : WordTrace (prefixWord ++ tailWord_6555810) baseStart_6555810 baseEnd_6555810 := by
    simpa [prefixWord, tailWord_6555810, baseEnd_6555810] using wordTrace_append hprefix tailTrace_6555810
  have hstable : (prefixWord ++ tailWord_6555810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555810).length < 2 ^ (prefixWord ++ tailWord_6555810).sum := by decide
  have hdescent : baseEnd_6555810 < baseStart_6555810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555826 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_6555826 : Nat := 118140960795 + 6555826 * 2 ^ 59
def prefixEnd_6555826 : Nat := 4983230072969 + 3 ^ 40 * 6555826 * 2
def baseEnd_6555826 : Nat := 3366289825242572534325311

theorem tailTrace_6555826 : CollatzResearch.WordTrace tailWord_6555826 prefixEnd_6555826 3366289825242572534325311 := by
  unfold tailWord_6555826
  simp only [CollatzResearch.WordTrace]
  refine ⟨59777654486842380696585833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159407078631579681857562221 59777654486842380696585833)
  ·
    refine ⟨44833240865131785522439375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59777654486842380696585833 44833240865131785522439375)
    ·
      refine ⟨67249861297697678283659063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44833240865131785522439375 67249861297697678283659063)
      ·
        refine ⟨100874791946546517425488595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67249861297697678283659063 100874791946546517425488595)
        ·
          refine ⟨151312187919819776138232893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100874791946546517425488595 151312187919819776138232893)
          ·
            refine ⟨56742070469932416051837335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151312187919819776138232893 56742070469932416051837335)
            ·
              refine ⟨85113105704898624077756003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56742070469932416051837335 85113105704898624077756003)
              ·
                refine ⟨127669658557347936116634005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85113105704898624077756003 127669658557347936116634005)
                ·
                  refine ⟨5984515244875684505467219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127669658557347936116634005 5984515244875684505467219)
                  ·
                    refine ⟨8976772867313526758200829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5984515244875684505467219 8976772867313526758200829)
                    ·
                      refine ⟨3366289825242572534325311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8976772867313526758200829 3366289825242572534325311)
                      ·
                        rfl

theorem cell23_6555826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_6555826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555826 prefixEnd_6555826 := by exact prefixLift 6555826
  have htrace : WordTrace (prefixWord ++ tailWord_6555826) baseStart_6555826 baseEnd_6555826 := by
    simpa [prefixWord, tailWord_6555826, baseEnd_6555826] using wordTrace_append hprefix tailTrace_6555826
  have hstable : (prefixWord ++ tailWord_6555826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555826).length < 2 ^ (prefixWord ++ tailWord_6555826).sum := by decide
  have hdescent : baseEnd_6555826 < baseStart_6555826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555844 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_6555844 : Nat := 118140960795 + 6555844 * 2 ^ 59
def prefixEnd_6555844 : Nat := 4983230072969 + 3 ^ 40 * 6555844 * 2
def baseEnd_6555844 : Nat := 3366299067894353463900229

theorem tailTrace_6555844 : CollatzResearch.WordTrace tailWord_6555844 prefixEnd_6555844 3366299067894353463900229 := by
  unfold tailWord_6555844
  simp only [CollatzResearch.WordTrace]
  refine ⟨119555637230652155930249293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159407516307536207906999057 119555637230652155930249293)
  ·
    refine ⟨44833363961494558473843485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119555637230652155930249293 44833363961494558473843485)
    ·
      refine ⟨16812511485560459427691307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44833363961494558473843485 16812511485560459427691307)
      ·
        refine ⟨25218767228340689141536961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16812511485560459427691307 25218767228340689141536961)
        ·
          refine ⟨18914075421255516856152721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25218767228340689141536961 18914075421255516856152721)
          ·
            refine ⟨14185556565941637642114541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18914075421255516856152721 14185556565941637642114541)
            ·
              refine ⟨5319583712228114115792953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14185556565941637642114541 5319583712228114115792953)
              ·
                refine ⟨3989687784171085586844715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319583712228114115792953 3989687784171085586844715)
                ·
                  refine ⟨5984531676256628380267073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989687784171085586844715 5984531676256628380267073)
                  ·
                    refine ⟨4488398757192471285200305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984531676256628380267073 4488398757192471285200305)
                    ·
                      refine ⟨3366299067894353463900229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488398757192471285200305 3366299067894353463900229)
                      ·
                        rfl

theorem cell23_6555844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_6555844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555844 prefixEnd_6555844 := by exact prefixLift 6555844
  have htrace : WordTrace (prefixWord ++ tailWord_6555844) baseStart_6555844 baseEnd_6555844 := by
    simpa [prefixWord, tailWord_6555844, baseEnd_6555844] using wordTrace_append hprefix tailTrace_6555844
  have hstable : (prefixWord ++ tailWord_6555844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555844).length < 2 ^ (prefixWord ++ tailWord_6555844).sum := by decide
  have hdescent : baseEnd_6555844 < baseStart_6555844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555899 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3]
def baseStart_6555899 : Nat := 118140960795 + 6555899 * 2 ^ 59
def prefixEnd_6555899 : Nat := 4983230072969 + 3 ^ 40 * 6555899 * 2
def baseEnd_6555899 : Nat := 3366327309330350748712475

theorem tailTrace_6555899 : CollatzResearch.WordTrace tailWord_6555899 prefixEnd_6555899 3366327309330350748712475 := by
  unfold tailWord_6555899
  simp only [CollatzResearch.WordTrace]
  refine ⟨239113280476105056253750751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159408853650736704169167167 239113280476105056253750751)
  ·
    refine ⟨358669920714157584380626127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239113280476105056253750751 358669920714157584380626127)
    ·
      refine ⟨538004881071236376570939191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358669920714157584380626127 538004881071236376570939191)
      ·
        refine ⟨807007321606854564856408787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538004881071236376570939191 807007321606854564856408787)
        ·
          refine ⟨1210510982410281847284613181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807007321606854564856408787 1210510982410281847284613181)
          ·
            refine ⟨453941618403855692731729943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210510982410281847284613181 453941618403855692731729943)
            ·
              refine ⟨680912427605783539097594915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453941618403855692731729943 680912427605783539097594915)
              ·
                refine ⟨1021368641408675308646392373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680912427605783539097594915 1021368641408675308646392373)
                ·
                  refine ⟨95753310132063310185599285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1021368641408675308646392373 95753310132063310185599285)
                  ·
                    refine ⟨8976872824880935329899933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95753310132063310185599285 8976872824880935329899933)
                    ·
                      refine ⟨3366327309330350748712475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8976872824880935329899933 3366327309330350748712475)
                      ·
                        rfl

theorem cell23_6555899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3].length) (baseStart_6555899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555899 prefixEnd_6555899 := by exact prefixLift 6555899
  have htrace : WordTrace (prefixWord ++ tailWord_6555899) baseStart_6555899 baseEnd_6555899 := by
    simpa [prefixWord, tailWord_6555899, baseEnd_6555899] using wordTrace_append hprefix tailTrace_6555899
  have hstable : (prefixWord ++ tailWord_6555899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555899).length < 2 ^ (prefixWord ++ tailWord_6555899).sum := by decide
  have hdescent : baseEnd_6555899 < baseStart_6555899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555900 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_6555900 : Nat := 118140960795 + 6555900 * 2 ^ 59
def prefixEnd_6555900 : Nat := 4983230072969 + 3 ^ 40 * 6555900 * 2
def baseEnd_6555900 : Nat := 3366327822811005244799971

theorem tailTrace_6555900 : CollatzResearch.WordTrace tailWord_6555900 prefixEnd_6555900 3366327822811005244799971 := by
  unfold tailWord_6555900
  simp only [CollatzResearch.WordTrace]
  refine ⟨119556658474550716712268577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159408877966067622283024769 119556658474550716712268577)
  ·
    refine ⟨89667493855913037534201433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119556658474550716712268577 89667493855913037534201433)
    ·
      refine ⟨67250620391934778150651075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89667493855913037534201433 67250620391934778150651075)
      ·
        refine ⟨100875930587902167225976613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67250620391934778150651075 100875930587902167225976613)
        ·
          refine ⟨18914236985231656354870615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100875930587902167225976613 18914236985231656354870615)
          ·
            refine ⟨28371355477847484532305923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18914236985231656354870615 28371355477847484532305923)
            ·
              refine ⟨42557033216771226798458885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28371355477847484532305923 42557033216771226798458885)
              ·
                refine ⟨7979443728144605024711041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42557033216771226798458885 7979443728144605024711041)
                ·
                  refine ⟨5984582796108453768533281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7979443728144605024711041 5984582796108453768533281)
                  ·
                    refine ⟨4488437097081340326399961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984582796108453768533281 4488437097081340326399961)
                    ·
                      refine ⟨3366327822811005244799971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488437097081340326399961 3366327822811005244799971)
                      ·
                        rfl

theorem cell23_6555900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_6555900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555900 prefixEnd_6555900 := by exact prefixLift 6555900
  have htrace : WordTrace (prefixWord ++ tailWord_6555900) baseStart_6555900 baseEnd_6555900 := by
    simpa [prefixWord, tailWord_6555900, baseEnd_6555900] using wordTrace_append hprefix tailTrace_6555900
  have hstable : (prefixWord ++ tailWord_6555900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555900).length < 2 ^ (prefixWord ++ tailWord_6555900).sum := by decide
  have hdescent : baseEnd_6555900 < baseStart_6555900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555916 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_6555916 : Nat := 118140960795 + 6555916 * 2 ^ 59
def prefixEnd_6555916 : Nat := 4983230072969 + 3 ^ 40 * 6555916 * 2
def baseEnd_6555916 : Nat := 3366336038501477182199897

theorem tailTrace_6555916 : CollatzResearch.WordTrace tailWord_6555916 prefixEnd_6555916 3366336038501477182199897 := by
  unfold tailWord_6555916
  simp only [CollatzResearch.WordTrace]
  refine ⟨119556950258521734078559801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159409267011362312104746401 119556950258521734078559801)
  ·
    refine ⟨89667712693891300558919851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119556950258521734078559801 89667712693891300558919851)
    ·
      refine ⟨134501569040836950838379777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89667712693891300558919851 134501569040836950838379777)
      ·
        refine ⟨100876176780627713128784833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134501569040836950838379777 100876176780627713128784833)
        ·
          refine ⟨75657132585470784846588625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100876176780627713128784833 75657132585470784846588625)
          ·
            refine ⟨56742849439103088634941469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75657132585470784846588625 56742849439103088634941469)
            ·
              refine ⟨21278568539663658238103051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56742849439103088634941469 21278568539663658238103051)
              ·
                refine ⟨31917852809495487357154577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278568539663658238103051 31917852809495487357154577)
                ·
                  refine ⟨23938389607121615517865933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31917852809495487357154577 23938389607121615517865933)
                  ·
                    refine ⟨8976896102670605819199725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23938389607121615517865933 8976896102670605819199725)
                    ·
                      refine ⟨3366336038501477182199897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8976896102670605819199725 3366336038501477182199897)
                      ·
                        rfl

theorem cell23_6555916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_6555916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555916 prefixEnd_6555916 := by exact prefixLift 6555916
  have htrace : WordTrace (prefixWord ++ tailWord_6555916) baseStart_6555916 baseEnd_6555916 := by
    simpa [prefixWord, tailWord_6555916, baseEnd_6555916] using wordTrace_append hprefix tailTrace_6555916
  have hstable : (prefixWord ++ tailWord_6555916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555916).length < 2 ^ (prefixWord ++ tailWord_6555916).sum := by decide
  have hdescent : baseEnd_6555916 < baseStart_6555916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555919 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 4, 5]
def baseStart_6555919 : Nat := 118140960795 + 6555919 * 2 ^ 59
def prefixEnd_6555919 : Nat := 4983230072969 + 3 ^ 40 * 6555919 * 2
def baseEnd_6555919 : Nat := 1122112526314480223487461

theorem tailTrace_6555919 : CollatzResearch.WordTrace tailWord_6555919 prefixEnd_6555919 1122112526314480223487461 := by
  unfold tailWord_6555919
  simp only [CollatzResearch.WordTrace]
  refine ⟨239114009936032599669478811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159409339957355066446319207 239114009936032599669478811)
  ·
    refine ⟨358671014904048899504218217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239114009936032599669478811 358671014904048899504218217)
    ·
      refine ⟨269003261178036674628163663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358671014904048899504218217 269003261178036674628163663)
      ·
        refine ⟨403504891767055011942245495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269003261178036674628163663 403504891767055011942245495)
        ·
          refine ⟨605257337650582517913368243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403504891767055011942245495 605257337650582517913368243)
          ·
            refine ⟨907886006475873776870052365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605257337650582517913368243 907886006475873776870052365)
            ·
              refine ⟨340457252428452666326269637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 907886006475873776870052365 340457252428452666326269637)
              ·
                refine ⟨63835734830334874936175557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340457252428452666326269637 63835734830334874936175557)
                ·
                  refine ⟨11969200280687789050532917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63835734830334874936175557 11969200280687789050532917)
                  ·
                    refine ⟨1122112526314480223487461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11969200280687789050532917 1122112526314480223487461)
                    ·
                      rfl

theorem cell23_6555919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_6555919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555919 prefixEnd_6555919 := by exact prefixLift 6555919
  have htrace : WordTrace (prefixWord ++ tailWord_6555919) baseStart_6555919 baseEnd_6555919 := by
    simpa [prefixWord, tailWord_6555919, baseEnd_6555919] using wordTrace_append hprefix tailTrace_6555919
  have hstable : (prefixWord ++ tailWord_6555919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555919).length < 2 ^ (prefixWord ++ tailWord_6555919).sum := by decide
  have hdescent : baseEnd_6555919 < baseStart_6555919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555936 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_6555936 : Nat := 118140960795 + 6555936 * 2 ^ 59
def prefixEnd_6555936 : Nat := 4983230072969 + 3 ^ 40 * 6555936 * 2
def baseEnd_6555936 : Nat := 1122115436038189034649935

theorem tailTrace_6555936 : CollatzResearch.WordTrace tailWord_6555936 prefixEnd_6555936 1122115436038189034649935 := by
  unfold tailWord_6555936
  simp only [CollatzResearch.WordTrace]
  refine ⟨119557314988485505786423831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159409753317980674381898441 119557314988485505786423831)
  ·
    refine ⟨179335972482728258679635747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119557314988485505786423831 179335972482728258679635747)
    ·
      refine ⟨269003958724092388019453621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179335972482728258679635747 269003958724092388019453621)
      ·
        refine ⟨25219121130383661376823777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269003958724092388019453621 25219121130383661376823777)
        ·
          refine ⟨18914340847787746032617833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25219121130383661376823777 18914340847787746032617833)
          ·
            refine ⟨14185755635840809524463375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18914340847787746032617833 14185755635840809524463375)
            ·
              refine ⟨21278633453761214286695063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185755635840809524463375 21278633453761214286695063)
              ·
                refine ⟨31917950180641821430042595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278633453761214286695063 31917950180641821430042595)
                ·
                  refine ⟨47876925270962732145063893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31917950180641821430042595 47876925270962732145063893)
                  ·
                    refine ⟨1122115436038189034649935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47876925270962732145063893 1122115436038189034649935)
                    ·
                      rfl

theorem cell23_6555936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_6555936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555936 prefixEnd_6555936 := by exact prefixLift 6555936
  have htrace : WordTrace (prefixWord ++ tailWord_6555936) baseStart_6555936 baseEnd_6555936 := by
    simpa [prefixWord, tailWord_6555936, baseEnd_6555936] using wordTrace_append hprefix tailTrace_6555936
  have hstable : (prefixWord ++ tailWord_6555936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555936).length < 2 ^ (prefixWord ++ tailWord_6555936).sum := by decide
  have hdescent : baseEnd_6555936 < baseStart_6555936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555959 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_6555959 : Nat := 118140960795 + 6555959 * 2 ^ 59
def prefixEnd_6555959 : Nat := 4983230072969 + 3 ^ 40 * 6555959 * 2
def baseEnd_6555959 : Nat := 3366358118169620513962199

theorem tailTrace_6555959 : CollatzResearch.WordTrace tailWord_6555959 prefixEnd_6555959 3366358118169620513962199 := by
  unfold tailWord_6555959
  simp only [CollatzResearch.WordTrace]
  refine ⟨239115468855887686500934931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159410312570591791000623287 239115468855887686500934931)
  ·
    refine ⟨358673203283831529751402397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239115468855887686500934931 358673203283831529751402397)
    ·
      refine ⟨134502451231436823656775899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358673203283831529751402397 134502451231436823656775899)
      ·
        refine ⟨201753676847155235485163849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134502451231436823656775899 201753676847155235485163849)
        ·
          refine ⟨151315257635366426613872887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201753676847155235485163849 151315257635366426613872887)
          ·
            refine ⟨226972886453049639920809331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151315257635366426613872887 226972886453049639920809331)
            ·
              refine ⟨340459329679574459881213997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226972886453049639920809331 340459329679574459881213997)
              ·
                refine ⟨127672248629840422455455249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340459329679574459881213997 127672248629840422455455249)
                ·
                  refine ⟨95754186472380316841591437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127672248629840422455455249 95754186472380316841591437)
                  ·
                    refine ⟨35907819927142618815596789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95754186472380316841591437 35907819927142618815596789)
                    ·
                      refine ⟨3366358118169620513962199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35907819927142618815596789 3366358118169620513962199)
                      ·
                        rfl

theorem cell23_6555959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_6555959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555959 prefixEnd_6555959 := by exact prefixLift 6555959
  have htrace : WordTrace (prefixWord ++ tailWord_6555959) baseStart_6555959 baseEnd_6555959 := by
    simpa [prefixWord, tailWord_6555959, baseEnd_6555959] using wordTrace_append hprefix tailTrace_6555959
  have hstable : (prefixWord ++ tailWord_6555959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555959).length < 2 ^ (prefixWord ++ tailWord_6555959).sum := by decide
  have hdescent : baseEnd_6555959 < baseStart_6555959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555976 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_6555976 : Nat := 118140960795 + 6555976 * 2 ^ 59
def prefixEnd_6555976 : Nat := 4983230072969 + 3 ^ 40 * 6555976 * 2
def baseEnd_6555976 : Nat := 3366366847340746947449621

theorem tailTrace_6555976 : CollatzResearch.WordTrace tailWord_6555976 prefixEnd_6555976 3366366847340746947449621 := by
  unfold tailWord_6555976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119558044448413049202151891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159410725931217398936202521 119558044448413049202151891)
  ·
    refine ⟨179337066672619573803227837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119558044448413049202151891 179337066672619573803227837)
    ·
      refine ⟨67251400002232340176210439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179337066672619573803227837 67251400002232340176210439)
      ·
        refine ⟨100877100003348510264315659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67251400002232340176210439 100877100003348510264315659)
        ·
          refine ⟨151315650005022765396473489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100877100003348510264315659 151315650005022765396473489)
          ·
            refine ⟨113486737503767074047355117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151315650005022765396473489 113486737503767074047355117)
            ·
              refine ⟨42557526563912652767758169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113486737503767074047355117 42557526563912652767758169)
              ·
                refine ⟨31918144922934489575818627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42557526563912652767758169 31918144922934489575818627)
                ·
                  refine ⟨47877217384401734363727941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31918144922934489575818627 47877217384401734363727941)
                  ·
                    refine ⟨8976978259575325193198989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47877217384401734363727941 8976978259575325193198989)
                    ·
                      refine ⟨3366366847340746947449621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8976978259575325193198989 3366366847340746947449621)
                      ·
                        rfl

theorem cell23_6555976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_6555976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555976 prefixEnd_6555976 := by exact prefixLift 6555976
  have htrace : WordTrace (prefixWord ++ tailWord_6555976) baseStart_6555976 baseEnd_6555976 := by
    simpa [prefixWord, tailWord_6555976, baseEnd_6555976] using wordTrace_append hprefix tailTrace_6555976
  have hstable : (prefixWord ++ tailWord_6555976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555976).length < 2 ^ (prefixWord ++ tailWord_6555976).sum := by decide
  have hdescent : baseEnd_6555976 < baseStart_6555976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556010 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6556010 : Nat := 118140960795 + 6556010 * 2 ^ 59
def prefixEnd_6556010 : Nat := 4983230072969 + 3 ^ 40 * 6556010 * 2
def baseEnd_6556010 : Nat := 3366384305682999814424465

theorem tailTrace_6556010 : CollatzResearch.WordTrace tailWord_6556010 prefixEnd_6556010 3366384305682999814424465 := by
  unfold tailWord_6556010
  simp only [CollatzResearch.WordTrace]
  refine ⟨59779332244675730552760371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159411552652468614807360989 59779332244675730552760371)
  ·
    refine ⟨89668998367013595829140557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59779332244675730552760371 89668998367013595829140557)
    ·
      refine ⟨33625874387630098435927709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89668998367013595829140557 33625874387630098435927709)
      ·
        refine ⟨12609702895361286913472891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33625874387630098435927709 12609702895361286913472891)
        ·
          refine ⟨18914554343041930370209337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12609702895361286913472891 18914554343041930370209337)
          ·
            refine ⟨14185915757281447777657003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18914554343041930370209337 14185915757281447777657003)
            ·
              refine ⟨21278873635922171666485505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185915757281447777657003 21278873635922171666485505)
              ·
                refine ⟨15959155226941628749864129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21278873635922171666485505 15959155226941628749864129)
                ·
                  refine ⟨11969366420206221562398097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15959155226941628749864129 11969366420206221562398097)
                  ·
                    refine ⟨8977024815154666171798573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11969366420206221562398097 8977024815154666171798573)
                    ·
                      refine ⟨3366384305682999814424465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8977024815154666171798573 3366384305682999814424465)
                      ·
                        rfl

theorem cell23_6556010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6556010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556010 prefixEnd_6556010 := by exact prefixLift 6556010
  have htrace : WordTrace (prefixWord ++ tailWord_6556010) baseStart_6556010 baseEnd_6556010 := by
    simpa [prefixWord, tailWord_6556010, baseEnd_6556010] using wordTrace_append hprefix tailTrace_6556010
  have hstable : (prefixWord ++ tailWord_6556010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556010).length < 2 ^ (prefixWord ++ tailWord_6556010).sum := by decide
  have hdescent : baseEnd_6556010 < baseStart_6556010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556023 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_6556023 : Nat := 118140960795 + 6556023 * 2 ^ 59
def prefixEnd_6556023 : Nat := 4983230072969 + 3 ^ 40 * 6556023 * 2
def baseEnd_6556023 : Nat := 3366390980931508263561905

theorem tailTrace_6556023 : CollatzResearch.WordTrace tailWord_6556023 prefixEnd_6556023 3366390980931508263561905 := by
  unfold tailWord_6556023
  simp only [CollatzResearch.WordTrace]
  refine ⟨239117803127655825431264723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159411868751770550287509815 239117803127655825431264723)
  ·
    refine ⟨358676704691483738146897085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239117803127655825431264723 358676704691483738146897085)
    ·
      refine ⟨134503764259306401805086407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358676704691483738146897085 134503764259306401805086407)
      ·
        refine ⟨201755646388959602707629611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134503764259306401805086407 201755646388959602707629611)
        ·
          refine ⟨302633469583439404061444417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201755646388959602707629611 302633469583439404061444417)
          ·
            refine ⟨226975102187579553046083313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302633469583439404061444417 226975102187579553046083313)
            ·
              refine ⟨170231326640684664784562485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226975102187579553046083313 170231326640684664784562485)
              ·
                refine ⟨15959186872564187323552733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170231326640684664784562485 15959186872564187323552733)
                ·
                  refine ⟨5984695077211570246332275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15959186872564187323552733 5984695077211570246332275)
                  ·
                    refine ⟨8977042615817355369498413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5984695077211570246332275 8977042615817355369498413)
                    ·
                      refine ⟨3366390980931508263561905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8977042615817355369498413 3366390980931508263561905)
                      ·
                        rfl

theorem cell23_6556023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_6556023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556023 prefixEnd_6556023 := by exact prefixLift 6556023
  have htrace : WordTrace (prefixWord ++ tailWord_6556023) baseStart_6556023 baseEnd_6556023 := by
    simpa [prefixWord, tailWord_6556023, baseEnd_6556023] using wordTrace_append hprefix tailTrace_6556023
  have hstable : (prefixWord ++ tailWord_6556023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556023).length < 2 ^ (prefixWord ++ tailWord_6556023).sum := by decide
  have hdescent : baseEnd_6556023 < baseStart_6556023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556043 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 1, 5]
def baseStart_6556043 : Nat := 118140960795 + 6556043 * 2 ^ 59
def prefixEnd_6556043 : Nat := 4983230072969 + 3 ^ 40 * 6556043 * 2
def baseEnd_6556043 : Nat := 1122133750181532728437271

theorem tailTrace_6556043 : CollatzResearch.WordTrace tailWord_6556043 prefixEnd_6556043 1122133750181532728437271 := by
  unfold tailWord_6556043
  simp only [CollatzResearch.WordTrace]
  refine ⟨239118532587583368846992783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159412355058388912564661855 239118532587583368846992783)
  ·
    refine ⟨358677798881375053270489175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239118532587583368846992783 358677798881375053270489175)
    ·
      refine ⟨538016698322062579905733763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358677798881375053270489175 538016698322062579905733763)
      ·
        refine ⟨807025047483093869858600645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538016698322062579905733763 807025047483093869858600645)
        ·
          refine ⟨151317196403080100598487621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 807025047483093869858600645 151317196403080100598487621)
          ·
            refine ⟨28371974325577518862216429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151317196403080100598487621 28371974325577518862216429)
            ·
              refine ⟨10639490372091569573331161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28371974325577518862216429 10639490372091569573331161)
              ·
                refine ⟨7979617779068677179998371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10639490372091569573331161 7979617779068677179998371)
                ·
                  refine ⟨11969426668603015769997557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7979617779068677179998371 11969426668603015769997557)
                  ·
                    refine ⟨1122133750181532728437271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11969426668603015769997557 1122133750181532728437271)
                    ·
                      rfl

theorem cell23_6556043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 5].length) (baseStart_6556043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556043 prefixEnd_6556043 := by exact prefixLift 6556043
  have htrace : WordTrace (prefixWord ++ tailWord_6556043) baseStart_6556043 baseEnd_6556043 := by
    simpa [prefixWord, tailWord_6556043, baseEnd_6556043] using wordTrace_append hprefix tailTrace_6556043
  have hstable : (prefixWord ++ tailWord_6556043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556043).length < 2 ^ (prefixWord ++ tailWord_6556043).sum := by decide
  have hdescent : baseEnd_6556043 < baseStart_6556043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556076 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_6556076 : Nat := 118140960795 + 6556076 * 2 ^ 59
def prefixEnd_6556076 : Nat := 4983230072969 + 3 ^ 40 * 6556076 * 2
def baseEnd_6556076 : Nat := 3366418195406196556199161

theorem tailTrace_6556076 : CollatzResearch.WordTrace tailWord_6556076 prefixEnd_6556076 3366418195406196556199161 := by
  unfold tailWord_6556076
  simp only [CollatzResearch.WordTrace]
  refine ⟨119559868098231907741472041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159413157464309210321962721 119559868098231907741472041)
  ·
    refine ⟨89669901073673930806104031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119559868098231907741472041 89669901073673930806104031)
    ·
      refine ⟨134504851610510896209156047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89669901073673930806104031 134504851610510896209156047)
      ·
        refine ⟨201757277415766344313734071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134504851610510896209156047 201757277415766344313734071)
        ·
          refine ⟨302635916123649516470601107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201757277415766344313734071 302635916123649516470601107)
          ·
            refine ⟨453953874185474274705901661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302635916123649516470601107 453953874185474274705901661)
            ·
              refine ⟨170232702819552853014713123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453953874185474274705901661 170232702819552853014713123)
              ·
                refine ⟨255349054229329279522069685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170232702819552853014713123 255349054229329279522069685)
                ·
                  refine ⟨23938973833999619955194033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255349054229329279522069685 23938973833999619955194033)
                  ·
                    refine ⟨17954230375499714966395525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23938973833999619955194033 17954230375499714966395525)
                    ·
                      refine ⟨3366418195406196556199161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17954230375499714966395525 3366418195406196556199161)
                      ·
                        rfl

theorem cell23_6556076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_6556076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556076 prefixEnd_6556076 := by exact prefixLift 6556076
  have htrace : WordTrace (prefixWord ++ tailWord_6556076) baseStart_6556076 baseEnd_6556076 := by
    simpa [prefixWord, tailWord_6556076, baseEnd_6556076] using wordTrace_append hprefix tailTrace_6556076
  have hstable : (prefixWord ++ tailWord_6556076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556076).length < 2 ^ (prefixWord ++ tailWord_6556076).sum := by decide
  have hdescent : baseEnd_6556076 < baseStart_6556076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556093 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_6556093 : Nat := 118140960795 + 6556093 * 2 ^ 59
def prefixEnd_6556093 : Nat := 4983230072969 + 3 ^ 40 * 6556093 * 2
def baseEnd_6556093 : Nat := 3366426924577322989686583

theorem tailTrace_6556093 : CollatzResearch.WordTrace tailWord_6556093 prefixEnd_6556093 3366426924577322989686583 := by
  unfold tailWord_6556093
  simp only [CollatzResearch.WordTrace]
  refine ⟨239120356237402227386312933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159413570824934818257541955 239120356237402227386312933)
  ·
    refine ⟨44835066794512917634933675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239120356237402227386312933 44835066794512917634933675)
    ·
      refine ⟨67252600191769376452400513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44835066794512917634933675 67252600191769376452400513)
      ·
        refine ⟨50439450143827032339300385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67252600191769376452400513 50439450143827032339300385)
        ·
          refine ⟨37829587607870274254475289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50439450143827032339300385 37829587607870274254475289)
          ·
            refine ⟨28372190705902705690856467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37829587607870274254475289 28372190705902705690856467)
            ·
              refine ⟨42558286058854058536284701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28372190705902705690856467 42558286058854058536284701)
              ·
                refine ⟨15959357272070271951106763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42558286058854058536284701 15959357272070271951106763)
                ·
                  refine ⟨23939035908105407926660145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15959357272070271951106763 23939035908105407926660145)
                  ·
                    refine ⟨17954276931079055944995109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23939035908105407926660145 17954276931079055944995109)
                    ·
                      refine ⟨3366426924577322989686583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17954276931079055944995109 3366426924577322989686583)
                      ·
                        rfl

theorem cell23_6556093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_6556093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556093 prefixEnd_6556093 := by exact prefixLift 6556093
  have htrace : WordTrace (prefixWord ++ tailWord_6556093) baseStart_6556093 baseEnd_6556093 := by
    simpa [prefixWord, tailWord_6556093, baseEnd_6556093] using wordTrace_append hprefix tailTrace_6556093
  have hstable : (prefixWord ++ tailWord_6556093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556093).length < 2 ^ (prefixWord ++ tailWord_6556093).sum := by decide
  have hdescent : baseEnd_6556093 < baseStart_6556093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556103 : List Nat := [1, 1, 4, 1, 1, 5, 3, 7]
def baseStart_6556103 : Nat := 118140960795 + 6556103 * 2 ^ 59
def prefixEnd_6556103 : Nat := 4983230072969 + 3 ^ 40 * 6556103 * 2
def baseEnd_6556103 : Nat := 124682668866069183354131

theorem tailTrace_6556103 : CollatzResearch.WordTrace tailWord_6556103 prefixEnd_6556103 124682668866069183354131 := by
  unfold tailWord_6556103
  simp only [CollatzResearch.WordTrace]
  refine ⟨239120720967365999094176963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159413813978243999396117975 239120720967365999094176963)
  ·
    refine ⟨358681081451048998641265445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239120720967365999094176963 358681081451048998641265445)
    ·
      refine ⟨67252702772071687245237271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358681081451048998641265445 67252702772071687245237271)
      ·
        refine ⟨100879054158107530867855907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67252702772071687245237271 100879054158107530867855907)
        ·
          refine ⟨151318581237161296301783861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100879054158107530867855907 151318581237161296301783861)
          ·
            refine ⟨14186116990983871528292237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151318581237161296301783861 14186116990983871528292237)
            ·
              refine ⟨5319793871618951823109589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14186116990983871528292237 5319793871618951823109589)
              ·
                refine ⟨124682668866069183354131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5319793871618951823109589 124682668866069183354131)
                ·
                  rfl

theorem cell23_6556103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 7].length) (baseStart_6556103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556103 prefixEnd_6556103 := by exact prefixLift 6556103
  have htrace : WordTrace (prefixWord ++ tailWord_6556103) baseStart_6556103 baseEnd_6556103 := by
    simpa [prefixWord, tailWord_6556103, baseEnd_6556103] using wordTrace_append hprefix tailTrace_6556103
  have hstable : (prefixWord ++ tailWord_6556103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556103).length < 2 ^ (prefixWord ++ tailWord_6556103).sum := by decide
  have hdescent : baseEnd_6556103 < baseStart_6556103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556117 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6556117 : Nat := 118140960795 + 6556117 * 2 ^ 59
def prefixEnd_6556117 : Nat := 4983230072969 + 3 ^ 40 * 6556117 * 2
def baseEnd_6556117 : Nat := 3366439248113030895786473

theorem tailTrace_6556117 : CollatzResearch.WordTrace tailWord_6556117 prefixEnd_6556117 3366439248113030895786473 := by
  unfold tailWord_6556117
  simp only [CollatzResearch.WordTrace]
  refine ⟨239121231589315279485186605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159414154392876852990124403 239121231589315279485186605)
  ·
    refine ⟨89670461845993229806944977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239121231589315279485186605 89670461845993229806944977)
    ·
      refine ⟨67252846384494922355208733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89670461845993229806944977 67252846384494922355208733)
      ·
        refine ⟨25219817394185595883203275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67252846384494922355208733 25219817394185595883203275)
        ·
          refine ⟨37829726091278393824804913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25219817394185595883203275 37829726091278393824804913)
          ·
            refine ⟨28372294568458795368603685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37829726091278393824804913 28372294568458795368603685)
            ·
              refine ⟨5319805231586024131613191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28372294568458795368603685 5319805231586024131613191)
              ·
                refine ⟨7979707847379036197419787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319805231586024131613191 7979707847379036197419787)
                ·
                  refine ⟨11969561771068554296129681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7979707847379036197419787 11969561771068554296129681)
                  ·
                    refine ⟨8977171328301415722097261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11969561771068554296129681 8977171328301415722097261)
                    ·
                      refine ⟨3366439248113030895786473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8977171328301415722097261 3366439248113030895786473)
                      ·
                        rfl

theorem cell23_6556117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6556117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556117 prefixEnd_6556117 := by exact prefixLift 6556117
  have htrace : WordTrace (prefixWord ++ tailWord_6556117) baseStart_6556117 baseEnd_6556117 := by
    simpa [prefixWord, tailWord_6556117, baseEnd_6556117] using wordTrace_append hprefix tailTrace_6556117
  have hstable : (prefixWord ++ tailWord_6556117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556117).length < 2 ^ (prefixWord ++ tailWord_6556117).sum := by decide
  have hdescent : baseEnd_6556117 < baseStart_6556117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556147 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 2, 1, 3]
def baseStart_6556147 : Nat := 118140960795 + 6556147 * 2 ^ 59
def prefixEnd_6556147 : Nat := 4983230072969 + 3 ^ 40 * 6556147 * 2
def baseEnd_6556147 : Nat := 3366454652532665778411335

theorem tailTrace_6556147 : CollatzResearch.WordTrace tailWord_6556147 prefixEnd_6556147 3366454652532665778411335 := by
  unfold tailWord_6556147
  simp only [CollatzResearch.WordTrace]
  refine ⟨239122325779206594608778695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159414883852804396405852463 239122325779206594608778695)
  ·
    refine ⟨358683488668809891913168043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239122325779206594608778695 358683488668809891913168043)
    ·
      refine ⟨538025233003214837869752065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358683488668809891913168043 538025233003214837869752065)
      ·
        refine ⟨403518924752411128402314049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538025233003214837869752065 403518924752411128402314049)
        ·
          refine ⟨302639193564308346301735537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403518924752411128402314049 302639193564308346301735537)
          ·
            refine ⟨226979395173231259726301653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302639193564308346301735537 226979395173231259726301653)
            ·
              refine ⟨5319829574372607649835195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 226979395173231259726301653 5319829574372607649835195)
              ·
                refine ⟨7979744361558911474752793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319829574372607649835195 7979744361558911474752793)
                ·
                  refine ⟨5984808271169183606064595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7979744361558911474752793 5984808271169183606064595)
                  ·
                    refine ⟨8977212406753775409096893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5984808271169183606064595 8977212406753775409096893)
                    ·
                      refine ⟨3366454652532665778411335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8977212406753775409096893 3366454652532665778411335)
                      ·
                        rfl

theorem cell23_6556147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 1, 3].length) (baseStart_6556147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556147 prefixEnd_6556147 := by exact prefixLift 6556147
  have htrace : WordTrace (prefixWord ++ tailWord_6556147) baseStart_6556147 baseEnd_6556147 := by
    simpa [prefixWord, tailWord_6556147, baseEnd_6556147] using wordTrace_append hprefix tailTrace_6556147
  have hstable : (prefixWord ++ tailWord_6556147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556147).length < 2 ^ (prefixWord ++ tailWord_6556147).sum := by decide
  have hdescent : baseEnd_6556147 < baseStart_6556147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556157 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_6556157 : Nat := 118140960795 + 6556157 * 2 ^ 59
def prefixEnd_6556157 : Nat := 4983230072969 + 3 ^ 40 * 6556157 * 2
def baseEnd_6556157 : Nat := 3366459787339210739286289

theorem tailTrace_6556157 : CollatzResearch.WordTrace tailWord_6556157 prefixEnd_6556157 3366459787339210739286289 := by
  unfold tailWord_6556157
  simp only [CollatzResearch.WordTrace]
  refine ⟨239122690509170366316642725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159415127006113577544428483 239122690509170366316642725)
  ·
    refine ⟨44835504470469443684370511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239122690509170366316642725 44835504470469443684370511)
    ·
      refine ⟨67253256705704165526555767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44835504470469443684370511 67253256705704165526555767)
      ·
        refine ⟨100879885058556248289833651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67253256705704165526555767 100879885058556248289833651)
        ·
          refine ⟨151319827587834372434750477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100879885058556248289833651 151319827587834372434750477)
          ·
            refine ⟨56744935345437889663031429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151319827587834372434750477 56744935345437889663031429)
            ·
              refine ⟨10639675377269604311818393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56744935345437889663031429 10639675377269604311818393)
              ·
                refine ⟨7979756532952203233863795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10639675377269604311818393 7979756532952203233863795)
                ·
                  refine ⟨11969634799428304850795693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7979756532952203233863795 11969634799428304850795693)
                  ·
                    refine ⟨4488613049785614319048385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11969634799428304850795693 4488613049785614319048385)
                    ·
                      refine ⟨3366459787339210739286289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488613049785614319048385 3366459787339210739286289)
                      ·
                        rfl

theorem cell23_6556157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_6556157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556157 prefixEnd_6556157 := by exact prefixLift 6556157
  have htrace : WordTrace (prefixWord ++ tailWord_6556157) baseStart_6556157 baseEnd_6556157 := by
    simpa [prefixWord, tailWord_6556157, baseEnd_6556157] using wordTrace_append hprefix tailTrace_6556157
  have hstable : (prefixWord ++ tailWord_6556157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556157).length < 2 ^ (prefixWord ++ tailWord_6556157).sum := by decide
  have hdescent : baseEnd_6556157 < baseStart_6556157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556170 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_6556170 : Nat := 118140960795 + 6556170 * 2 ^ 59
def prefixEnd_6556170 : Nat := 4983230072969 + 3 ^ 40 * 6556170 * 2
def baseEnd_6556170 : Nat := 3366466462587719188423729

theorem tailTrace_6556170 : CollatzResearch.WordTrace tailWord_6556170 prefixEnd_6556170 3366466462587719188423729 := by
  unfold tailWord_6556170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59780791164530817384216491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159415443105415513024577309 59780791164530817384216491)
  ·
    refine ⟨89671186746796226076324737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59780791164530817384216491 89671186746796226076324737)
    ·
      refine ⟨67253390060097169557243553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89671186746796226076324737 67253390060097169557243553)
      ·
        refine ⟨50440042545072877167932665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67253390060097169557243553 50440042545072877167932665)
        ·
          refine ⟨37830031908804657875949499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50440042545072877167932665 37830031908804657875949499)
          ·
            refine ⟨56745047863206986813924249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37830031908804657875949499 56745047863206986813924249)
            ·
              refine ⟨42558785897405240110443187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56745047863206986813924249 42558785897405240110443187)
              ·
                refine ⟨63838178846107860165664781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42558785897405240110443187 63838178846107860165664781)
                ·
                  refine ⟨23939317067290447562124293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63838178846107860165664781 23939317067290447562124293)
                  ·
                    refine ⟨4488621950116958917898305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23939317067290447562124293 4488621950116958917898305)
                    ·
                      refine ⟨3366466462587719188423729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488621950116958917898305 3366466462587719188423729)
                      ·
                        rfl

theorem cell23_6556170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_6556170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556170 prefixEnd_6556170 := by exact prefixLift 6556170
  have htrace : WordTrace (prefixWord ++ tailWord_6556170) baseStart_6556170 baseEnd_6556170 := by
    simpa [prefixWord, tailWord_6556170, baseEnd_6556170] using wordTrace_append hprefix tailTrace_6556170
  have hstable : (prefixWord ++ tailWord_6556170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556170).length < 2 ^ (prefixWord ++ tailWord_6556170).sum := by decide
  have hdescent : baseEnd_6556170 < baseStart_6556170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556203 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3]
def baseStart_6556203 : Nat := 118140960795 + 6556203 * 2 ^ 59
def prefixEnd_6556203 : Nat := 4983230072969 + 3 ^ 40 * 6556203 * 2
def baseEnd_6556203 : Nat := 3366483407449317559311077

theorem tailTrace_6556203 : CollatzResearch.WordTrace tailWord_6556203 prefixEnd_6556203 3366483407449317559311077 := by
  unfold tailWord_6556203
  simp only [CollatzResearch.WordTrace]
  refine ⟨239124368267003716172817263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159416245511335810781878175 239124368267003716172817263)
  ·
    refine ⟨358686552400505574259225895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239124368267003716172817263 358686552400505574259225895)
    ·
      refine ⟨538029828600758361388838843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358686552400505574259225895 538029828600758361388838843)
      ·
        refine ⟨807044742901137542083258265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538029828600758361388838843 807044742901137542083258265)
        ·
          refine ⟨605283557175853156562443699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807044742901137542083258265 605283557175853156562443699)
          ·
            refine ⟨907925335763779734843665549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605283557175853156562443699 907925335763779734843665549)
            ·
              refine ⟨340472000911417400566374581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 907925335763779734843665549 340472000911417400566374581)
              ·
                refine ⟨31919250085445381303097617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340472000911417400566374581 31919250085445381303097617)
                ·
                  refine ⟨23939437564084035977323213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31919250085445381303097617 23939437564084035977323213)
                  ·
                    refine ⟨8977289086531513491496205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23939437564084035977323213 8977289086531513491496205)
                    ·
                      refine ⟨3366483407449317559311077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8977289086531513491496205 3366483407449317559311077)
                      ·
                        rfl

theorem cell23_6556203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3].length) (baseStart_6556203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556203 prefixEnd_6556203 := by exact prefixLift 6556203
  have htrace : WordTrace (prefixWord ++ tailWord_6556203) baseStart_6556203 baseEnd_6556203 := by
    simpa [prefixWord, tailWord_6556203, baseEnd_6556203] using wordTrace_append hprefix tailTrace_6556203
  have hstable : (prefixWord ++ tailWord_6556203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556203).length < 2 ^ (prefixWord ++ tailWord_6556203).sum := by decide
  have hdescent : baseEnd_6556203 < baseStart_6556203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556244 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 5]
def baseStart_6556244 : Nat := 118140960795 + 6556244 * 2 ^ 59
def prefixEnd_6556244 : Nat := 4983230072969 + 3 ^ 40 * 6556244 * 2
def baseEnd_6556244 : Nat := 374056051128461322099821

theorem tailTrace_6556244 : CollatzResearch.WordTrace tailWord_6556244 prefixEnd_6556244 374056051128461322099821 := by
  unfold tailWord_6556244
  simp only [CollatzResearch.WordTrace]
  refine ⟨119562931829927590087529893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159417242439903453450039857 119562931829927590087529893)
  ·
    refine ⟨22418049718111423141411855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119562931829927590087529893 22418049718111423141411855)
    ·
      refine ⟨33627074577167134712117783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22418049718111423141411855 33627074577167134712117783)
      ·
        refine ⟨50440611865750702068176675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33627074577167134712117783 50440611865750702068176675)
        ·
          refine ⟨75660917798626053102265013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50440611865750702068176675 75660917798626053102265013)
          ·
            refine ⟨7093211043621192478337345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75660917798626053102265013 7093211043621192478337345)
            ·
              refine ⟨5319908282715894358753009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093211043621192478337345 5319908282715894358753009)
              ·
                refine ⟨3989931212036920769064757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319908282715894358753009 3989931212036920769064757)
                ·
                  refine ⟨374056051128461322099821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3989931212036920769064757 374056051128461322099821)
                  ·
                    rfl

theorem cell23_6556244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_6556244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556244 prefixEnd_6556244 := by exact prefixLift 6556244
  have htrace : WordTrace (prefixWord ++ tailWord_6556244) baseStart_6556244 baseEnd_6556244 := by
    simpa [prefixWord, tailWord_6556244, baseEnd_6556244] using wordTrace_append hprefix tailTrace_6556244
  have hstable : (prefixWord ++ tailWord_6556244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556244).length < 2 ^ (prefixWord ++ tailWord_6556244).sum := by decide
  have hdescent : baseEnd_6556244 < baseStart_6556244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556274 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_6556274 : Nat := 118140960795 + 6556274 * 2 ^ 59
def prefixEnd_6556274 : Nat := 4983230072969 + 3 ^ 40 * 6556274 * 2
def baseEnd_6556274 : Nat := 1122173288191928927174417

theorem tailTrace_6556274 : CollatzResearch.WordTrace tailWord_6556274 prefixEnd_6556274 1122173288191928927174417 := by
  unfold tailWord_6556274
  simp only [CollatzResearch.WordTrace]
  refine ⟨59781739462436623824662969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159417971899830996865767917 59781739462436623824662969)
  ·
    refine ⟨44836304596827467868497227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59781739462436623824662969 44836304596827467868497227)
    ·
      refine ⟨67254456895241201802745841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44836304596827467868497227 67254456895241201802745841)
      ·
        refine ⟨50440842671430901352059381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67254456895241201802745841 50440842671430901352059381)
        ·
          refine ⟨4728829000446647001755567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50440842671430901352059381 4728829000446647001755567)
          ·
            refine ⟨7093243500669970502633351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728829000446647001755567 7093243500669970502633351)
            ·
              refine ⟨10639865251004955753950027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093243500669970502633351 10639865251004955753950027)
              ·
                refine ⟨15959797876507433630925041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10639865251004955753950027 15959797876507433630925041)
                ·
                  refine ⟨11969848407380575223193781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15959797876507433630925041 11969848407380575223193781)
                  ·
                    refine ⟨1122173288191928927174417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11969848407380575223193781 1122173288191928927174417)
                    ·
                      rfl

theorem cell23_6556274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_6556274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556274 prefixEnd_6556274 := by exact prefixLift 6556274
  have htrace : WordTrace (prefixWord ++ tailWord_6556274) baseStart_6556274 baseEnd_6556274 := by
    simpa [prefixWord, tailWord_6556274, baseEnd_6556274] using wordTrace_append hprefix tailTrace_6556274
  have hstable : (prefixWord ++ tailWord_6556274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556274).length < 2 ^ (prefixWord ++ tailWord_6556274).sum := by decide
  have hdescent : baseEnd_6556274 < baseStart_6556274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556277 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6556277 : Nat := 118140960795 + 6556277 * 2 ^ 59
def prefixEnd_6556277 : Nat := 4983230072969 + 3 ^ 40 * 6556277 * 2
def baseEnd_6556277 : Nat := 3366521405017750269785737

theorem tailTrace_6556277 : CollatzResearch.WordTrace tailWord_6556277 prefixEnd_6556277 3366521405017750269785737 := by
  unfold tailWord_6556277
  simp only [CollatzResearch.WordTrace]
  refine ⟨239127067268735626811011085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159418044845823751207340723 239127067268735626811011085)
  ·
    refine ⟨89672650225775860054129157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239127067268735626811011085 89672650225775860054129157)
    ·
      refine ⟨16813621917332973760149217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89672650225775860054129157 16813621917332973760149217)
      ·
        refine ⟨12610216437999730320111913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16813621917332973760149217 12610216437999730320111913)
        ·
          refine ⟨9457662328499797740083935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12610216437999730320111913 9457662328499797740083935)
          ·
            refine ⟨14186493492749696610125903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457662328499797740083935 14186493492749696610125903)
            ·
              refine ⟨21279740239124544915188855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14186493492749696610125903 21279740239124544915188855)
              ·
                refine ⟨31919610358686817372783283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21279740239124544915188855 31919610358686817372783283)
                ·
                  refine ⟨47879415538030226059174925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31919610358686817372783283 47879415538030226059174925)
                  ·
                    refine ⟨17954780826761334772190597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47879415538030226059174925 17954780826761334772190597)
                    ·
                      refine ⟨3366521405017750269785737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17954780826761334772190597 3366521405017750269785737)
                      ·
                        rfl

theorem cell23_6556277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6556277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556277 prefixEnd_6556277 := by exact prefixLift 6556277
  have htrace : WordTrace (prefixWord ++ tailWord_6556277) baseStart_6556277 baseEnd_6556277 := by
    simpa [prefixWord, tailWord_6556277, baseEnd_6556277] using wordTrace_append hprefix tailTrace_6556277
  have hstable : (prefixWord ++ tailWord_6556277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556277).length < 2 ^ (prefixWord ++ tailWord_6556277).sum := by decide
  have hdescent : baseEnd_6556277 < baseStart_6556277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556377 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_6556377 : Nat := 118140960795 + 6556377 * 2 ^ 59
def prefixEnd_6556377 : Nat := 4983230072969 + 3 ^ 40 * 6556377 * 2
def baseEnd_6556377 : Nat := 1122190917694399959511759

theorem tailTrace_6556377 : CollatzResearch.WordTrace tailWord_6556377 prefixEnd_6556377 1122190917694399959511759 := by
  unfold tailWord_6556377
  simp only [CollatzResearch.WordTrace]
  refine ⟨239130714568373343889651385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159420476378915562593100923 239130714568373343889651385)
  ·
    refine ⟨179348035926280007917238539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239130714568373343889651385 179348035926280007917238539)
    ·
      refine ⟨269022053889420011875857809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179348035926280007917238539 269022053889420011875857809)
      ·
        refine ⟨201766540417065008906893357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269022053889420011875857809 201766540417065008906893357)
        ·
          refine ⟨75662452656399378340085009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201766540417065008906893357 75662452656399378340085009)
          ·
            refine ⟨56746839492299533755063757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75662452656399378340085009 56746839492299533755063757)
            ·
              refine ⟨21280064809612325158148909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56746839492299533755063757 21280064809612325158148909)
              ·
                refine ⟨7980024303604621934305841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21280064809612325158148909 7980024303604621934305841)
                ·
                  refine ⟨5985018227703466450729381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7980024303604621934305841 5985018227703466450729381)
                  ·
                    refine ⟨1122190917694399959511759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985018227703466450729381 1122190917694399959511759)
                    ·
                      rfl

theorem cell23_6556377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_6556377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556377 prefixEnd_6556377 := by exact prefixLift 6556377
  have htrace : WordTrace (prefixWord ++ tailWord_6556377) baseStart_6556377 baseEnd_6556377 := by
    simpa [prefixWord, tailWord_6556377, baseEnd_6556377] using wordTrace_append hprefix tailTrace_6556377
  have hstable : (prefixWord ++ tailWord_6556377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556377).length < 2 ^ (prefixWord ++ tailWord_6556377).sum := by decide
  have hdescent : baseEnd_6556377 < baseStart_6556377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556397 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6556397 : Nat := 118140960795 + 6556397 * 2 ^ 59
def prefixEnd_6556397 : Nat := 4983230072969 + 3 ^ 40 * 6556397 * 2
def baseEnd_6556397 : Nat := 3366583022696289800285185

theorem tailTrace_6556397 : CollatzResearch.WordTrace tailWord_6556397 prefixEnd_6556397 3366583022696289800285185 := by
  unfold tailWord_6556397
  simp only [CollatzResearch.WordTrace]
  refine ⟨239131444028300887305379445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159420962685533924870252963 239131444028300887305379445)
  ·
    refine ⟨22418572877653208184879323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239131444028300887305379445 22418572877653208184879323)
    ·
      refine ⟨33627859316479812277318985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22418572877653208184879323 33627859316479812277318985)
      ·
        refine ⟨25220894487359859207989239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33627859316479812277318985 25220894487359859207989239)
        ·
          refine ⟨37831341731039788811983859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25220894487359859207989239 37831341731039788811983859)
          ·
            refine ⟨56747012596559683217975789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37831341731039788811983859 56747012596559683217975789)
            ·
              refine ⟨21280129723709881206740921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56747012596559683217975789 21280129723709881206740921)
              ·
                refine ⟨15960097292782410905055691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21280129723709881206740921 15960097292782410905055691)
                ·
                  refine ⟨23940145939173616357583537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15960097292782410905055691 23940145939173616357583537)
                  ·
                    refine ⟨17955109454380212268187653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23940145939173616357583537 17955109454380212268187653)
                    ·
                      refine ⟨3366583022696289800285185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17955109454380212268187653 3366583022696289800285185)
                      ·
                        rfl

theorem cell23_6556397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6556397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556397 prefixEnd_6556397 := by exact prefixLift 6556397
  have htrace : WordTrace (prefixWord ++ tailWord_6556397) baseStart_6556397 baseEnd_6556397 := by
    simpa [prefixWord, tailWord_6556397, baseEnd_6556397] using wordTrace_append hprefix tailTrace_6556397
  have hstable : (prefixWord ++ tailWord_6556397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556397).length < 2 ^ (prefixWord ++ tailWord_6556397).sum := by decide
  have hdescent : baseEnd_6556397 < baseStart_6556397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556401 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 1, 2, 2]
def baseStart_6556401 : Nat := 118140960795 + 6556401 * 2 ^ 59
def prefixEnd_6556401 : Nat := 4983230072969 + 3 ^ 40 * 6556401 * 2
def baseEnd_6556401 : Nat := 3366585076618907784635167

theorem tailTrace_6556401 : CollatzResearch.WordTrace tailWord_6556401 prefixEnd_6556401 3366585076618907784635167 := by
  unfold tailWord_6556401
  simp only [CollatzResearch.WordTrace]
  refine ⟨239131589920286395988525057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159421059946857597325683371 239131589920286395988525057)
  ·
    refine ⟨179348692440214796991393793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239131589920286395988525057 179348692440214796991393793)
    ·
      refine ⟨134511519330161097743545345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179348692440214796991393793 134511519330161097743545345)
      ·
        refine ⟨100883639497620823307659009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134511519330161097743545345 100883639497620823307659009)
        ·
          refine ⟨75662729623215617480744257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100883639497620823307659009 75662729623215617480744257)
          ·
            refine ⟨56747047217411713110558193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75662729623215617480744257 56747047217411713110558193)
            ·
              refine ⟨42560285413058784832918645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56747047217411713110558193 42560285413058784832918645)
              ·
                refine ⟨3990026757474261078086123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42560285413058784832918645 3990026757474261078086123)
                ·
                  refine ⟨5985040136211391617129185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990026757474261078086123 5985040136211391617129185)
                  ·
                    refine ⟨4488780102158543712846889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5985040136211391617129185 4488780102158543712846889)
                    ·
                      refine ⟨3366585076618907784635167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488780102158543712846889 3366585076618907784635167)
                      ·
                        rfl

theorem cell23_6556401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_6556401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556401 prefixEnd_6556401 := by exact prefixLift 6556401
  have htrace : WordTrace (prefixWord ++ tailWord_6556401) baseStart_6556401 baseEnd_6556401 := by
    simpa [prefixWord, tailWord_6556401, baseEnd_6556401] using wordTrace_append hprefix tailTrace_6556401
  have hstable : (prefixWord ++ tailWord_6556401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556401).length < 2 ^ (prefixWord ++ tailWord_6556401).sum := by decide
  have hdescent : baseEnd_6556401 < baseStart_6556401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556420 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_6556420 : Nat := 118140960795 + 6556420 * 2 ^ 59
def prefixEnd_6556420 : Nat := 4983230072969 + 3 ^ 40 * 6556420 * 2
def baseEnd_6556420 : Nat := 1122198277583781070099193

theorem tailTrace_6556420 : CollatzResearch.WordTrace tailWord_6556420 prefixEnd_6556420 1122198277583781070099193 := by
  unfold tailWord_6556420
  simp only [CollatzResearch.WordTrace]
  refine ⟨119566141453608781116733357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159421521938145041488977809 119566141453608781116733357)
  ·
    refine ⟨44837303045103292918775009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119566141453608781116733357 44837303045103292918775009)
    ·
      refine ⟨33627977283827469689081257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44837303045103292918775009 33627977283827469689081257)
      ·
        refine ⟨25220982962870602266810943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33627977283827469689081257 25220982962870602266810943)
        ·
          refine ⟨37831474444305903400216415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25220982962870602266810943 37831474444305903400216415)
          ·
            refine ⟨56747211666458855100324623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37831474444305903400216415 56747211666458855100324623)
            ·
              refine ⟨85120817499688282650486935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56747211666458855100324623 85120817499688282650486935)
              ·
                refine ⟨127681226249532423975730403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85120817499688282650486935 127681226249532423975730403)
                ·
                  refine ⟨191521839374298635963595605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127681226249532423975730403 191521839374298635963595605)
                  ·
                    refine ⟨1122198277583781070099193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 191521839374298635963595605 1122198277583781070099193)
                    ·
                      rfl

theorem cell23_6556420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_6556420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556420 prefixEnd_6556420 := by exact prefixLift 6556420
  have htrace : WordTrace (prefixWord ++ tailWord_6556420) baseStart_6556420 baseEnd_6556420 := by
    simpa [prefixWord, tailWord_6556420, baseEnd_6556420] using wordTrace_append hprefix tailTrace_6556420
  have hstable : (prefixWord ++ tailWord_6556420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556420).length < 2 ^ (prefixWord ++ tailWord_6556420).sum := by decide
  have hdescent : baseEnd_6556420 < baseStart_6556420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556430 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6556430 : Nat := 118140960795 + 6556430 * 2 ^ 59
def prefixEnd_6556430 : Nat := 4983230072969 + 3 ^ 40 * 6556430 * 2
def baseEnd_6556430 : Nat := 3366599967557888171172533

theorem tailTrace_6556430 : CollatzResearch.WordTrace tailWord_6556430 prefixEnd_6556430 3366599967557888171172533 := by
  unfold tailWord_6556430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891580954647666742666343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159421765091454222627553829 29891580954647666742666343)
  ·
    refine ⟨44837371431971500113999515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29891580954647666742666343 44837371431971500113999515)
    ·
      refine ⟨67256057147957250170999273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44837371431971500113999515 67256057147957250170999273)
      ·
        refine ⟨50442042860967937628249455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67256057147957250170999273 50442042860967937628249455)
        ·
          refine ⟨75663064291451906442374183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50442042860967937628249455 75663064291451906442374183)
          ·
            refine ⟨113494596437177859663561275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75663064291451906442374183 113494596437177859663561275)
            ·
              refine ⟨170241894655766789495341913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113494596437177859663561275 170241894655766789495341913)
              ·
                refine ⟨127681420991825092121506435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170241894655766789495341913 127681420991825092121506435)
                ·
                  refine ⟨191522131487737638182259653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127681420991825092121506435 191522131487737638182259653)
                  ·
                    refine ⟨35910399653950807159173685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191522131487737638182259653 35910399653950807159173685)
                    ·
                      refine ⟨3366599967557888171172533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35910399653950807159173685 3366599967557888171172533)
                      ·
                        rfl

theorem cell23_6556430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6556430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556430 prefixEnd_6556430 := by exact prefixLift 6556430
  have htrace : WordTrace (prefixWord ++ tailWord_6556430) baseStart_6556430 baseEnd_6556430 := by
    simpa [prefixWord, tailWord_6556430, baseEnd_6556430] using wordTrace_append hprefix tailTrace_6556430
  have hstable : (prefixWord ++ tailWord_6556430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556430).length < 2 ^ (prefixWord ++ tailWord_6556430).sum := by decide
  have hdescent : baseEnd_6556430 < baseStart_6556430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556440 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6556440 : Nat := 118140960795 + 6556440 * 2 ^ 59
def prefixEnd_6556440 : Nat := 4983230072969 + 3 ^ 40 * 6556440 * 2
def baseEnd_6556440 : Nat := 3366605102364433132047487

theorem tailTrace_6556440 : CollatzResearch.WordTrace tailWord_6556440 prefixEnd_6556440 3366605102364433132047487 := by
  unfold tailWord_6556440
  simp only [CollatzResearch.WordTrace]
  refine ⟨119566506183572552824597387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159422008244763403766129849 119566506183572552824597387)
  ·
    refine ⟨179349759275358829236896081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119566506183572552824597387 179349759275358829236896081)
    ·
      refine ⟨134512319456519121927672061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179349759275358829236896081 134512319456519121927672061)
      ·
        refine ⟨50442119796194670722877023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134512319456519121927672061 50442119796194670722877023)
        ·
          refine ⟨75663179694292006084315535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50442119796194670722877023 75663179694292006084315535)
          ·
            refine ⟨113494769541438009126473303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75663179694292006084315535 113494769541438009126473303)
            ·
              refine ⟨170242154312157013689709955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113494769541438009126473303 170242154312157013689709955)
              ·
                refine ⟨255363231468235520534564933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170242154312157013689709955 255363231468235520534564933)
                ·
                  refine ⟨47880605900294160100230925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255363231468235520534564933 47880605900294160100230925)
                  ·
                    refine ⟨17955227212610310037586597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47880605900294160100230925 17955227212610310037586597)
                    ·
                      refine ⟨3366605102364433132047487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17955227212610310037586597 3366605102364433132047487)
                      ·
                        rfl

theorem cell23_6556440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6556440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556440 prefixEnd_6556440 := by exact prefixLift 6556440
  have htrace : WordTrace (prefixWord ++ tailWord_6556440) baseStart_6556440 baseEnd_6556440 := by
    simpa [prefixWord, tailWord_6556440, baseEnd_6556440] using wordTrace_append hprefix tailTrace_6556440
  have hstable : (prefixWord ++ tailWord_6556440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556440).length < 2 ^ (prefixWord ++ tailWord_6556440).sum := by decide
  have hdescent : baseEnd_6556440 < baseStart_6556440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556444 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_6556444 : Nat := 118140960795 + 6556444 * 2 ^ 59
def prefixEnd_6556444 : Nat := 4983230072969 + 3 ^ 40 * 6556444 * 2
def baseEnd_6556444 : Nat := 3366607156287051116397469

theorem tailTrace_6556444 : CollatzResearch.WordTrace tailWord_6556444 prefixEnd_6556444 3366607156287051116397469 := by
  unfold tailWord_6556444
  simp only [CollatzResearch.WordTrace]
  refine ⟨119566579129565307166170193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159422105506087076221560257 119566579129565307166170193)
  ·
    refine ⟨89674934347173980374627645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119566579129565307166170193 89674934347173980374627645)
    ·
      refine ⟨33628100380190242640485367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89674934347173980374627645 33628100380190242640485367)
      ·
        refine ⟨50442150570285363960728051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33628100380190242640485367 50442150570285363960728051)
        ·
          refine ⟨75663225855428045941092077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50442150570285363960728051 75663225855428045941092077)
          ·
            refine ⟨28373709695785517227909529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75663225855428045941092077 28373709695785517227909529)
            ·
              refine ⟨21280282271839137920932147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28373709695785517227909529 21280282271839137920932147)
              ·
                refine ⟨31920423407758706881398221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21280282271839137920932147 31920423407758706881398221)
                ·
                  refine ⟨11970158777909515080524333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31920423407758706881398221 11970158777909515080524333)
                  ·
                    refine ⟨4488809541716068155196625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11970158777909515080524333 4488809541716068155196625)
                    ·
                      refine ⟨3366607156287051116397469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488809541716068155196625 3366607156287051116397469)
                      ·
                        rfl

theorem cell23_6556444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_6556444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556444 prefixEnd_6556444 := by exact prefixLift 6556444
  have htrace : WordTrace (prefixWord ++ tailWord_6556444) baseStart_6556444 baseEnd_6556444 := by
    simpa [prefixWord, tailWord_6556444, baseEnd_6556444] using wordTrace_append hprefix tailTrace_6556444
  have hstable : (prefixWord ++ tailWord_6556444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556444).length < 2 ^ (prefixWord ++ tailWord_6556444).sum := by decide
  have hdescent : baseEnd_6556444 < baseStart_6556444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556460 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_6556460 : Nat := 118140960795 + 6556460 * 2 ^ 59
def prefixEnd_6556460 : Nat := 4983230072969 + 3 ^ 40 * 6556460 * 2
def baseEnd_6556460 : Nat := 3366615371977523053797395

theorem tailTrace_6556460 : CollatzResearch.WordTrace tailWord_6556460 prefixEnd_6556460 3366615371977523053797395 := by
  unfold tailWord_6556460
  simp only [CollatzResearch.WordTrace]
  refine ⟨119566870913536324532461417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159422494551381766043281889 119566870913536324532461417)
  ·
    refine ⟨89675153185152243399346063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119566870913536324532461417 89675153185152243399346063)
    ·
      refine ⟨134512729777728365099019095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89675153185152243399346063 134512729777728365099019095)
      ·
        refine ⟨201769094666592547648528643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134512729777728365099019095 201769094666592547648528643)
        ·
          refine ⟨302653641999888821472792965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201769094666592547648528643 302653641999888821472792965)
          ·
            refine ⟨56747557874979154026148681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302653641999888821472792965 56747557874979154026148681)
            ·
              refine ⟨42560668406234365519611511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56747557874979154026148681 42560668406234365519611511)
              ·
                refine ⟨63841002609351548279417267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42560668406234365519611511 63841002609351548279417267)
                ·
                  refine ⟨95761503914027322419125901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63841002609351548279417267 95761503914027322419125901)
                  ·
                    refine ⟨35910563967760245907172213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95761503914027322419125901 35910563967760245907172213)
                    ·
                      refine ⟨3366615371977523053797395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35910563967760245907172213 3366615371977523053797395)
                      ·
                        rfl

theorem cell23_6556460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_6556460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556460 prefixEnd_6556460 := by exact prefixLift 6556460
  have htrace : WordTrace (prefixWord ++ tailWord_6556460) baseStart_6556460 baseEnd_6556460 := by
    simpa [prefixWord, tailWord_6556460, baseEnd_6556460] using wordTrace_append hprefix tailTrace_6556460
  have hstable : (prefixWord ++ tailWord_6556460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556460).length < 2 ^ (prefixWord ++ tailWord_6556460).sum := by decide
  have hdescent : baseEnd_6556460 < baseStart_6556460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556537 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6556537 : Nat := 118140960795 + 6556537 * 2 ^ 59
def prefixEnd_6556537 : Nat := 4983230072969 + 3 ^ 40 * 6556537 * 2
def baseEnd_6556537 : Nat := 3366654909987919252534541

theorem tailTrace_6556537 : CollatzResearch.WordTrace tailWord_6556537 prefixEnd_6556537 3366654909987919252534541 := by
  unfold tailWord_6556537
  simp only [CollatzResearch.WordTrace]
  refine ⟨239136550247793691215475865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159424366831862460810317243 239136550247793691215475865)
  ·
    refine ⟨179352412685845268411606899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239136550247793691215475865 179352412685845268411606899)
    ·
      refine ⟨269028619028767902617410349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179352412685845268411606899 269028619028767902617410349)
      ·
        refine ⟨100885732135787963481528881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269028619028767902617410349 100885732135787963481528881)
        ·
          refine ⟨75664299101840972611146661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100885732135787963481528881 75664299101840972611146661)
          ·
            refine ⟨14187056081595182364589999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75664299101840972611146661 14187056081595182364589999)
            ·
              refine ⟨21280584122392773546884999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14187056081595182364589999 21280584122392773546884999)
              ·
                refine ⟨31920876183589160320327499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21280584122392773546884999 31920876183589160320327499)
                ·
                  refine ⟨47881314275383740480491249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31920876183589160320327499 47881314275383740480491249)
                  ·
                    refine ⟨35910985706537805360368437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47881314275383740480491249 35910985706537805360368437)
                    ·
                      refine ⟨3366654909987919252534541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35910985706537805360368437 3366654909987919252534541)
                      ·
                        rfl

theorem cell23_6556537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6556537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556537 prefixEnd_6556537 := by exact prefixLift 6556537
  have htrace : WordTrace (prefixWord ++ tailWord_6556537) baseStart_6556537 baseEnd_6556537 := by
    simpa [prefixWord, tailWord_6556537, baseEnd_6556537] using wordTrace_append hprefix tailTrace_6556537
  have hstable : (prefixWord ++ tailWord_6556537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556537).length < 2 ^ (prefixWord ++ tailWord_6556537).sum := by decide
  have hdescent : baseEnd_6556537 < baseStart_6556537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556547 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4]
def baseStart_6556547 : Nat := 118140960795 + 6556547 * 2 ^ 59
def prefixEnd_6556547 : Nat := 4983230072969 + 3 ^ 40 * 6556547 * 2
def baseEnd_6556547 : Nat := 3366660044794464213409495

theorem tailTrace_6556547 : CollatzResearch.WordTrace tailWord_6556547 prefixEnd_6556547 3366660044794464213409495 := by
  unfold tailWord_6556547
  simp only [CollatzResearch.WordTrace]
  refine ⟨239136914977757462923339895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159424609985171641948893263 239136914977757462923339895)
  ·
    refine ⟨358705372466636194385009843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239136914977757462923339895 358705372466636194385009843)
    ·
      refine ⟨538058058699954291577514765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358705372466636194385009843 538058058699954291577514765)
      ·
        refine ⟨201771772012482859341568037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538058058699954291577514765 201771772012482859341568037)
        ·
          refine ⟨37832207252340536126544007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201771772012482859341568037 37832207252340536126544007)
          ·
            refine ⟨56748310878510804189816011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37832207252340536126544007 56748310878510804189816011)
            ·
              refine ⟨85122466317766206284724017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56748310878510804189816011 85122466317766206284724017)
              ·
                refine ⟨63841849738324654713543013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85122466317766206284724017 63841849738324654713543013)
                ·
                  refine ⟨11970346825935872758789315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63841849738324654713543013 11970346825935872758789315)
                  ·
                    refine ⟨17955520238903809138183973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11970346825935872758789315 17955520238903809138183973)
                    ·
                      refine ⟨3366660044794464213409495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17955520238903809138183973 3366660044794464213409495)
                      ·
                        rfl

theorem cell23_6556547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_6556547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556547 prefixEnd_6556547 := by exact prefixLift 6556547
  have htrace : WordTrace (prefixWord ++ tailWord_6556547) baseStart_6556547 baseEnd_6556547 := by
    simpa [prefixWord, tailWord_6556547, baseEnd_6556547] using wordTrace_append hprefix tailTrace_6556547
  have hstable : (prefixWord ++ tailWord_6556547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556547).length < 2 ^ (prefixWord ++ tailWord_6556547).sum := by decide
  have hdescent : baseEnd_6556547 < baseStart_6556547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556648 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6556648 : Nat := 118140960795 + 6556648 * 2 ^ 59
def prefixEnd_6556648 : Nat := 4983230072969 + 3 ^ 40 * 6556648 * 2
def baseEnd_6556648 : Nat := 3366711906340568318246531

theorem tailTrace_6556648 : CollatzResearch.WordTrace tailWord_6556648 prefixEnd_6556648 3366711906340568318246531 := by
  unfold tailWord_6556648
  simp only [CollatzResearch.WordTrace]
  refine ⟨119570299375195778586383299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159427065833594371448511065 119570299375195778586383299)
  ·
    refine ⟨179355449062793667879574949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119570299375195778586383299 179355449062793667879574949)
    ·
      refine ⟨33629146699273812727420303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179355449062793667879574949 33629146699273812727420303)
      ·
        refine ⟨50443720048910719091130455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33629146699273812727420303 50443720048910719091130455)
        ·
          refine ⟨75665580073366078636695683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50443720048910719091130455 75665580073366078636695683)
          ·
            refine ⟨113498370110049117955043525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75665580073366078636695683 113498370110049117955043525)
            ·
              refine ⟨21280944395634209616570661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113498370110049117955043525 21280944395634209616570661)
              ·
                refine ⟨3990177074181414303106999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21280944395634209616570661 3990177074181414303106999)
                ·
                  refine ⟨5985265611272121454660499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990177074181414303106999 5985265611272121454660499)
                  ·
                    refine ⟨8977898416908182181990749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5985265611272121454660499 8977898416908182181990749)
                    ·
                      refine ⟨3366711906340568318246531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8977898416908182181990749 3366711906340568318246531)
                      ·
                        rfl

theorem cell23_6556648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6556648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556648 prefixEnd_6556648 := by exact prefixLift 6556648
  have htrace : WordTrace (prefixWord ++ tailWord_6556648) baseStart_6556648 baseEnd_6556648 := by
    simpa [prefixWord, tailWord_6556648, baseEnd_6556648] using wordTrace_append hprefix tailTrace_6556648
  have hstable : (prefixWord ++ tailWord_6556648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556648).length < 2 ^ (prefixWord ++ tailWord_6556648).sum := by decide
  have hdescent : baseEnd_6556648 < baseStart_6556648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556677 : List Nat := [1, 3, 1, 1, 2, 3, 3, 9]
def baseStart_6556677 : Nat := 118140960795 + 6556677 * 2 ^ 59
def prefixEnd_6556677 : Nat := 4983230072969 + 3 ^ 40 * 6556677 * 2
def baseEnd_6556677 : Nat := 124693585084427729806811

theorem tailTrace_6556677 : CollatzResearch.WordTrace tailWord_6556677 prefixEnd_6556677 124693585084427729806811 := by
  unfold tailWord_6556677
  simp only [CollatzResearch.WordTrace]
  refine ⟨239141656467286495125572285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159427770978190996750381523 239141656467286495125572285)
  ·
    refine ⟨89678121175232435672089607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239141656467286495125572285 89678121175232435672089607)
    ·
      refine ⟨134517181762848653508134411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89678121175232435672089607 134517181762848653508134411)
      ·
        refine ⟨201775772644272980262201617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134517181762848653508134411 201775772644272980262201617)
        ·
          refine ⟨151331829483204735196651213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201775772644272980262201617 151331829483204735196651213)
          ·
            refine ⟨56749436056201775698744205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151331829483204735196651213 56749436056201775698744205)
            ·
              refine ⟨21281038521075665887029077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56749436056201775698744205 21281038521075665887029077)
              ·
                refine ⟨124693585084427729806811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21281038521075665887029077 124693585084427729806811)
                ·
                  rfl

theorem cell23_6556677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 9].length) (baseStart_6556677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556677 prefixEnd_6556677 := by exact prefixLift 6556677
  have htrace : WordTrace (prefixWord ++ tailWord_6556677) baseStart_6556677 baseEnd_6556677 := by
    simpa [prefixWord, tailWord_6556677, baseEnd_6556677] using wordTrace_append hprefix tailTrace_6556677
  have hstable : (prefixWord ++ tailWord_6556677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556677).length < 2 ^ (prefixWord ++ tailWord_6556677).sum := by decide
  have hdescent : baseEnd_6556677 < baseStart_6556677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556705 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6556705 : Nat := 118140960795 + 6556705 * 2 ^ 59
def prefixEnd_6556705 : Nat := 4983230072969 + 3 ^ 40 * 6556705 * 2
def baseEnd_6556705 : Nat := 3366741174737874595233769

theorem tailTrace_6556705 : CollatzResearch.WordTrace tailWord_6556705 prefixEnd_6556705 3366741174737874595233769 := by
  unfold tailWord_6556705
  simp only [CollatzResearch.WordTrace]
  refine ⟨239142677711185055907591569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159428451807456703938394379 239142677711185055907591569)
  ·
    refine ⟨179357008283388791930693677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239142677711185055907591569 179357008283388791930693677)
    ·
      refine ⟨67258878106270796974010129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179357008283388791930693677 67258878106270796974010129)
      ·
        refine ⟨50444158579703097730507597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67258878106270796974010129 50444158579703097730507597)
        ·
          refine ⟨18916559467388661648940349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50444158579703097730507597 18916559467388661648940349)
          ·
            refine ⟨7093709800270748118352631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18916559467388661648940349 7093709800270748118352631)
            ·
              refine ⟨10640564700406122177528947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093709800270748118352631 10640564700406122177528947)
              ·
                refine ⟨15960847050609183266293421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10640564700406122177528947 15960847050609183266293421)
                ·
                  refine ⟨5985317643978443724860033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15960847050609183266293421 5985317643978443724860033)
                  ·
                    refine ⟨4488988232983832793645025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5985317643978443724860033 4488988232983832793645025)
                    ·
                      refine ⟨3366741174737874595233769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488988232983832793645025 3366741174737874595233769)
                      ·
                        rfl

theorem cell23_6556705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6556705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556705 prefixEnd_6556705 := by exact prefixLift 6556705
  have htrace : WordTrace (prefixWord ++ tailWord_6556705) baseStart_6556705 baseEnd_6556705 := by
    simpa [prefixWord, tailWord_6556705, baseEnd_6556705] using wordTrace_append hprefix tailTrace_6556705
  have hstable : (prefixWord ++ tailWord_6556705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556705).length < 2 ^ (prefixWord ++ tailWord_6556705).sum := by decide
  have hdescent : baseEnd_6556705 < baseStart_6556705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556711 : List Nat := [1, 1, 7, 1, 1, 2, 2, 8]
def baseStart_6556711 : Nat := 118140960795 + 6556711 * 2 ^ 59
def prefixEnd_6556711 : Nat := 4983230072969 + 3 ^ 40 * 6556711 * 2
def baseEnd_6556711 : Nat := 124694231689696354509583

theorem tailTrace_6556711 : CollatzResearch.WordTrace tailWord_6556711 prefixEnd_6556711 124694231689696354509583 := by
  unfold tailWord_6556711
  simp only [CollatzResearch.WordTrace]
  refine ⟨239142896549163318932309987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159428597699442212621539991 239142896549163318932309987)
  ·
    refine ⟨358714344823744978398464981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239142896549163318932309987 358714344823744978398464981)
    ·
      refine ⟨8407367456806522931214023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 358714344823744978398464981 8407367456806522931214023)
      ·
        refine ⟨12611051185209784396821035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8407367456806522931214023 12611051185209784396821035)
        ·
          refine ⟨18916576777814676595231553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12611051185209784396821035 18916576777814676595231553)
          ·
            refine ⟨14187432583361007446423665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18916576777814676595231553 14187432583361007446423665)
            ·
              refine ⟨10640574437520755584817749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14187432583361007446423665 10640574437520755584817749)
              ·
                refine ⟨124694231689696354509583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10640574437520755584817749 124694231689696354509583)
                ·
                  rfl

theorem cell23_6556711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 8].length) (baseStart_6556711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556711 prefixEnd_6556711 := by exact prefixLift 6556711
  have htrace : WordTrace (prefixWord ++ tailWord_6556711) baseStart_6556711 baseEnd_6556711 := by
    simpa [prefixWord, tailWord_6556711, baseEnd_6556711] using wordTrace_append hprefix tailTrace_6556711
  have hstable : (prefixWord ++ tailWord_6556711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556711).length < 2 ^ (prefixWord ++ tailWord_6556711).sum := by decide
  have hdescent : baseEnd_6556711 < baseStart_6556711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556727 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_6556727 : Nat := 118140960795 + 6556727 * 2 ^ 59
def prefixEnd_6556727 : Nat := 4983230072969 + 3 ^ 40 * 6556727 * 2
def baseEnd_6556727 : Nat := 3366752471312273509158667

theorem tailTrace_6556727 : CollatzResearch.WordTrace tailWord_6556727 prefixEnd_6556727 3366752471312273509158667 := by
  unfold tailWord_6556727
  simp only [CollatzResearch.WordTrace]
  refine ⟨239143480117105353664892435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159428986744736902443261623 239143480117105353664892435)
  ·
    refine ⟨358715220175658030497338653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239143480117105353664892435 358715220175658030497338653)
    ·
      refine ⟨134518207565871761436501995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358715220175658030497338653 134518207565871761436501995)
      ·
        refine ⟨201777311348807642154752993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134518207565871761436501995 201777311348807642154752993)
        ·
          refine ⟨151332983511605731616064745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201777311348807642154752993 151332983511605731616064745)
          ·
            refine ⟨113499737633704298712048559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151332983511605731616064745 113499737633704298712048559)
            ·
              refine ⟨170249606450556448068072839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113499737633704298712048559 170249606450556448068072839)
              ·
                refine ⟨255374409675834672102109259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170249606450556448068072839 255374409675834672102109259)
                ·
                  refine ⟨383061614513752008153163889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255374409675834672102109259 383061614513752008153163889)
                  ·
                    refine ⟨287296210885314006114872917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383061614513752008153163889 287296210885314006114872917)
                    ·
                      refine ⟨3366752471312273509158667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287296210885314006114872917 3366752471312273509158667)
                      ·
                        rfl

theorem cell23_6556727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_6556727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556727 prefixEnd_6556727 := by exact prefixLift 6556727
  have htrace : WordTrace (prefixWord ++ tailWord_6556727) baseStart_6556727 baseEnd_6556727 := by
    simpa [prefixWord, tailWord_6556727, baseEnd_6556727] using wordTrace_append hprefix tailTrace_6556727
  have hstable : (prefixWord ++ tailWord_6556727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556727).length < 2 ^ (prefixWord ++ tailWord_6556727).sum := by decide
  have hdescent : baseEnd_6556727 < baseStart_6556727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556742 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6556742 : Nat := 118140960795 + 6556742 * 2 ^ 59
def prefixEnd_6556742 : Nat := 4983230072969 + 3 ^ 40 * 6556742 * 2
def baseEnd_6556742 : Nat := 3366760173522090950471099

theorem tailTrace_6556742 : CollatzResearch.WordTrace tailWord_6556742 prefixEnd_6556742 3366760173522090950471099 := by
  unfold tailWord_6556742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473250850376594100834015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159429351474700674151125653 7473250850376594100834015)
  ·
    refine ⟨11209876275564891151251023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7473250850376594100834015 11209876275564891151251023)
    ·
      refine ⟨16814814413347336726876535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11209876275564891151251023 16814814413347336726876535)
      ·
        refine ⟨25222221620021005090314803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16814814413347336726876535 25222221620021005090314803)
        ·
          refine ⟨37833332430031507635472205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25222221620021005090314803 37833332430031507635472205)
          ·
            refine ⟨14187499661261815363302077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37833332430031507635472205 14187499661261815363302077)
            ·
              refine ⟨5320312372973180761238279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14187499661261815363302077 5320312372973180761238279)
              ·
                refine ⟨7980468559459771141857419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320312372973180761238279 7980468559459771141857419)
                ·
                  refine ⟨11970702839189656712786129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7980468559459771141857419 11970702839189656712786129)
                  ·
                    refine ⟨8978027129392242534589597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11970702839189656712786129 8978027129392242534589597)
                    ·
                      refine ⟨3366760173522090950471099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8978027129392242534589597 3366760173522090950471099)
                      ·
                        rfl

theorem cell23_6556742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6556742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556742 prefixEnd_6556742 := by exact prefixLift 6556742
  have htrace : WordTrace (prefixWord ++ tailWord_6556742) baseStart_6556742 baseEnd_6556742 := by
    simpa [prefixWord, tailWord_6556742, baseEnd_6556742] using wordTrace_append hprefix tailTrace_6556742
  have hstable : (prefixWord ++ tailWord_6556742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556742).length < 2 ^ (prefixWord ++ tailWord_6556742).sum := by decide
  have hdescent : baseEnd_6556742 < baseStart_6556742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556778 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_6556778 : Nat := 118140960795 + 6556778 * 2 ^ 59
def prefixEnd_6556778 : Nat := 4983230072969 + 3 ^ 40 * 6556778 * 2
def baseEnd_6556778 : Nat := 3366778658825652809620933

theorem tailTrace_6556778 : CollatzResearch.WordTrace tailWord_6556778 prefixEnd_6556778 3366778658825652809620933 := by
  unfold tailWord_6556778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59786335059980147343749747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159430226826613726249999325 59786335059980147343749747)
  ·
    refine ⟨89679502589970221015624621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59786335059980147343749747 89679502589970221015624621)
    ·
      refine ⟨33629813471238832880859233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89679502589970221015624621 33629813471238832880859233)
      ·
        refine ⟨25222360103429124660644425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33629813471238832880859233 25222360103429124660644425)
        ·
          refine ⟨18916770077571843495483319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25222360103429124660644425 18916770077571843495483319)
          ·
            refine ⟨28375155116357765243224979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18916770077571843495483319 28375155116357765243224979)
            ·
              refine ⟨42562732674536647864837469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28375155116357765243224979 42562732674536647864837469)
              ·
                refine ⟨15961024752951242949314051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42562732674536647864837469 15961024752951242949314051)
                ·
                  refine ⟨23941537129426864423971077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15961024752951242949314051 23941537129426864423971077)
                  ·
                    refine ⟨4489038211767537079494577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23941537129426864423971077 4489038211767537079494577)
                    ·
                      refine ⟨3366778658825652809620933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489038211767537079494577 3366778658825652809620933)
                      ·
                        rfl

theorem cell23_6556778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_6556778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556778 prefixEnd_6556778 := by exact prefixLift 6556778
  have htrace : WordTrace (prefixWord ++ tailWord_6556778) baseStart_6556778 baseEnd_6556778 := by
    simpa [prefixWord, tailWord_6556778, baseEnd_6556778] using wordTrace_append hprefix tailTrace_6556778
  have hstable : (prefixWord ++ tailWord_6556778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556778).length < 2 ^ (prefixWord ++ tailWord_6556778).sum := by decide
  have hdescent : baseEnd_6556778 < baseStart_6556778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556784 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 7]
def baseStart_6556784 : Nat := 118140960795 + 6556784 * 2 ^ 59
def prefixEnd_6556784 : Nat := 4983230072969 + 3 ^ 40 * 6556784 * 2
def baseEnd_6556784 : Nat := 374086859967731087349545

theorem tailTrace_6556784 : CollatzResearch.WordTrace tailWord_6556784 prefixEnd_6556784 374086859967731087349545 := by
  unfold tailWord_6556784
  simp only [CollatzResearch.WordTrace]
  refine ⟨119572779538949426199858703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159430372718599234933144937 119572779538949426199858703)
  ·
    refine ⟨179359169308424139299788055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119572779538949426199858703 179359169308424139299788055)
    ·
      refine ⟨269038753962636208949682083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179359169308424139299788055 269038753962636208949682083)
      ·
        refine ⟨403558130943954313424523125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269038753962636208949682083 403558130943954313424523125)
        ·
          refine ⟨37833574775995716883549043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 403558130943954313424523125 37833574775995716883549043)
          ·
            refine ⟨56750362163993575325323565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37833574775995716883549043 56750362163993575325323565)
            ·
              refine ⟨21281385811497590746996337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56750362163993575325323565 21281385811497590746996337)
              ·
                refine ⟨15961039358623193060247253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21281385811497590746996337 15961039358623193060247253)
                ·
                  refine ⟨374086859967731087349545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15961039358623193060247253 374086859967731087349545)
                  ·
                    rfl

theorem cell23_6556784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_6556784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556784 prefixEnd_6556784 := by exact prefixLift 6556784
  have htrace : WordTrace (prefixWord ++ tailWord_6556784) baseStart_6556784 baseEnd_6556784 := by
    simpa [prefixWord, tailWord_6556784, baseEnd_6556784] using wordTrace_append hprefix tailTrace_6556784
  have hstable : (prefixWord ++ tailWord_6556784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556784).length < 2 ^ (prefixWord ++ tailWord_6556784).sum := by decide
  have hdescent : baseEnd_6556784 < baseStart_6556784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556818 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_6556818 : Nat := 118140960795 + 6556818 * 2 ^ 59
def prefixEnd_6556818 : Nat := 4983230072969 + 3 ^ 40 * 6556818 * 2
def baseEnd_6556818 : Nat := 374088799783536961457861

theorem tailTrace_6556818 : CollatzResearch.WordTrace tailWord_6556818 prefixEnd_6556818 374088799783536961457861 := by
  unfold tailWord_6556818
  simp only [CollatzResearch.WordTrace]
  refine ⟨59786699789943919051613777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159431199439850450804303405 59786699789943919051613777)
  ·
    refine ⟨44840024842457939288710333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59786699789943919051613777 44840024842457939288710333)
    ·
      refine ⟨16815009315921727233266375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44840024842457939288710333 16815009315921727233266375)
      ·
        refine ⟨25222513973882590849899563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815009315921727233266375 25222513973882590849899563)
        ·
          refine ⟨37833770960823886274849345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25222513973882590849899563 37833770960823886274849345)
          ·
            refine ⟨28375328220617914706137009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37833770960823886274849345 28375328220617914706137009)
            ·
              refine ⟨21281496165463436029602757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28375328220617914706137009 21281496165463436029602757)
              ·
                refine ⟨3990280531024394255550517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21281496165463436029602757 3990280531024394255550517)
                ·
                  refine ⟨374088799783536961457861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990280531024394255550517 374088799783536961457861)
                  ·
                    rfl

theorem cell23_6556818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_6556818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556818 prefixEnd_6556818 := by exact prefixLift 6556818
  have htrace : WordTrace (prefixWord ++ tailWord_6556818) baseStart_6556818 baseEnd_6556818 := by
    simpa [prefixWord, tailWord_6556818, baseEnd_6556818] using wordTrace_append hprefix tailTrace_6556818
  have hstable : (prefixWord ++ tailWord_6556818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556818).length < 2 ^ (prefixWord ++ tailWord_6556818).sum := by decide
  have hdescent : baseEnd_6556818 < baseStart_6556818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556821 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_6556821 : Nat := 118140960795 + 6556821 * 2 ^ 59
def prefixEnd_6556821 : Nat := 4983230072969 + 3 ^ 40 * 6556821 * 2
def baseEnd_6556821 : Nat := 3366800738493796141383235

theorem tailTrace_6556821 : CollatzResearch.WordTrace tailWord_6556821 prefixEnd_6556821 3366800738493796141383235 := by
  unfold tailWord_6556821
  simp only [CollatzResearch.WordTrace]
  refine ⟨239146908578764807718814317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159431272385843205145876211 239146908578764807718814317)
  ·
    refine ⟨89680090717036802894555369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239146908578764807718814317 89680090717036802894555369)
    ·
      refine ⟨67260068037777602170916527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89680090717036802894555369 67260068037777602170916527)
      ·
        refine ⟨100890102056666403256374791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67260068037777602170916527 100890102056666403256374791)
        ·
          refine ⟨151335153084999604884562187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100890102056666403256374791 151335153084999604884562187)
          ·
            refine ⟨227002729627499407326843281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151335153084999604884562187 227002729627499407326843281)
            ·
              refine ⟨170252047220624555495132461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227002729627499407326843281 170252047220624555495132461)
              ·
                refine ⟨63844517707734208310674673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170252047220624555495132461 63844517707734208310674673)
                ·
                  refine ⟨47883388280800656233006005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63844517707734208310674673 47883388280800656233006005)
                  ·
                    refine ⟨4489067651325061521844313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47883388280800656233006005 4489067651325061521844313)
                    ·
                      refine ⟨3366800738493796141383235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489067651325061521844313 3366800738493796141383235)
                      ·
                        rfl

theorem cell23_6556821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_6556821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556821 prefixEnd_6556821 := by exact prefixLift 6556821
  have htrace : WordTrace (prefixWord ++ tailWord_6556821) baseStart_6556821 baseEnd_6556821 := by
    simpa [prefixWord, tailWord_6556821, baseEnd_6556821] using wordTrace_append hprefix tailTrace_6556821
  have hstable : (prefixWord ++ tailWord_6556821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556821).length < 2 ^ (prefixWord ++ tailWord_6556821).sum := by decide
  have hdescent : baseEnd_6556821 < baseStart_6556821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556851 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 6, 2]
def baseStart_6556851 : Nat := 118140960795 + 6556851 * 2 ^ 59
def prefixEnd_6556851 : Nat := 4983230072969 + 3 ^ 40 * 6556851 * 2
def baseEnd_6556851 : Nat := 3366816142913431024008097

theorem tailTrace_6556851 : CollatzResearch.WordTrace tailWord_6556851 prefixEnd_6556851 3366816142913431024008097 := by
  unfold tailWord_6556851
  simp only [CollatzResearch.WordTrace]
  refine ⟨239148002768656122842406407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159432001845770748561604271 239148002768656122842406407)
  ·
    refine ⟨358722004152984184263609611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239148002768656122842406407 358722004152984184263609611)
    ·
      refine ⟨538083006229476276395414417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358722004152984184263609611 538083006229476276395414417)
      ·
        refine ⟨403562254672107207296560813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538083006229476276395414417 403562254672107207296560813)
        ·
          refine ⟨151335845502040202736210305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403562254672107207296560813 151335845502040202736210305)
          ·
            refine ⟨113501884126530152052157729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151335845502040202736210305 113501884126530152052157729)
            ·
              refine ⟨85126413094897614039118297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113501884126530152052157729 85126413094897614039118297)
              ·
                refine ⟨63844809821173210529338723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85126413094897614039118297 63844809821173210529338723)
                ·
                  refine ⟨95767214731759815794008085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63844809821173210529338723 95767214731759815794008085)
                  ·
                    refine ⟨4489088190551241365344129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95767214731759815794008085 4489088190551241365344129)
                    ·
                      refine ⟨3366816142913431024008097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489088190551241365344129 3366816142913431024008097)
                      ·
                        rfl

theorem cell23_6556851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6, 2].length) (baseStart_6556851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556851 prefixEnd_6556851 := by exact prefixLift 6556851
  have htrace : WordTrace (prefixWord ++ tailWord_6556851) baseStart_6556851 baseEnd_6556851 := by
    simpa [prefixWord, tailWord_6556851, baseEnd_6556851] using wordTrace_append hprefix tailTrace_6556851
  have hstable : (prefixWord ++ tailWord_6556851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556851).length < 2 ^ (prefixWord ++ tailWord_6556851).sum := by decide
  have hdescent : baseEnd_6556851 < baseStart_6556851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556861 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_6556861 : Nat := 118140960795 + 6556861 * 2 ^ 59
def prefixEnd_6556861 : Nat := 4983230072969 + 3 ^ 40 * 6556861 * 2
def baseEnd_6556861 : Nat := 1122273759239991994961017

theorem tailTrace_6556861 : CollatzResearch.WordTrace tailWord_6556861 prefixEnd_6556861 1122273759239991994961017 := by
  unfold tailWord_6556861
  simp only [CollatzResearch.WordTrace]
  refine ⟨239148367498619894550270437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159432244999079929700180291 239148367498619894550270437)
  ·
    refine ⟨44840318905991230228175707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239148367498619894550270437 44840318905991230228175707)
    ·
      refine ⟨67260478358986845342263561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44840318905991230228175707 67260478358986845342263561)
      ·
        refine ⟨50445358769240134006697671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67260478358986845342263561 50445358769240134006697671)
        ·
          refine ⟨75668038153860201010046507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50445358769240134006697671 75668038153860201010046507)
          ·
            refine ⟨113502057230790301515069761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75668038153860201010046507 113502057230790301515069761)
            ·
              refine ⟨85126542923092726136302321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113502057230790301515069761 85126542923092726136302321)
              ·
                refine ⟨63844907192319544602226741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85126542923092726136302321 63844907192319544602226741)
                ·
                  refine ⟨5985460049279957306458757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63844907192319544602226741 5985460049279957306458757)
                  ·
                    refine ⟨1122273759239991994961017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985460049279957306458757 1122273759239991994961017)
                    ·
                      rfl

theorem cell23_6556861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_6556861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556861 prefixEnd_6556861 := by exact prefixLift 6556861
  have htrace : WordTrace (prefixWord ++ tailWord_6556861) baseStart_6556861 baseEnd_6556861 := by
    simpa [prefixWord, tailWord_6556861, baseEnd_6556861] using wordTrace_append hprefix tailTrace_6556861
  have hstable : (prefixWord ++ tailWord_6556861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556861).length < 2 ^ (prefixWord ++ tailWord_6556861).sum := by decide
  have hdescent : baseEnd_6556861 < baseStart_6556861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556968 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6556968 : Nat := 118140960795 + 6556968 * 2 ^ 59
def prefixEnd_6556968 : Nat := 4983230072969 + 3 ^ 40 * 6556968 * 2
def baseEnd_6556968 : Nat := 1122292073383335688748353

theorem tailTrace_6556968 : CollatzResearch.WordTrace tailWord_6556968 prefixEnd_6556968 1122292073383335688748353 := by
  unfold tailWord_6556968
  simp only [CollatzResearch.WordTrace]
  refine ⟨119576135054616125912207779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159434846739488167882943705 119576135054616125912207779)
  ·
    refine ⟨179364202581924188868311669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119576135054616125912207779 179364202581924188868311669)
    ·
      refine ⟨16815393992055392706404219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179364202581924188868311669 16815393992055392706404219)
      ·
        refine ⟨25223090988083089059606329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815393992055392706404219 25223090988083089059606329)
        ·
          refine ⟨18917318241062316794704747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25223090988083089059606329 18917318241062316794704747)
          ·
            refine ⟨28375977361593475192057121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18917318241062316794704747 28375977361593475192057121)
            ·
              refine ⟨21281983021195106394042841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28375977361593475192057121 21281983021195106394042841)
              ·
                refine ⟨15961487265896329795532131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21281983021195106394042841 15961487265896329795532131)
                ·
                  refine ⟨23942230898844494693298197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15961487265896329795532131 23942230898844494693298197)
                  ·
                    refine ⟨1122292073383335688748353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23942230898844494693298197 1122292073383335688748353)
                    ·
                      rfl

theorem cell23_6556968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6556968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556968 prefixEnd_6556968 := by exact prefixLift 6556968
  have htrace : WordTrace (prefixWord ++ tailWord_6556968) baseStart_6556968 baseEnd_6556968 := by
    simpa [prefixWord, tailWord_6556968, baseEnd_6556968] using wordTrace_append hprefix tailTrace_6556968
  have hstable : (prefixWord ++ tailWord_6556968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556968).length < 2 ^ (prefixWord ++ tailWord_6556968).sum := by decide
  have hdescent : baseEnd_6556968 < baseStart_6556968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556981 : List Nat := [1, 3, 3, 1, 2, 3, 10]
def baseStart_6556981 : Nat := 118140960795 + 6556981 * 2 ^ 59
def prefixEnd_6556981 : Nat := 4983230072969 + 3 ^ 40 * 6556981 * 2
def baseEnd_6556981 : Nat := 41566455498747105128179

theorem tailTrace_6556981 : CollatzResearch.WordTrace tailWord_6556981 prefixEnd_6556981 41566455498747105128179 := by
  unfold tailWord_6556981
  simp only [CollatzResearch.WordTrace]
  refine ⟨239152744258185155044638797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159435162838790103363092531 239152744258185155044638797)
  ·
    refine ⟨89682279096819433141739549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239152744258185155044638797 89682279096819433141739549)
    ·
      refine ⟨33630854661307287428152331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89682279096819433141739549 33630854661307287428152331)
      ·
        refine ⟨50446281991960931142228497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33630854661307287428152331 50446281991960931142228497)
        ·
          refine ⟨37834711493970698356671373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50446281991960931142228497 37834711493970698356671373)
          ·
            refine ⟨14188016810239011883751765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37834711493970698356671373 14188016810239011883751765)
            ·
              refine ⟨41566455498747105128179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14188016810239011883751765 41566455498747105128179)
              ·
                rfl

theorem cell23_6556981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 10].length) (baseStart_6556981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556981 prefixEnd_6556981 := by exact prefixLift 6556981
  have htrace : WordTrace (prefixWord ++ tailWord_6556981) baseStart_6556981 baseEnd_6556981 := by
    simpa [prefixWord, tailWord_6556981, baseEnd_6556981] using wordTrace_append hprefix tailTrace_6556981
  have hstable : (prefixWord ++ tailWord_6556981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556981).length < 2 ^ (prefixWord ++ tailWord_6556981).sum := by decide
  have hdescent : baseEnd_6556981 < baseStart_6556981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556985 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_6556985 : Nat := 118140960795 + 6556985 * 2 ^ 59
def prefixEnd_6556985 : Nat := 4983230072969 + 3 ^ 40 * 6556985 * 2
def baseEnd_6556985 : Nat := 1122294983107044499910827

theorem tailTrace_6556985 : CollatzResearch.WordTrace tailWord_6556985 prefixEnd_6556985 1122294983107044499910827 := by
  unfold tailWord_6556985
  simp only [CollatzResearch.WordTrace]
  refine ⟨239152890150170663727784409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159435260100113775818522939 239152890150170663727784409)
  ·
    refine ⟨179364667612627997795838307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239152890150170663727784409 179364667612627997795838307)
    ·
      refine ⟨269047001418941996693757461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179364667612627997795838307 269047001418941996693757461)
      ·
        refine ⟨12611578191512906095019881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 269047001418941996693757461 12611578191512906095019881)
        ·
          refine ⟨9458683643634679571264911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12611578191512906095019881 9458683643634679571264911)
          ·
            refine ⟨14188025465452019356897367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458683643634679571264911 14188025465452019356897367)
            ·
              refine ⟨21282038198178029035346051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14188025465452019356897367 21282038198178029035346051)
              ·
                refine ⟨31923057297267043553019077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21282038198178029035346051 31923057297267043553019077)
                ·
                  refine ⟨5985573243237570666191077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31923057297267043553019077 5985573243237570666191077)
                  ·
                    refine ⟨1122294983107044499910827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985573243237570666191077 1122294983107044499910827)
                    ·
                      rfl

theorem cell23_6556985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_6556985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556985 prefixEnd_6556985 := by exact prefixLift 6556985
  have htrace : WordTrace (prefixWord ++ tailWord_6556985) baseStart_6556985 baseEnd_6556985 := by
    simpa [prefixWord, tailWord_6556985, baseEnd_6556985] using wordTrace_append hprefix tailTrace_6556985
  have hstable : (prefixWord ++ tailWord_6556985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556985).length < 2 ^ (prefixWord ++ tailWord_6556985).sum := by decide
  have hdescent : baseEnd_6556985 < baseStart_6556985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6556992 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 1, 2, 2]
def baseStart_6556992 : Nat := 118140960795 + 6556992 * 2 ^ 59
def prefixEnd_6556992 : Nat := 4983230072969 + 3 ^ 40 * 6556992 * 2
def baseEnd_6556992 : Nat := 3366888543685714972344949

theorem tailTrace_6556992 : CollatzResearch.WordTrace tailWord_6556992 prefixEnd_6556992 3366888543685714972344949 := by
  unfold tailWord_6556992
  simp only [CollatzResearch.WordTrace]
  refine ⟨119576572730572651961644615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159435430307430202615526153 119576572730572651961644615)
  ·
    refine ⟨179364859095858977942466923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119576572730572651961644615 179364859095858977942466923)
    ·
      refine ⟨269047288643788466913700385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179364859095858977942466923 269047288643788466913700385)
      ·
        refine ⟨201785466482841350185275289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269047288643788466913700385 201785466482841350185275289)
        ·
          refine ⟨151339099862131012638956467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201785466482841350185275289 151339099862131012638956467)
          ·
            refine ⟨227008649793196518958434701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151339099862131012638956467 227008649793196518958434701)
            ·
              refine ⟨85128243672448694609413013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227008649793196518958434701 85128243672448694609413013)
              ·
                refine ⟨3990386422146032559816235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85128243672448694609413013 3990386422146032559816235)
                ·
                  refine ⟨5985579633219048839724353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990386422146032559816235 5985579633219048839724353)
                  ·
                    refine ⟨4489184724914286629793265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5985579633219048839724353 4489184724914286629793265)
                    ·
                      refine ⟨3366888543685714972344949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489184724914286629793265 3366888543685714972344949)
                      ·
                        rfl

theorem cell23_6556992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_6556992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6556992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6556992 prefixEnd_6556992 := by exact prefixLift 6556992
  have htrace : WordTrace (prefixWord ++ tailWord_6556992) baseStart_6556992 baseEnd_6556992 := by
    simpa [prefixWord, tailWord_6556992, baseEnd_6556992] using wordTrace_append hprefix tailTrace_6556992
  have hstable : (prefixWord ++ tailWord_6556992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6556992).length < 2 ^ (prefixWord ++ tailWord_6556992).sum := by decide
  have hdescent : baseEnd_6556992 < baseStart_6556992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6556992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557041 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_6557041 : Nat := 118140960795 + 6557041 * 2 ^ 59
def prefixEnd_6557041 : Nat := 4983230072969 + 3 ^ 40 * 6557041 * 2
def baseEnd_6557041 : Nat := 1122304568079261760210741

theorem tailTrace_6557041 : CollatzResearch.WordTrace tailWord_6557041 prefixEnd_6557041 1122304568079261760210741 := by
  unfold tailWord_6557041
  simp only [CollatzResearch.WordTrace]
  refine ⟨239154932637967785291822977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159436621758645190194548651 239154932637967785291822977)
  ·
    refine ⟨179366199478475838968867233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239154932637967785291822977 179366199478475838968867233)
    ·
      refine ⟨134524649608856879226650425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179366199478475838968867233 134524649608856879226650425)
      ·
        refine ⟨100893487206642659419987819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134524649608856879226650425 100893487206642659419987819)
        ·
          refine ⟨151340230809963989129981729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100893487206642659419987819 151340230809963989129981729)
          ·
            refine ⟨113505173107472991847486297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151340230809963989129981729 113505173107472991847486297)
            ·
              refine ⟨85128879830604743885614723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113505173107472991847486297 85128879830604743885614723)
              ·
                refine ⟨127693319745907115828422085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85128879830604743885614723 127693319745907115828422085)
                ·
                  refine ⟨23942497452357584217829141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127693319745907115828422085 23942497452357584217829141)
                  ·
                    refine ⟨1122304568079261760210741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23942497452357584217829141 1122304568079261760210741)
                    ·
                      rfl

theorem cell23_6557041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_6557041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557041 prefixEnd_6557041 := by exact prefixLift 6557041
  have htrace : WordTrace (prefixWord ++ tailWord_6557041) baseStart_6557041 baseEnd_6557041 := by
    simpa [prefixWord, tailWord_6557041, baseEnd_6557041] using wordTrace_append hprefix tailTrace_6557041
  have hstable : (prefixWord ++ tailWord_6557041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557041).length < 2 ^ (prefixWord ++ tailWord_6557041).sum := by decide
  have hdescent : baseEnd_6557041 < baseStart_6557041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557051 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_6557051 : Nat := 118140960795 + 6557051 * 2 ^ 59
def prefixEnd_6557051 : Nat := 4983230072969 + 3 ^ 40 * 6557051 * 2
def baseEnd_6557051 : Nat := 3366918839044330241507177

theorem tailTrace_6557051 : CollatzResearch.WordTrace tailWord_6557051 prefixEnd_6557051 3366918839044330241507177 := by
  unfold tailWord_6557051
  simp only [CollatzResearch.WordTrace]
  refine ⟨239155297367931556999687007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159436864911954371333124671 239155297367931556999687007)
  ·
    refine ⟨358732946051897335499530511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239155297367931556999687007 358732946051897335499530511)
    ·
      refine ⟨538099419077846003249295767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358732946051897335499530511 538099419077846003249295767)
      ·
        refine ⟨807149128616769004873943651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538099419077846003249295767 807149128616769004873943651)
        ·
          refine ⟨1210723692925153507310915477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807149128616769004873943651 1210723692925153507310915477)
          ·
            refine ⟨56752673105866570655199163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1210723692925153507310915477 56752673105866570655199163)
            ·
              refine ⟨85129009658799855982798745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56752673105866570655199163 85129009658799855982798745)
              ·
                refine ⟨63846757244099891987099059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85129009658799855982798745 63846757244099891987099059)
                ·
                  refine ⟨95770135866149837980648589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63846757244099891987099059 95770135866149837980648589)
                  ·
                    refine ⟨35913800949806189242743221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95770135866149837980648589 35913800949806189242743221)
                    ·
                      refine ⟨3366918839044330241507177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35913800949806189242743221 3366918839044330241507177)
                      ·
                        rfl

theorem cell23_6557051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_6557051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557051 prefixEnd_6557051 := by exact prefixLift 6557051
  have htrace : WordTrace (prefixWord ++ tailWord_6557051) baseStart_6557051 baseEnd_6557051 := by
    simpa [prefixWord, tailWord_6557051, baseEnd_6557051] using wordTrace_append hprefix tailTrace_6557051
  have hstable : (prefixWord ++ tailWord_6557051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557051).length < 2 ^ (prefixWord ++ tailWord_6557051).sum := by decide
  have hdescent : baseEnd_6557051 < baseStart_6557051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557059 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 2, 1, 3]
def baseStart_6557059 : Nat := 118140960795 + 6557059 * 2 ^ 59
def prefixEnd_6557059 : Nat := 4983230072969 + 3 ^ 40 * 6557059 * 2
def baseEnd_6557059 : Nat := 3366922946889566210207141

theorem tailTrace_6557059 : CollatzResearch.WordTrace tailWord_6557059 prefixEnd_6557059 3366922946889566210207141 := by
  unfold tailWord_6557059
  simp only [CollatzResearch.WordTrace]
  refine ⟨239155589151902574365978231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159437059434601716243985487 239155589151902574365978231)
  ·
    refine ⟨358733383727853861548967347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239155589151902574365978231 358733383727853861548967347)
    ·
      refine ⟨538100075591780792323451021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358733383727853861548967347 538100075591780792323451021)
      ·
        refine ⟨201787528346917797121294133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538100075591780792323451021 201787528346917797121294133)
        ·
          refine ⟨18917580782523543480121325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201787528346917797121294133 18917580782523543480121325)
          ·
            refine ⟨7094092793446328805045497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18917580782523543480121325 7094092793446328805045497)
            ·
              refine ⟨5320569595084746603784123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7094092793446328805045497 5320569595084746603784123)
              ·
                refine ⟨7980854392627119905676185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320569595084746603784123 7980854392627119905676185)
                ·
                  refine ⟨5985640794470339929257139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7980854392627119905676185 5985640794470339929257139)
                  ·
                    refine ⟨8978461191705509893885709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5985640794470339929257139 8978461191705509893885709)
                    ·
                      refine ⟨3366922946889566210207141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8978461191705509893885709 3366922946889566210207141)
                      ·
                        rfl

theorem cell23_6557059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_6557059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557059 prefixEnd_6557059 := by exact prefixLift 6557059
  have htrace : WordTrace (prefixWord ++ tailWord_6557059) baseStart_6557059 baseEnd_6557059 := by
    simpa [prefixWord, tailWord_6557059, baseEnd_6557059] using wordTrace_append hprefix tailTrace_6557059
  have hstable : (prefixWord ++ tailWord_6557059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557059).length < 2 ^ (prefixWord ++ tailWord_6557059).sum := by decide
  have hdescent : baseEnd_6557059 < baseStart_6557059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557105 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 5]
def baseStart_6557105 : Nat := 118140960795 + 6557105 * 2 ^ 59
def prefixEnd_6557105 : Nat := 4983230072969 + 3 ^ 40 * 6557105 * 2
def baseEnd_6557105 : Nat := 374105174111074781136881

theorem tailTrace_6557105 : CollatzResearch.WordTrace tailWord_6557105 prefixEnd_6557105 374105174111074781136881 := by
  unfold tailWord_6557105
  simp only [CollatzResearch.WordTrace]
  refine ⟨239157266909735924222152769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159438177939823949481435179 239157266909735924222152769)
  ·
    refine ⟨179367950182301943166614577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239157266909735924222152769 179367950182301943166614577)
    ·
      refine ⟨134525962636726457374960933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179367950182301943166614577 134525962636726457374960933)
      ·
        refine ⟨25223617994386210757805175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134525962636726457374960933 25223617994386210757805175)
        ·
          refine ⟨37835426991579316136707763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25223617994386210757805175 37835426991579316136707763)
          ·
            refine ⟨56753140487368974205061645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37835426991579316136707763 56753140487368974205061645)
            ·
              refine ⟨21282427682763365326898117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56753140487368974205061645 21282427682763365326898117)
              ·
                refine ⟨3990455190518130998793397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21282427682763365326898117 3990455190518130998793397)
                ·
                  refine ⟨374105174111074781136881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990455190518130998793397 374105174111074781136881)
                  ·
                    rfl

theorem cell23_6557105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 5].length) (baseStart_6557105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557105 prefixEnd_6557105 := by exact prefixLift 6557105
  have htrace : WordTrace (prefixWord ++ tailWord_6557105) baseStart_6557105 baseEnd_6557105 := by
    simpa [prefixWord, tailWord_6557105, baseEnd_6557105] using wordTrace_append hprefix tailTrace_6557105
  have hstable : (prefixWord ++ tailWord_6557105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557105).length < 2 ^ (prefixWord ++ tailWord_6557105).sum := by decide
  have hdescent : baseEnd_6557105 < baseStart_6557105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557118 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_6557118 : Nat := 118140960795 + 6557118 * 2 ^ 59
def prefixEnd_6557118 : Nat := 4983230072969 + 3 ^ 40 * 6557118 * 2
def baseEnd_6557118 : Nat := 1122317747416060493123123

theorem tailTrace_6557118 : CollatzResearch.WordTrace tailWord_6557118 prefixEnd_6557118 1122317747416060493123123 := by
  unfold tailWord_6557118
  simp only [CollatzResearch.WordTrace]
  refine ⟨29894717632336103430297001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159438494039125884961584005 29894717632336103430297001)
  ·
    refine ⟨22421038224252077572722751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29894717632336103430297001 22421038224252077572722751)
    ·
      refine ⟨33631557336378116359084127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22421038224252077572722751 33631557336378116359084127)
      ·
        refine ⟨50447336004567174538626191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33631557336378116359084127 50447336004567174538626191)
        ·
          refine ⟨75671004006850761807939287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50447336004567174538626191 75671004006850761807939287)
          ·
            refine ⟨113506506010276142711908931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75671004006850761807939287 113506506010276142711908931)
            ·
              refine ⟨170259759015414214067863397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113506506010276142711908931 170259759015414214067863397)
              ·
                refine ⟨31923704815390165137724387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170259759015414214067863397 31923704815390165137724387)
                ·
                  refine ⟨47885557223085247706586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31923704815390165137724387 47885557223085247706586581)
                  ·
                    refine ⟨1122317747416060493123123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47885557223085247706586581 1122317747416060493123123)
                    ·
                      rfl

theorem cell23_6557118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_6557118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557118 prefixEnd_6557118 := by exact prefixLift 6557118
  have htrace : WordTrace (prefixWord ++ tailWord_6557118) baseStart_6557118 baseEnd_6557118 := by
    simpa [prefixWord, tailWord_6557118, baseEnd_6557118] using wordTrace_append hprefix tailTrace_6557118
  have hstable : (prefixWord ++ tailWord_6557118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557118).length < 2 ^ (prefixWord ++ tailWord_6557118).sum := by decide
  have hdescent : baseEnd_6557118 < baseStart_6557118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557190 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_6557190 : Nat := 118140960795 + 6557190 * 2 ^ 59
def prefixEnd_6557190 : Nat := 4983230072969 + 3 ^ 40 * 6557190 * 2
def baseEnd_6557190 : Nat := 374110023650589466407671

theorem tailTrace_6557190 : CollatzResearch.WordTrace tailWord_6557190 prefixEnd_6557190 374110023650589466407671 := by
  unfold tailWord_6557190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473761472325874491843657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159440244742951989159331349 7473761472325874491843657)
  ·
    refine ⟨5605321104244405868882743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7473761472325874491843657 5605321104244405868882743)
    ·
      refine ⟨8407981656366608803324115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605321104244405868882743 8407981656366608803324115)
      ·
        refine ⟨12611972484549913204986173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8407981656366608803324115 12611972484549913204986173)
        ·
          refine ⟨4729489681706217451869815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12611972484549913204986173 4729489681706217451869815)
          ·
            refine ⟨7094234522559326177804723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729489681706217451869815 7094234522559326177804723)
            ·
              refine ⟨10641351783838989266707085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094234522559326177804723 10641351783838989266707085)
              ·
                refine ⟨3990506918939620975015157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10641351783838989266707085 3990506918939620975015157)
                ·
                  refine ⟨374110023650589466407671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990506918939620975015157 374110023650589466407671)
                  ·
                    rfl

theorem cell23_6557190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_6557190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557190 prefixEnd_6557190 := by exact prefixLift 6557190
  have htrace : WordTrace (prefixWord ++ tailWord_6557190) baseStart_6557190 baseEnd_6557190 := by
    simpa [prefixWord, tailWord_6557190, baseEnd_6557190] using wordTrace_append hprefix tailTrace_6557190
  have hstable : (prefixWord ++ tailWord_6557190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557190).length < 2 ^ (prefixWord ++ tailWord_6557190).sum := by decide
  have hdescent : baseEnd_6557190 < baseStart_6557190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557216 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 1, 4]
def baseStart_6557216 : Nat := 118140960795 + 6557216 * 2 ^ 59
def prefixEnd_6557216 : Nat := 4983230072969 + 3 ^ 40 * 6557216 * 2
def baseEnd_6557216 : Nat := 1122334521117440698647973

theorem tailTrace_6557216 : CollatzResearch.WordTrace tailWord_6557216 prefixEnd_6557216 1122334521117440698647973 := by
  unfold tailWord_6557216
  simp only [CollatzResearch.WordTrace]
  refine ⟨119580657706166895089721751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159440876941555860119629001 119580657706166895089721751)
  ·
    refine ⟨179370986559250342634582627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119580657706166895089721751 179370986559250342634582627)
    ·
      refine ⟨269056479838875513951873941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179370986559250342634582627 269056479838875513951873941)
      ·
        refine ⟨12612022492447289716494091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 269056479838875513951873941 12612022492447289716494091)
        ·
          refine ⟨18918033738670934574741137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612022492447289716494091 18918033738670934574741137)
          ·
            refine ⟨14188525304003200931055853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18918033738670934574741137 14188525304003200931055853)
            ·
              refine ⟨5320696989001200349145945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14188525304003200931055853 5320696989001200349145945)
              ·
                refine ⟨3990522741750900261859459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320696989001200349145945 3990522741750900261859459)
                ·
                  refine ⟨5985784112626350392789189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990522741750900261859459 5985784112626350392789189)
                  ·
                    refine ⟨1122334521117440698647973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985784112626350392789189 1122334521117440698647973)
                    ·
                      rfl

theorem cell23_6557216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 4].length) (baseStart_6557216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557216 prefixEnd_6557216 := by exact prefixLift 6557216
  have htrace : WordTrace (prefixWord ++ tailWord_6557216) baseStart_6557216 baseEnd_6557216 := by
    simpa [prefixWord, tailWord_6557216, baseEnd_6557216] using wordTrace_append hprefix tailTrace_6557216
  have hstable : (prefixWord ++ tailWord_6557216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557216).length < 2 ^ (prefixWord ++ tailWord_6557216).sum := by decide
  have hdescent : baseEnd_6557216 < baseStart_6557216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557228 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_6557228 : Nat := 118140960795 + 6557228 * 2 ^ 59
def prefixEnd_6557228 : Nat := 4983230072969 + 3 ^ 40 * 6557228 * 2
def baseEnd_6557228 : Nat := 3367009725120176048993863

theorem tailTrace_6557228 : CollatzResearch.WordTrace tailWord_6557228 prefixEnd_6557228 3367009725120176048993863 := by
  unfold tailWord_6557228
  simp only [CollatzResearch.WordTrace]
  refine ⟨119580876544145158114440169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159441168725526877485920225 119580876544145158114440169)
  ·
    refine ⟨89685657408108868585830127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119580876544145158114440169 89685657408108868585830127)
    ·
      refine ⟨134528486112163302878745191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89685657408108868585830127 134528486112163302878745191)
      ·
        refine ⟨201792729168244954318117787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134528486112163302878745191 201792729168244954318117787)
        ·
          refine ⟨302689093752367431477176681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201792729168244954318117787 302689093752367431477176681)
          ·
            refine ⟨227016820314275573607882511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302689093752367431477176681 227016820314275573607882511)
            ·
              refine ⟨340525230471413360411823767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227016820314275573607882511 340525230471413360411823767)
              ·
                refine ⟨510787845707120040617735651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340525230471413360411823767 510787845707120040617735651)
                ·
                  refine ⟨766181768560680060926603477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510787845707120040617735651 766181768560680060926603477)
                  ·
                    refine ⟨17957385200640938927967269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 766181768560680060926603477 17957385200640938927967269)
                    ·
                      refine ⟨3367009725120176048993863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17957385200640938927967269 3367009725120176048993863)
                      ·
                        rfl

theorem cell23_6557228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_6557228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557228 prefixEnd_6557228 := by exact prefixLift 6557228
  have htrace : WordTrace (prefixWord ++ tailWord_6557228) baseStart_6557228 baseEnd_6557228 := by
    simpa [prefixWord, tailWord_6557228, baseEnd_6557228] using wordTrace_append hprefix tailTrace_6557228
  have hstable : (prefixWord ++ tailWord_6557228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557228).length < 2 ^ (prefixWord ++ tailWord_6557228).sum := by decide
  have hdescent : baseEnd_6557228 < baseStart_6557228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557249 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6557249 : Nat := 118140960795 + 6557249 * 2 ^ 59
def prefixEnd_6557249 : Nat := 4983230072969 + 3 ^ 40 * 6557249 * 2
def baseEnd_6557249 : Nat := 3367020508213920466831267

theorem tailTrace_6557249 : CollatzResearch.WordTrace tailWord_6557249 prefixEnd_6557249 3367020508213920466831267 := by
  unfold tailWord_6557249
  simp only [CollatzResearch.WordTrace]
  refine ⟨239162519021214236815394801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159441679347476157876929867 239162519021214236815394801)
  ·
    refine ⟨179371889265910677611546101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239162519021214236815394801 179371889265910677611546101)
    ·
      refine ⟨16816114618679126026082447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179371889265910677611546101 16816114618679126026082447)
      ·
        refine ⟨25224171928018689039123671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16816114618679126026082447 25224171928018689039123671)
        ·
          refine ⟨37836257892028033558685507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25224171928018689039123671 37836257892028033558685507)
          ·
            refine ⟨56754386838042050338028261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37836257892028033558685507 56754386838042050338028261)
            ·
              refine ⟨10641447532132884438380299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56754386838042050338028261 10641447532132884438380299)
              ·
                refine ⟨15962171298199326657570449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10641447532132884438380299 15962171298199326657570449)
                ·
                  refine ⟨11971628473649494993177837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15962171298199326657570449 11971628473649494993177837)
                  ·
                    refine ⟨4489360677618560622441689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11971628473649494993177837 4489360677618560622441689)
                    ·
                      refine ⟨3367020508213920466831267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489360677618560622441689 3367020508213920466831267)
                      ·
                        rfl

theorem cell23_6557249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6557249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557249 prefixEnd_6557249 := by exact prefixLift 6557249
  have htrace : WordTrace (prefixWord ++ tailWord_6557249) baseStart_6557249 baseEnd_6557249 := by
    simpa [prefixWord, tailWord_6557249, baseEnd_6557249] using wordTrace_append hprefix tailTrace_6557249
  have hstable : (prefixWord ++ tailWord_6557249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557249).length < 2 ^ (prefixWord ++ tailWord_6557249).sum := by decide
  have hdescent : baseEnd_6557249 < baseStart_6557249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557285 : List Nat := [1, 3, 1, 3, 3, 1, 3, 8]
def baseStart_6557285 : Nat := 118140960795 + 6557285 * 2 ^ 59
def prefixEnd_6557285 : Nat := 4983230072969 + 3 ^ 40 * 6557285 * 2
def baseEnd_6557285 : Nat := 124705147908054900962263

theorem tailTrace_6557285 : CollatzResearch.WordTrace tailWord_6557285 prefixEnd_6557285 124705147908054900962263 := by
  unfold tailWord_6557285
  simp only [CollatzResearch.WordTrace]
  refine ⟨239163832049083814963705309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159442554699389209975803539 239163832049083814963705309)
  ·
    refine ⟨89686437018406430611389491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239163832049083814963705309 89686437018406430611389491)
    ·
      refine ⟨134529655527609645917084237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89686437018406430611389491 134529655527609645917084237)
      ·
        refine ⟨50448620822853617218906589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134529655527609645917084237 50448620822853617218906589)
        ·
          refine ⟨18918232808570106457089971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50448620822853617218906589 18918232808570106457089971)
          ·
            refine ⟨28377349212855159685634957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18918232808570106457089971 28377349212855159685634957)
            ·
              refine ⟨10641505954820684882113109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28377349212855159685634957 10641505954820684882113109)
              ·
                refine ⟨124705147908054900962263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10641505954820684882113109 124705147908054900962263)
                ·
                  rfl

theorem cell23_6557285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 8].length) (baseStart_6557285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557285 prefixEnd_6557285 := by exact prefixLift 6557285
  have htrace : WordTrace (prefixWord ++ tailWord_6557285) baseStart_6557285 baseEnd_6557285 := by
    simpa [prefixWord, tailWord_6557285, baseEnd_6557285] using wordTrace_append hprefix tailTrace_6557285
  have hstable : (prefixWord ++ tailWord_6557285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557285).length < 2 ^ (prefixWord ++ tailWord_6557285).sum := by decide
  have hdescent : baseEnd_6557285 < baseStart_6557285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557312 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3]
def baseStart_6557312 : Nat := 118140960795 + 6557312 * 2 ^ 59
def prefixEnd_6557312 : Nat := 4983230072969 + 3 ^ 40 * 6557312 * 2
def baseEnd_6557312 : Nat := 3367052857495153720343477

theorem tailTrace_6557312 : CollatzResearch.WordTrace tailWord_6557312 prefixEnd_6557312 3367052857495153720343477 := by
  unfold tailWord_6557312
  simp only [CollatzResearch.WordTrace]
  refine ⟨119582408409992999287469095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159443211213323999049958793 119582408409992999287469095)
  ·
    refine ⟨179373612614989498931203643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119582408409992999287469095 179373612614989498931203643)
    ·
      refine ⟨269060418922484248396805465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179373612614989498931203643 269060418922484248396805465)
      ·
        refine ⟨201795314191863186297604099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269060418922484248396805465 201795314191863186297604099)
        ·
          refine ⟨302692971287794779446406149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201795314191863186297604099 302692971287794779446406149)
          ·
            refine ⟨56754932116461521146201153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302692971287794779446406149 56754932116461521146201153)
            ·
              refine ⟨42566199087346140859650865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56754932116461521146201153 42566199087346140859650865)
              ·
                refine ⟨31924649315509605644738149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42566199087346140859650865 31924649315509605644738149)
                ·
                  refine ⟨5985871746658051058388403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31924649315509605644738149 5985871746658051058388403)
                  ·
                    refine ⟨8978807619987076587582605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5985871746658051058388403 8978807619987076587582605)
                    ·
                      refine ⟨3367052857495153720343477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8978807619987076587582605 3367052857495153720343477)
                      ·
                        rfl

theorem cell23_6557312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_6557312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557312 prefixEnd_6557312 := by exact prefixLift 6557312
  have htrace : WordTrace (prefixWord ++ tailWord_6557312) baseStart_6557312 baseEnd_6557312 := by
    simpa [prefixWord, tailWord_6557312, baseEnd_6557312] using wordTrace_append hprefix tailTrace_6557312
  have hstable : (prefixWord ++ tailWord_6557312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557312).length < 2 ^ (prefixWord ++ tailWord_6557312).sum := by decide
  have hdescent : baseEnd_6557312 < baseStart_6557312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557313 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_6557313 : Nat := 118140960795 + 6557313 * 2 ^ 59
def prefixEnd_6557313 : Nat := 4983230072969 + 3 ^ 40 * 6557313 * 2
def baseEnd_6557313 : Nat := 3367053370975808216430973

theorem tailTrace_6557313 : CollatzResearch.WordTrace tailWord_6557313 prefixEnd_6557313 3367053370975808216430973 := by
  unfold tailWord_6557313
  simp only [CollatzResearch.WordTrace]
  refine ⟨239164853292982375745724593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159443235528654917163816395 239164853292982375745724593)
  ·
    refine ⟨179373639969736781809293445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239164853292982375745724593 179373639969736781809293445)
    ·
      refine ⟨33632557494325646589242521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179373639969736781809293445 33632557494325646589242521)
      ·
        refine ⟨25224418120744234941931891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33632557494325646589242521 25224418120744234941931891)
        ·
          refine ⟨37836627181116352412897837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25224418120744234941931891 37836627181116352412897837)
          ·
            refine ⟨14188735192918632154836689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37836627181116352412897837 14188735192918632154836689)
            ·
              refine ⟨10641551394688974116127517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14188735192918632154836689 10641551394688974116127517)
              ·
                refine ⟨3990581773008365293547819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10641551394688974116127517 3990581773008365293547819)
                ·
                  refine ⟨5985872659512547940321729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990581773008365293547819 5985872659512547940321729)
                  ·
                    refine ⟨4489404494634410955241297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5985872659512547940321729 4489404494634410955241297)
                    ·
                      refine ⟨3367053370975808216430973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489404494634410955241297 3367053370975808216430973)
                      ·
                        rfl

theorem cell23_6557313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_6557313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557313 prefixEnd_6557313 := by exact prefixLift 6557313
  have htrace : WordTrace (prefixWord ++ tailWord_6557313) baseStart_6557313 baseEnd_6557313 := by
    simpa [prefixWord, tailWord_6557313, baseEnd_6557313] using wordTrace_append hprefix tailTrace_6557313
  have hstable : (prefixWord ++ tailWord_6557313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557313).length < 2 ^ (prefixWord ++ tailWord_6557313).sum := by decide
  have hdescent : baseEnd_6557313 < baseStart_6557313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557369 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6557369 : Nat := 118140960795 + 6557369 * 2 ^ 59
def prefixEnd_6557369 : Nat := 4983230072969 + 3 ^ 40 * 6557369 * 2
def baseEnd_6557369 : Nat := 3367082125892459997330715

theorem tailTrace_6557369 : CollatzResearch.WordTrace tailWord_6557369 prefixEnd_6557369 3367082125892459997330715 := by
  unfold tailWord_6557369
  simp only [CollatzResearch.WordTrace]
  refine ⟨239166895780779497309763161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159444597187186331539842107 239166895780779497309763161)
  ·
    refine ⟨179375171835584622982322371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239166895780779497309763161 179375171835584622982322371)
    ·
      refine ⟨269062757753376934473483557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179375171835584622982322371 269062757753376934473483557)
      ·
        refine ⟨50449267078758175213778167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269062757753376934473483557 50449267078758175213778167)
        ·
          refine ⟨75673900618137262820667251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50449267078758175213778167 75673900618137262820667251)
          ·
            refine ⟨113510850927205894231000877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75673900618137262820667251 113510850927205894231000877)
            ·
              refine ⟨42566569097702210336625329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113510850927205894231000877 42566569097702210336625329)
              ·
                refine ⟨31924926823276657752468997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42566569097702210336625329 31924926823276657752468997)
                ·
                  refine ⟨5985923779364373328587937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31924926823276657752468997 5985923779364373328587937)
                  ·
                    refine ⟨4489442834523279996440953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5985923779364373328587937 4489442834523279996440953)
                    ·
                      refine ⟨3367082125892459997330715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489442834523279996440953 3367082125892459997330715)
                      ·
                        rfl

theorem cell23_6557369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6557369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557369 prefixEnd_6557369 := by exact prefixLift 6557369
  have htrace : WordTrace (prefixWord ++ tailWord_6557369) baseStart_6557369 baseEnd_6557369 := by
    simpa [prefixWord, tailWord_6557369, baseEnd_6557369] using wordTrace_append hprefix tailTrace_6557369
  have hstable : (prefixWord ++ tailWord_6557369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557369).length < 2 ^ (prefixWord ++ tailWord_6557369).sum := by decide
  have hdescent : baseEnd_6557369 < baseStart_6557369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557372 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6557372 : Nat := 118140960795 + 6557372 * 2 ^ 59
def prefixEnd_6557372 : Nat := 4983230072969 + 3 ^ 40 * 6557372 * 2
def baseEnd_6557372 : Nat := 3367083666334423485593201

theorem tailTrace_6557372 : CollatzResearch.WordTrace tailWord_6557372 prefixEnd_6557372 3367083666334423485593201 := by
  unfold tailWord_6557372
  simp only [CollatzResearch.WordTrace]
  refine ⟨119583502599884314411061185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159444670133179085881414913 119583502599884314411061185)
  ·
    refine ⟨89687626949913235808295889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119583502599884314411061185 89687626949913235808295889)
    ·
      refine ⟨67265720212434926856221917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89687626949913235808295889 67265720212434926856221917)
      ·
        refine ⟨25224645079663097571083219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67265720212434926856221917 25224645079663097571083219)
        ·
          refine ⟨37836967619494646356624829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25224645079663097571083219 37836967619494646356624829)
          ·
            refine ⟨14188862857310492383734311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37836967619494646356624829 14188862857310492383734311)
            ·
              refine ⟨21283294285965738575601467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14188862857310492383734311 21283294285965738575601467)
              ·
                refine ⟨31924941428948607863402201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21283294285965738575601467 31924941428948607863402201)
                ·
                  refine ⟨23943706071711455897551651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31924941428948607863402201 23943706071711455897551651)
                  ·
                    refine ⟨35915559107567183846327477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23943706071711455897551651 35915559107567183846327477)
                    ·
                      refine ⟨3367083666334423485593201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35915559107567183846327477 3367083666334423485593201)
                      ·
                        rfl

theorem cell23_6557372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6557372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557372 prefixEnd_6557372 := by exact prefixLift 6557372
  have htrace : WordTrace (prefixWord ++ tailWord_6557372) baseStart_6557372 baseEnd_6557372 := by
    simpa [prefixWord, tailWord_6557372, baseEnd_6557372] using wordTrace_append hprefix tailTrace_6557372
  have hstable : (prefixWord ++ tailWord_6557372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557372).length < 2 ^ (prefixWord ++ tailWord_6557372).sum := by decide
  have hdescent : baseEnd_6557372 < baseStart_6557372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557455 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_6557455 : Nat := 118140960795 + 6557455 * 2 ^ 59
def prefixEnd_6557455 : Nat := 4983230072969 + 3 ^ 40 * 6557455 * 2
def baseEnd_6557455 : Nat := 3367126285228746660855319

theorem tailTrace_6557455 : CollatzResearch.WordTrace tailWord_6557455 prefixEnd_6557455 3367126285228746660855319 := by
  unfold tailWord_6557455
  simp only [CollatzResearch.WordTrace]
  refine ⟨239170032458467933997393819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159446688305645289331595879 239170032458467933997393819)
  ·
    refine ⟨358755048687701900996090729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239170032458467933997393819 358755048687701900996090729)
    ·
      refine ⟨269066286515776425747068047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358755048687701900996090729 269066286515776425747068047)
      ·
        refine ⟨403599429773664638620602071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269066286515776425747068047 403599429773664638620602071)
        ·
          refine ⟨605399144660496957930903107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403599429773664638620602071 605399144660496957930903107)
          ·
            refine ⟨908098716990745436896354661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605399144660496957930903107 908098716990745436896354661)
            ·
              refine ⟨170268509435764769418066499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 908098716990745436896354661 170268509435764769418066499)
              ·
                refine ⟨255402764153647154127099749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170268509435764769418066499 255402764153647154127099749)
                ·
                  refine ⟨47888018278808841398831203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255402764153647154127099749 47888018278808841398831203)
                  ·
                    refine ⟨71832027418213262098246805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47888018278808841398831203 71832027418213262098246805)
                    ·
                      refine ⟨3367126285228746660855319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71832027418213262098246805 3367126285228746660855319)
                      ·
                        rfl

theorem cell23_6557455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_6557455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557455 prefixEnd_6557455 := by exact prefixLift 6557455
  have htrace : WordTrace (prefixWord ++ tailWord_6557455) baseStart_6557455 baseEnd_6557455 := by
    simpa [prefixWord, tailWord_6557455, baseEnd_6557455] using wordTrace_append hprefix tailTrace_6557455
  have hstable : (prefixWord ++ tailWord_6557455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557455).length < 2 ^ (prefixWord ++ tailWord_6557455).sum := by decide
  have hdescent : baseEnd_6557455 < baseStart_6557455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557476 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_6557476 : Nat := 118140960795 + 6557476 * 2 ^ 59
def prefixEnd_6557476 : Nat := 4983230072969 + 3 ^ 40 * 6557476 * 2
def baseEnd_6557476 : Nat := 3367137068322491078692723

theorem tailTrace_6557476 : CollatzResearch.WordTrace tailWord_6557476 prefixEnd_6557476 3367137068322491078692723 := by
  unfold tailWord_6557476
  simp only [CollatzResearch.WordTrace]
  refine ⟨119585399195695927291954141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159447198927594569722605521 119585399195695927291954141)
  ·
    refine ⟨44844524698385972734482803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119585399195695927291954141 44844524698385972734482803)
    ·
      refine ⟨67266787047578959101724205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44844524698385972734482803 67266787047578959101724205)
      ·
        refine ⟨25225045142842109663146577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67266787047578959101724205 25225045142842109663146577)
        ·
          refine ⟨18918783857131582247359933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25225045142842109663146577 18918783857131582247359933)
          ·
            refine ⟨7094543946424343342759975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18918783857131582247359933 7094543946424343342759975)
            ·
              refine ⟨10641815919636515014139963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094543946424343342759975 10641815919636515014139963)
              ·
                refine ⟨15962723879454772521209945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10641815919636515014139963 15962723879454772521209945)
                ·
                  refine ⟨11972042909591079390907459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15962723879454772521209945 11972042909591079390907459)
                  ·
                    refine ⟨17958064364386619086361189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11972042909591079390907459 17958064364386619086361189)
                    ·
                      refine ⟨3367137068322491078692723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17958064364386619086361189 3367137068322491078692723)
                      ·
                        rfl

theorem cell23_6557476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_6557476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557476 prefixEnd_6557476 := by exact prefixLift 6557476
  have htrace : WordTrace (prefixWord ++ tailWord_6557476) baseStart_6557476 baseEnd_6557476 := by
    simpa [prefixWord, tailWord_6557476, baseEnd_6557476] using wordTrace_append hprefix tailTrace_6557476
  have hstable : (prefixWord ++ tailWord_6557476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557476).length < 2 ^ (prefixWord ++ tailWord_6557476).sum := by decide
  have hdescent : baseEnd_6557476 < baseStart_6557476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557516 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 6]
def baseStart_6557516 : Nat := 118140960795 + 6557516 * 2 ^ 59
def prefixEnd_6557516 : Nat := 4983230072969 + 3 ^ 40 * 6557516 * 2
def baseEnd_6557516 : Nat := 374128623060963435799171

theorem tailTrace_6557516 : CollatzResearch.WordTrace tailWord_6557516 prefixEnd_6557516 374128623060963435799171 := by
  unfold tailWord_6557516
  simp only [CollatzResearch.WordTrace]
  refine ⟨119586128655623470707682201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159448171540831294276909601 119586128655623470707682201)
  ·
    refine ⟨89689596491717603030761651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119586128655623470707682201 89689596491717603030761651)
    ·
      refine ⟨134534394737576404546142477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89689596491717603030761651 134534394737576404546142477)
      ·
        refine ⟨50450398026591151704803429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134534394737576404546142477 50450398026591151704803429)
        ·
          refine ⟨9459449629985840944650643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50450398026591151704803429 9459449629985840944650643)
          ·
            refine ⟨14189174444978761416975965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9459449629985840944650643 14189174444978761416975965)
            ·
              refine ⟨5320940416867035531365987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14189174444978761416975965 5320940416867035531365987)
              ·
                refine ⟨7981410625300553297048981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320940416867035531365987 7981410625300553297048981)
                ·
                  refine ⟨374128623060963435799171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7981410625300553297048981 374128623060963435799171)
                  ·
                    rfl

theorem cell23_6557516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_6557516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557516 prefixEnd_6557516 := by exact prefixLift 6557516
  have htrace : WordTrace (prefixWord ++ tailWord_6557516) baseStart_6557516 baseEnd_6557516 := by
    simpa [prefixWord, tailWord_6557516, baseEnd_6557516] using wordTrace_append hprefix tailTrace_6557516
  have hstable : (prefixWord ++ tailWord_6557516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557516).length < 2 ^ (prefixWord ++ tailWord_6557516).sum := by decide
  have hdescent : baseEnd_6557516 < baseStart_6557516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557529 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_6557529 : Nat := 118140960795 + 6557529 * 2 ^ 59
def prefixEnd_6557529 : Nat := 4983230072969 + 3 ^ 40 * 6557529 * 2
def baseEnd_6557529 : Nat := 1122388094265726457109993

theorem tailTrace_6557529 : CollatzResearch.WordTrace tailWord_6557529 prefixEnd_6557529 1122388094265726457109993 := by
  unfold tailWord_6557529
  simp only [CollatzResearch.WordTrace]
  refine ⟨239172731460199844635587641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159448487640133229757058427 239172731460199844635587641)
  ·
    refine ⟨179379548595149883476690731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239172731460199844635587641 179379548595149883476690731)
    ·
      refine ⟨269069322892724825215036097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179379548595149883476690731 269069322892724825215036097)
      ·
        refine ⟨201801992169543618911277073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269069322892724825215036097 201801992169543618911277073)
        ·
          refine ⟨151351494127157714183457805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201801992169543618911277073 151351494127157714183457805)
          ·
            refine ⟨56756810297684142818796677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151351494127157714183457805 56756810297684142818796677)
            ·
              refine ⟨10641901930815776778524377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56756810297684142818796677 10641901930815776778524377)
              ·
                refine ⟨7981426448111832583893283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10641901930815776778524377 7981426448111832583893283)
                ·
                  refine ⟨11972139672167748875839925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7981426448111832583893283 11972139672167748875839925)
                  ·
                    refine ⟨1122388094265726457109993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11972139672167748875839925 1122388094265726457109993)
                    ·
                      rfl

theorem cell23_6557529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_6557529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557529 prefixEnd_6557529 := by exact prefixLift 6557529
  have htrace : WordTrace (prefixWord ++ tailWord_6557529) baseStart_6557529 baseEnd_6557529 := by
    simpa [prefixWord, tailWord_6557529, baseEnd_6557529] using wordTrace_append hprefix tailTrace_6557529
  have hstable : (prefixWord ++ tailWord_6557529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557529).length < 2 ^ (prefixWord ++ tailWord_6557529).sum := by decide
  have hdescent : baseEnd_6557529 < baseStart_6557529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557562 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_6557562 : Nat := 118140960795 + 6557562 * 2 ^ 59
def prefixEnd_6557562 : Nat := 4983230072969 + 3 ^ 40 * 6557562 * 2
def baseEnd_6557562 : Nat := 3367181227658777742217327

theorem tailTrace_6557562 : CollatzResearch.WordTrace tailWord_6557562 prefixEnd_6557562 3367181227658777742217327 := by
  unfold tailWord_6557562
  simp only [CollatzResearch.WordTrace]
  refine ⟨59793483767270072817884735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159449290046053527514359293 59793483767270072817884735)
  ·
    refine ⟨89690225650905109226827103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59793483767270072817884735 89690225650905109226827103)
    ·
      refine ⟨134535338476357663840240655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89690225650905109226827103 134535338476357663840240655)
      ·
        refine ⟨201803007714536495760360983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134535338476357663840240655 201803007714536495760360983)
        ·
          refine ⟨302704511571804743640541475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201803007714536495760360983 302704511571804743640541475)
          ·
            refine ⟨454056767357707115460812213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302704511571804743640541475 454056767357707115460812213)
            ·
              refine ⟨42567821939785042074451145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 454056767357707115460812213 42567821939785042074451145)
              ·
                refine ⟨31925866454838781555838359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42567821939785042074451145 31925866454838781555838359)
                ·
                  refine ⟨47888799682258172333757539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31925866454838781555838359 47888799682258172333757539)
                  ·
                    refine ⟨71833199523387258500636309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47888799682258172333757539 71833199523387258500636309)
                    ·
                      refine ⟨3367181227658777742217327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71833199523387258500636309 3367181227658777742217327)
                      ·
                        rfl

theorem cell23_6557562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_6557562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557562 prefixEnd_6557562 := by exact prefixLift 6557562
  have htrace : WordTrace (prefixWord ++ tailWord_6557562) baseStart_6557562 baseEnd_6557562 := by
    simpa [prefixWord, tailWord_6557562, baseEnd_6557562] using wordTrace_append hprefix tailTrace_6557562
  have hstable : (prefixWord ++ tailWord_6557562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557562).length < 2 ^ (prefixWord ++ tailWord_6557562).sum := by decide
  have hdescent : baseEnd_6557562 < baseStart_6557562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557572 : List Nat := [2, 3, 2, 1, 1, 1, 3, 10]
def baseStart_6557572 : Nat := 118140960795 + 6557572 * 2 ^ 59
def prefixEnd_6557572 : Nat := 4983230072969 + 3 ^ 40 * 6557572 * 2
def baseEnd_6557572 : Nat := 124710606017234174188603

theorem tailTrace_6557572 : CollatzResearch.WordTrace tailWord_6557572 prefixEnd_6557572 124710606017234174188603 := by
  unfold tailWord_6557572
  simp only [CollatzResearch.WordTrace]
  refine ⟨119587149899522031489701485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159449533199362708652935313 119587149899522031489701485)
  ·
    refine ⟨44845181212320761808638057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119587149899522031489701485 44845181212320761808638057)
    ·
      refine ⟨33633885909240571356478543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44845181212320761808638057 33633885909240571356478543)
      ·
        refine ⟨50450828863860857034717815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33633885909240571356478543 50450828863860857034717815)
        ·
          refine ⟨75676243295791285552076723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50450828863860857034717815 75676243295791285552076723)
          ·
            refine ⟨113514364943686928328115085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75676243295791285552076723 113514364943686928328115085)
            ·
              refine ⟨42567886853882598123043157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113514364943686928328115085 42567886853882598123043157)
              ·
                refine ⟨124710606017234174188603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42567886853882598123043157 124710606017234174188603)
                ·
                  rfl

theorem cell23_6557572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 10].length) (baseStart_6557572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557572 prefixEnd_6557572 := by exact prefixLift 6557572
  have htrace : WordTrace (prefixWord ++ tailWord_6557572) baseStart_6557572 baseEnd_6557572 := by
    simpa [prefixWord, tailWord_6557572, baseEnd_6557572] using wordTrace_append hprefix tailTrace_6557572
  have hstable : (prefixWord ++ tailWord_6557572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557572).length < 2 ^ (prefixWord ++ tailWord_6557572).sum := by decide
  have hdescent : baseEnd_6557572 < baseStart_6557572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557596 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6557596 : Nat := 118140960795 + 6557596 * 2 ^ 59
def prefixEnd_6557596 : Nat := 4983230072969 + 3 ^ 40 * 6557596 * 2
def baseEnd_6557596 : Nat := 3367198686001030609192171

theorem tailTrace_6557596 : CollatzResearch.WordTrace tailWord_6557596 prefixEnd_6557596 3367198686001030609192171 := by
  unfold tailWord_6557596
  simp only [CollatzResearch.WordTrace]
  refine ⟨119587587575478557539138321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159450116767304743385517761 119587587575478557539138321)
  ·
    refine ⟨89690690681608918154353741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119587587575478557539138321 89690690681608918154353741)
    ·
      refine ⟨33634009005603344307882653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89690690681608918154353741 33634009005603344307882653)
      ·
        refine ⟨12612753377101254115455995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33634009005603344307882653 12612753377101254115455995)
        ·
          refine ⟨18919130065651881173183993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612753377101254115455995 18919130065651881173183993)
          ·
            refine ⟨14189347549238910879887995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18919130065651881173183993 14189347549238910879887995)
            ·
              refine ⟨21284021323858366319831993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14189347549238910879887995 21284021323858366319831993)
              ·
                refine ⟨15963015992893774739873995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21284021323858366319831993 15963015992893774739873995)
                ·
                  refine ⟨23944523989340662109810993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15963015992893774739873995 23944523989340662109810993)
                  ·
                    refine ⟨17958392992005496582358245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23944523989340662109810993 17958392992005496582358245)
                    ·
                      refine ⟨3367198686001030609192171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17958392992005496582358245 3367198686001030609192171)
                      ·
                        rfl

theorem cell23_6557596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6557596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557596 prefixEnd_6557596 := by exact prefixLift 6557596
  have htrace : WordTrace (prefixWord ++ tailWord_6557596) baseStart_6557596 baseEnd_6557596 := by
    simpa [prefixWord, tailWord_6557596, baseEnd_6557596] using wordTrace_append hprefix tailTrace_6557596
  have hstable : (prefixWord ++ tailWord_6557596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557596).length < 2 ^ (prefixWord ++ tailWord_6557596).sum := by decide
  have hdescent : baseEnd_6557596 < baseStart_6557596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557617 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6557617 : Nat := 118140960795 + 6557617 * 2 ^ 59
def prefixEnd_6557617 : Nat := 4983230072969 + 3 ^ 40 * 6557617 * 2
def baseEnd_6557617 : Nat := 3367209469094775027029575

theorem tailTrace_6557617 : CollatzResearch.WordTrace tailWord_6557617 prefixEnd_6557617 3367209469094775027029575 := by
  unfold tailWord_6557617
  simp only [CollatzResearch.WordTrace]
  refine ⟨239175941083881035664791105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159450627389254023776527403 239175941083881035664791105)
  ·
    refine ⟨179381955812910776748593329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239175941083881035664791105 179381955812910776748593329)
    ·
      refine ⟨134536466859683082561444997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179381955812910776748593329 134536466859683082561444997)
      ·
        refine ⟨25225587536190577980270937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134536466859683082561444997 25225587536190577980270937)
        ·
          refine ⟨18919190652142933485203203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25225587536190577980270937 18919190652142933485203203)
          ·
            refine ⟨28378785978214400227804805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18919190652142933485203203 28378785978214400227804805)
            ·
              refine ⟨5321022370915200042713401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28378785978214400227804805 5321022370915200042713401)
              ·
                refine ⟨3990766778186400032035051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5321022370915200042713401 3990766778186400032035051)
                ·
                  refine ⟨5986150167279600048052577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990766778186400032035051 5986150167279600048052577)
                  ·
                    refine ⟨4489612625459700036039433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5986150167279600048052577 4489612625459700036039433)
                    ·
                      refine ⟨3367209469094775027029575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489612625459700036039433 3367209469094775027029575)
                      ·
                        rfl

theorem cell23_6557617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6557617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557617 prefixEnd_6557617 := by exact prefixLift 6557617
  have htrace : WordTrace (prefixWord ++ tailWord_6557617) baseStart_6557617 baseEnd_6557617 := by
    simpa [prefixWord, tailWord_6557617, baseEnd_6557617] using wordTrace_append hprefix tailTrace_6557617
  have hstable : (prefixWord ++ tailWord_6557617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557617).length < 2 ^ (prefixWord ++ tailWord_6557617).sum := by decide
  have hdescent : baseEnd_6557617 < baseStart_6557617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557654 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_6557654 : Nat := 118140960795 + 6557654 * 2 ^ 59
def prefixEnd_6557654 : Nat := 4983230072969 + 3 ^ 40 * 6557654 * 2
def baseEnd_6557654 : Nat := 3367228467878991382266905

theorem tailTrace_6557654 : CollatzResearch.WordTrace tailWord_6557654 prefixEnd_6557654 3367228467878991382266905 := by
  unfold tailWord_6557654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14948580661546686936493001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159451527056497993989258677 14948580661546686936493001)
  ·
    refine ⟨11211435496160015202369751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14948580661546686936493001 11211435496160015202369751)
    ·
      refine ⟨16817153244240022803554627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11211435496160015202369751 16817153244240022803554627)
      ·
        refine ⟨25225729866360034205331941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16817153244240022803554627 25225729866360034205331941)
        ·
          refine ⟨4729824349942506413499739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25225729866360034205331941 4729824349942506413499739)
          ·
            refine ⟨7094736524913759620249609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729824349942506413499739 7094736524913759620249609)
            ·
              refine ⟨5321052393685319715187207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7094736524913759620249609 5321052393685319715187207)
              ·
                refine ⟨7981578590527979572780811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321052393685319715187207 7981578590527979572780811)
                ·
                  refine ⟨11972367885791969359171217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7981578590527979572780811 11972367885791969359171217)
                  ·
                    refine ⟨8979275914343977019378413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11972367885791969359171217 8979275914343977019378413)
                    ·
                      refine ⟨3367228467878991382266905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8979275914343977019378413 3367228467878991382266905)
                      ·
                        rfl

theorem cell23_6557654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_6557654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557654 prefixEnd_6557654 := by exact prefixLift 6557654
  have htrace : WordTrace (prefixWord ++ tailWord_6557654) baseStart_6557654 baseEnd_6557654 := by
    simpa [prefixWord, tailWord_6557654, baseEnd_6557654] using wordTrace_append hprefix tailTrace_6557654
  have hstable : (prefixWord ++ tailWord_6557654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557654).length < 2 ^ (prefixWord ++ tailWord_6557654).sum := by decide
  have hdescent : baseEnd_6557654 < baseStart_6557654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557656 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_6557656 : Nat := 118140960795 + 6557656 * 2 ^ 59
def prefixEnd_6557656 : Nat := 4983230072969 + 3 ^ 40 * 6557656 * 2
def baseEnd_6557656 : Nat := 3367229494840300374441895

theorem tailTrace_6557656 : CollatzResearch.WordTrace tailWord_6557656 prefixEnd_6557656 3367229494840300374441895 := by
  unfold tailWord_6557656
  simp only [CollatzResearch.WordTrace]
  refine ⟨119588681765369872662730411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159451575687159830216973881 119588681765369872662730411)
  ·
    refine ⟨179383022648054808994095617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119588681765369872662730411 179383022648054808994095617)
    ·
      refine ⟨134537266986041106745571713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179383022648054808994095617 134537266986041106745571713)
      ·
        refine ⟨100902950239530830059178785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134537266986041106745571713 100902950239530830059178785)
        ·
          refine ⟨75677212679648122544384089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100902950239530830059178785 75677212679648122544384089)
          ·
            refine ⟨56757909509736091908288067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75677212679648122544384089 56757909509736091908288067)
            ·
              refine ⟨85136864264604137862432101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56757909509736091908288067 85136864264604137862432101)
              ·
                refine ⟨15963162049613275849206019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85136864264604137862432101 15963162049613275849206019)
                ·
                  refine ⟨23944743074419913773809029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15963162049613275849206019 23944743074419913773809029)
                  ·
                    refine ⟨4489639326453733832589193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23944743074419913773809029 4489639326453733832589193)
                    ·
                      refine ⟨3367229494840300374441895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489639326453733832589193 3367229494840300374441895)
                      ·
                        rfl

theorem cell23_6557656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_6557656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557656 prefixEnd_6557656 := by exact prefixLift 6557656
  have htrace : WordTrace (prefixWord ++ tailWord_6557656) baseStart_6557656 baseEnd_6557656 := by
    simpa [prefixWord, tailWord_6557656, baseEnd_6557656] using wordTrace_append hprefix tailTrace_6557656
  have hstable : (prefixWord ++ tailWord_6557656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557656).length < 2 ^ (prefixWord ++ tailWord_6557656).sum := by decide
  have hdescent : baseEnd_6557656 < baseStart_6557656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557679 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 7]
def baseStart_6557679 : Nat := 118140960795 + 6557679 * 2 ^ 59
def prefixEnd_6557679 : Nat := 4983230072969 + 3 ^ 40 * 6557679 * 2
def baseEnd_6557679 : Nat := 374137922766150420494921

theorem tailTrace_6557679 : CollatzResearch.WordTrace tailWord_6557679 prefixEnd_6557679 374137922766150420494921 := by
  unfold tailWord_6557679
  simp only [CollatzResearch.WordTrace]
  refine ⟨239178202409656420253548091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159452134939770946835698727 239178202409656420253548091)
  ·
    refine ⟨358767303614484630380322137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239178202409656420253548091 358767303614484630380322137)
    ·
      refine ⟨269075477710863472785241603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358767303614484630380322137 269075477710863472785241603)
      ·
        refine ⟨403613216566295209177862405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269075477710863472785241603 403613216566295209177862405)
        ·
          refine ⟨75677478106180351720849201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403613216566295209177862405 75677478106180351720849201)
          ·
            refine ⟨56758108579635263790636901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75677478106180351720849201 56758108579635263790636901)
            ·
              refine ⟨10642145358681611960744419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56758108579635263790636901 10642145358681611960744419)
              ·
                refine ⟨15963218038022417941116629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10642145358681611960744419 15963218038022417941116629)
                ·
                  refine ⟨374137922766150420494921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15963218038022417941116629 374137922766150420494921)
                  ·
                    rfl

theorem cell23_6557679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 7].length) (baseStart_6557679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557679 prefixEnd_6557679 := by exact prefixLift 6557679
  have htrace : WordTrace (prefixWord ++ tailWord_6557679) baseStart_6557679 baseEnd_6557679 := by
    simpa [prefixWord, tailWord_6557679, baseEnd_6557679] using wordTrace_append hprefix tailTrace_6557679
  have hstable : (prefixWord ++ tailWord_6557679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557679).length < 2 ^ (prefixWord ++ tailWord_6557679).sum := by decide
  have hdescent : baseEnd_6557679 < baseStart_6557679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557756 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_6557756 : Nat := 118140960795 + 6557756 * 2 ^ 59
def prefixEnd_6557756 : Nat := 4983230072969 + 3 ^ 40 * 6557756 * 2
def baseEnd_6557756 : Nat := 1122426947635249994397145

theorem tailTrace_6557756 : CollatzResearch.WordTrace tailWord_6557756 prefixEnd_6557756 1122426947635249994397145 := by
  unfold tailWord_6557756
  simp only [CollatzResearch.WordTrace]
  refine ⟨119590505415188731202050561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159454007220251641602734081 119590505415188731202050561)
  ·
    refine ⟨89692879061391548401537921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119590505415188731202050561 89692879061391548401537921)
    ·
      refine ⟨67269659296043661301153441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89692879061391548401537921 67269659296043661301153441)
      ·
        refine ⟨50452244472032745975865081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67269659296043661301153441 50452244472032745975865081)
        ·
          refine ⟨37839183354024559481898811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50452244472032745975865081 37839183354024559481898811)
          ·
            refine ⟨56758775031036839222848217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37839183354024559481898811 56758775031036839222848217)
            ·
              refine ⟨42569081273277629417136163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56758775031036839222848217 42569081273277629417136163)
              ·
                refine ⟨63853621909916444125704245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42569081273277629417136163 63853621909916444125704245)
                ·
                  refine ⟨5986277054054666636784773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63853621909916444125704245 5986277054054666636784773)
                  ·
                    refine ⟨1122426947635249994397145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986277054054666636784773 1122426947635249994397145)
                    ·
                      rfl

theorem cell23_6557756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_6557756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557756 prefixEnd_6557756 := by exact prefixLift 6557756
  have htrace : WordTrace (prefixWord ++ tailWord_6557756) baseStart_6557756 baseEnd_6557756 := by
    simpa [prefixWord, tailWord_6557756, baseEnd_6557756] using wordTrace_append hprefix tailTrace_6557756
  have hstable : (prefixWord ++ tailWord_6557756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557756).length < 2 ^ (prefixWord ++ tailWord_6557756).sum := by decide
  have hdescent : baseEnd_6557756 < baseStart_6557756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557759 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_6557759 : Nat := 118140960795 + 6557759 * 2 ^ 59
def prefixEnd_6557759 : Nat := 4983230072969 + 3 ^ 40 * 6557759 * 2
def baseEnd_6557759 : Nat := 3367282383347713471453921

theorem tailTrace_6557759 : CollatzResearch.WordTrace tailWord_6557759 prefixEnd_6557759 3367282383347713471453921 := by
  unfold tailWord_6557759
  simp only [CollatzResearch.WordTrace]
  refine ⟨239181120249366593916460331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159454080166244395944306887 239181120249366593916460331)
  ·
    refine ⟨358771680374049890874690497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239181120249366593916460331 358771680374049890874690497)
    ·
      refine ⟨269078760280537418156017873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358771680374049890874690497 269078760280537418156017873)
      ·
        refine ⟨201809070210403063617013405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269078760280537418156017873 201809070210403063617013405)
        ·
          refine ⟨75678401328901148856380027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201809070210403063617013405 75678401328901148856380027)
          ·
            refine ⟨113517601993351723284570041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75678401328901148856380027 113517601993351723284570041)
            ·
              refine ⟨85138201495013792463427531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113517601993351723284570041 85138201495013792463427531)
              ·
                refine ⟨127707302242520688695141297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85138201495013792463427531 127707302242520688695141297)
                ·
                  refine ⟨95780476681890516521355973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127707302242520688695141297 95780476681890516521355973)
                  ·
                    refine ⟨17958839377854471847754245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95780476681890516521355973 17958839377854471847754245)
                    ·
                      refine ⟨3367282383347713471453921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17958839377854471847754245 3367282383347713471453921)
                      ·
                        rfl

theorem cell23_6557759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_6557759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557759 prefixEnd_6557759 := by exact prefixLift 6557759
  have htrace : WordTrace (prefixWord ++ tailWord_6557759) baseStart_6557759 baseEnd_6557759 := by
    simpa [prefixWord, tailWord_6557759, baseEnd_6557759] using wordTrace_append hprefix tailTrace_6557759
  have hstable : (prefixWord ++ tailWord_6557759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557759).length < 2 ^ (prefixWord ++ tailWord_6557759).sum := by decide
  have hdescent : baseEnd_6557759 < baseStart_6557759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557786 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_6557786 : Nat := 118140960795 + 6557786 * 2 ^ 59
def prefixEnd_6557786 : Nat := 4983230072969 + 3 ^ 40 * 6557786 * 2
def baseEnd_6557786 : Nat := 374144027480598318424033

theorem tailTrace_6557786 : CollatzResearch.WordTrace tailWord_6557786 prefixEnd_6557786 374144027480598318424033 := by
  unfold tailWord_6557786
  simp only [CollatzResearch.WordTrace]
  refine ⟨59795526255067194381923303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159454736680179185018462141 59795526255067194381923303)
  ·
    refine ⟨89693289382600791572884955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59795526255067194381923303 89693289382600791572884955)
    ·
      refine ⟨134539934073901187359327433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89693289382600791572884955 134539934073901187359327433)
      ·
        refine ⟨100904950555425890519495575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134539934073901187359327433 100904950555425890519495575)
        ·
          refine ⟨151357425833138835779243363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100904950555425890519495575 151357425833138835779243363)
          ·
            refine ⟨227036138749708253668865045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151357425833138835779243363 227036138749708253668865045)
            ·
              refine ⟨10642319003892574390728049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 227036138749708253668865045 10642319003892574390728049)
              ·
                refine ⟨7981739252919430793046037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642319003892574390728049 7981739252919430793046037)
                ·
                  refine ⟨374144027480598318424033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7981739252919430793046037 374144027480598318424033)
                  ·
                    rfl

theorem cell23_6557786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_6557786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557786 prefixEnd_6557786 := by exact prefixLift 6557786
  have htrace : WordTrace (prefixWord ++ tailWord_6557786) baseStart_6557786 baseEnd_6557786 := by
    simpa [prefixWord, tailWord_6557786, baseEnd_6557786] using wordTrace_append hprefix tailTrace_6557786
  have hstable : (prefixWord ++ tailWord_6557786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557786).length < 2 ^ (prefixWord ++ tailWord_6557786).sum := by decide
  have hdescent : baseEnd_6557786 < baseStart_6557786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557809 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_6557809 : Nat := 118140960795 + 6557809 * 2 ^ 59
def prefixEnd_6557809 : Nat := 4983230072969 + 3 ^ 40 * 6557809 * 2
def baseEnd_6557809 : Nat := 3367308057380438275828691

theorem tailTrace_6557809 : CollatzResearch.WordTrace tailWord_6557809 prefixEnd_6557809 3367308057380438275828691 := by
  unfold tailWord_6557809
  simp only [CollatzResearch.WordTrace]
  refine ⟨239182943899185452455780481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159455295932790301637186987 239182943899185452455780481)
  ·
    refine ⟨179387207924389089341835361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239182943899185452455780481 179387207924389089341835361)
    ·
      refine ⟨134540405943291817006376521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179387207924389089341835361 134540405943291817006376521)
      ·
        refine ⟨100905304457468862754782391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134540405943291817006376521 100905304457468862754782391)
        ·
          refine ⟨151357956686203294132173587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100905304457468862754782391 151357956686203294132173587)
          ·
            refine ⟨227036935029304941198260381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151357956686203294132173587 227036935029304941198260381)
            ·
              refine ⟨85138850635989352949347643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227036935029304941198260381 85138850635989352949347643)
              ·
                refine ⟨127708275953984029424021465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85138850635989352949347643 127708275953984029424021465)
                ·
                  refine ⟨95781206965488022068016099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127708275953984029424021465 95781206965488022068016099)
                  ·
                    refine ⟨143671810448232033102024149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95781206965488022068016099 143671810448232033102024149)
                    ·
                      refine ⟨3367308057380438275828691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143671810448232033102024149 3367308057380438275828691)
                      ·
                        rfl

theorem cell23_6557809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_6557809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557809 prefixEnd_6557809 := by exact prefixLift 6557809
  have htrace : WordTrace (prefixWord ++ tailWord_6557809) baseStart_6557809 baseEnd_6557809 := by
    simpa [prefixWord, tailWord_6557809, baseEnd_6557809] using wordTrace_append hprefix tailTrace_6557809
  have hstable : (prefixWord ++ tailWord_6557809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557809).length < 2 ^ (prefixWord ++ tailWord_6557809).sum := by decide
  have hdescent : baseEnd_6557809 < baseStart_6557809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557816 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_6557816 : Nat := 118140960795 + 6557816 * 2 ^ 59
def prefixEnd_6557816 : Nat := 4983230072969 + 3 ^ 40 * 6557816 * 2
def baseEnd_6557816 : Nat := 1122437217248339916147053

theorem tailTrace_6557816 : CollatzResearch.WordTrace tailWord_6557816 prefixEnd_6557816 1122437217248339916147053 := by
  unfold tailWord_6557816
  simp only [CollatzResearch.WordTrace]
  refine ⟨119591599605080046325642651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159455466140106728434190201 119591599605080046325642651)
  ·
    refine ⟨179387399407620069488463977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119591599605080046325642651 179387399407620069488463977)
    ·
      refine ⟨134540549555715052116347983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179387399407620069488463977 134540549555715052116347983)
      ·
        refine ⟨201810824333572578174521975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134540549555715052116347983 201810824333572578174521975)
        ·
          refine ⟨302716236500358867261782963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201810824333572578174521975 302716236500358867261782963)
          ·
            refine ⟨454074354750538300892674445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302716236500358867261782963 454074354750538300892674445)
            ·
              refine ⟨170277883031451862834752917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454074354750538300892674445 170277883031451862834752917)
              ·
                refine ⟨7981775767099306070379043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170277883031451862834752917 7981775767099306070379043)
                ·
                  refine ⟨11972663650648959105568565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7981775767099306070379043 11972663650648959105568565)
                  ·
                    refine ⟨1122437217248339916147053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11972663650648959105568565 1122437217248339916147053)
                    ·
                      rfl

theorem cell23_6557816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_6557816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557816 prefixEnd_6557816 := by exact prefixLift 6557816
  have htrace : WordTrace (prefixWord ++ tailWord_6557816) baseStart_6557816 baseEnd_6557816 := by
    simpa [prefixWord, tailWord_6557816, baseEnd_6557816] using wordTrace_append hprefix tailTrace_6557816
  have hstable : (prefixWord ++ tailWord_6557816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557816).length < 2 ^ (prefixWord ++ tailWord_6557816).sum := by decide
  have hdescent : baseEnd_6557816 < baseStart_6557816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557839 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_6557839 : Nat := 118140960795 + 6557839 * 2 ^ 59
def prefixEnd_6557839 : Nat := 4983230072969 + 3 ^ 40 * 6557839 * 2
def baseEnd_6557839 : Nat := 3367323461800073158453553

theorem tailTrace_6557839 : CollatzResearch.WordTrace tailWord_6557839 prefixEnd_6557839 3367323461800073158453553 := by
  unfold tailWord_6557839
  simp only [CollatzResearch.WordTrace]
  refine ⟨239184038089076767579372571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159456025392717845052915047 239184038089076767579372571)
  ·
    refine ⟨358776057133615151369058857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239184038089076767579372571 358776057133615151369058857)
    ·
      refine ⟨269082042850211363526794143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358776057133615151369058857 269082042850211363526794143)
      ·
        refine ⟨403623064275317045290191215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269082042850211363526794143 403623064275317045290191215)
        ·
          refine ⟨605434596412975567935286823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403623064275317045290191215 605434596412975567935286823)
          ·
            refine ⟨908151894619463351902930235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605434596412975567935286823 908151894619463351902930235)
            ·
              refine ⟨1362227841929195027854395353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908151894619463351902930235 1362227841929195027854395353)
              ·
                refine ⟨1021670881446896270890796515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362227841929195027854395353 1021670881446896270890796515)
                ·
                  refine ⟨1532506322170344406336194773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021670881446896270890796515 1532506322170344406336194773)
                  ·
                    refine ⟨35918116925867447023504565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1532506322170344406336194773 35918116925867447023504565)
                    ·
                      refine ⟨3367323461800073158453553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35918116925867447023504565 3367323461800073158453553)
                      ·
                        rfl

theorem cell23_6557839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_6557839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557839 prefixEnd_6557839 := by exact prefixLift 6557839
  have htrace : WordTrace (prefixWord ++ tailWord_6557839) baseStart_6557839 baseEnd_6557839 := by
    simpa [prefixWord, tailWord_6557839, baseEnd_6557839] using wordTrace_append hprefix tailTrace_6557839
  have hstable : (prefixWord ++ tailWord_6557839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557839).length < 2 ^ (prefixWord ++ tailWord_6557839).sum := by decide
  have hdescent : baseEnd_6557839 < baseStart_6557839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557856 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6557856 : Nat := 118140960795 + 6557856 * 2 ^ 59
def prefixEnd_6557856 : Nat := 4983230072969 + 3 ^ 40 * 6557856 * 2
def baseEnd_6557856 : Nat := 3367332190971199591940975

theorem tailTrace_6557856 : CollatzResearch.WordTrace tailWord_6557856 prefixEnd_6557856 3367332190971199591940975 := by
  unfold tailWord_6557856
  simp only [CollatzResearch.WordTrace]
  refine ⟨119592329065007589741370711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159456438753343452988494281 119592329065007589741370711)
  ·
    refine ⟨179388493597511384612056067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119592329065007589741370711 179388493597511384612056067)
    ·
      refine ⟨269082740396267076918084101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179388493597511384612056067 269082740396267076918084101)
      ·
        refine ⟨50453013824300076922140769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269082740396267076918084101 50453013824300076922140769)
        ·
          refine ⟨37839760368225057691605577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50453013824300076922140769 37839760368225057691605577)
          ·
            refine ⟨28379820276168793268704183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37839760368225057691605577 28379820276168793268704183)
            ·
              refine ⟨42569730414253189903056275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28379820276168793268704183 42569730414253189903056275)
              ·
                refine ⟨63854595621379784854584413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42569730414253189903056275 63854595621379784854584413)
                ·
                  refine ⟨23945473358017419320469155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63854595621379784854584413 23945473358017419320469155)
                  ·
                    refine ⟨35918210037026128980703733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23945473358017419320469155 35918210037026128980703733)
                    ·
                      refine ⟨3367332190971199591940975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35918210037026128980703733 3367332190971199591940975)
                      ·
                        rfl

theorem cell23_6557856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6557856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557856 prefixEnd_6557856 := by exact prefixLift 6557856
  have htrace : WordTrace (prefixWord ++ tailWord_6557856) baseStart_6557856 baseEnd_6557856 := by
    simpa [prefixWord, tailWord_6557856, baseEnd_6557856] using wordTrace_append hprefix tailTrace_6557856
  have hstable : (prefixWord ++ tailWord_6557856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557856).length < 2 ^ (prefixWord ++ tailWord_6557856).sum := by decide
  have hdescent : baseEnd_6557856 < baseStart_6557856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557903 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 3]
def baseStart_6557903 : Nat := 118140960795 + 6557903 * 2 ^ 59
def prefixEnd_6557903 : Nat := 4983230072969 + 3 ^ 40 * 6557903 * 2
def baseEnd_6557903 : Nat := 3367356324561960908053259

theorem tailTrace_6557903 : CollatzResearch.WordTrace tailWord_6557903 prefixEnd_6557903 3367356324561960908053259 := by
  unfold tailWord_6557903
  simp only [CollatzResearch.WordTrace]
  refine ⟨239186372360844906509702363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159457581573896604339801575 239186372360844906509702363)
  ·
    refine ⟨358779558541267359764553545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239186372360844906509702363 358779558541267359764553545)
    ·
      refine ⟨269084668905950519823415159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358779558541267359764553545 269084668905950519823415159)
      ·
        refine ⟨403627003358925779735122739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269084668905950519823415159 403627003358925779735122739)
        ·
          refine ⟨605440505038388669602684109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403627003358925779735122739 605440505038388669602684109)
          ·
            refine ⟨227040189389395751101006541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605440505038388669602684109 227040189389395751101006541)
            ·
              refine ⟨85140071021023406662877453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227040189389395751101006541 85140071021023406662877453)
              ·
                refine ⟨31927526632883777498579045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85140071021023406662877453 31927526632883777498579045)
                ·
                  refine ⟨5986411243665708280983571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31927526632883777498579045 5986411243665708280983571)
                  ·
                    refine ⟨8979616865498562421475357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5986411243665708280983571 8979616865498562421475357)
                    ·
                      refine ⟨3367356324561960908053259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8979616865498562421475357 3367356324561960908053259)
                      ·
                        rfl

theorem cell23_6557903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_6557903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557903 prefixEnd_6557903 := by exact prefixLift 6557903
  have htrace : WordTrace (prefixWord ++ tailWord_6557903) baseStart_6557903 baseEnd_6557903 := by
    simpa [prefixWord, tailWord_6557903, baseEnd_6557903] using wordTrace_append hprefix tailTrace_6557903
  have hstable : (prefixWord ++ tailWord_6557903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557903).length < 2 ^ (prefixWord ++ tailWord_6557903).sum := by decide
  have hdescent : baseEnd_6557903 < baseStart_6557903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557910 : List Nat := [5, 2, 1, 2, 1, 2, 2, 8]
def baseStart_6557910 : Nat := 118140960795 + 6557910 * 2 ^ 59
def prefixEnd_6557910 : Nat := 4983230072969 + 3 ^ 40 * 6557910 * 2
def baseEnd_6557910 : Nat := 124717034034316384469101

theorem tailTrace_6557910 : CollatzResearch.WordTrace tailWord_6557910 prefixEnd_6557910 124717034034316384469101 := by
  unfold tailWord_6557910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14949164229488721669075449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159457751781213031136804789 14949164229488721669075449)
  ·
    refine ⟨11211873172116541251806587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14949164229488721669075449 11211873172116541251806587)
    ·
      refine ⟨16817809758174811877709881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11211873172116541251806587 16817809758174811877709881)
      ·
        refine ⟨12613357318631108908282411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16817809758174811877709881 12613357318631108908282411)
        ·
          refine ⟨18920035977946663362423617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12613357318631108908282411 18920035977946663362423617)
          ·
            refine ⟨14190026983459997521817713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18920035977946663362423617 14190026983459997521817713)
            ·
              refine ⟨10642520237594998141363285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14190026983459997521817713 10642520237594998141363285)
              ·
                refine ⟨124717034034316384469101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10642520237594998141363285 124717034034316384469101)
                ·
                  rfl

theorem cell23_6557910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_6557910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557910 prefixEnd_6557910 := by exact prefixLift 6557910
  have htrace : WordTrace (prefixWord ++ tailWord_6557910) baseStart_6557910 baseEnd_6557910 := by
    simpa [prefixWord, tailWord_6557910, baseEnd_6557910] using wordTrace_append hprefix tailTrace_6557910
  have hstable : (prefixWord ++ tailWord_6557910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557910).length < 2 ^ (prefixWord ++ tailWord_6557910).sum := by decide
  have hdescent : baseEnd_6557910 < baseStart_6557910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557920 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3]
def baseStart_6557920 : Nat := 118140960795 + 6557920 * 2 ^ 59
def prefixEnd_6557920 : Nat := 4983230072969 + 3 ^ 40 * 6557920 * 2
def baseEnd_6557920 : Nat := 3367365053733087341540681

theorem tailTrace_6557920 : CollatzResearch.WordTrace tailWord_6557920 prefixEnd_6557920 3367365053733087341540681 := by
  unfold tailWord_6557920
  simp only [CollatzResearch.WordTrace]
  refine ⟨119593496200891659206535607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159457994934522212275380809 119593496200891659206535607)
  ·
    refine ⟨179390244301337488809803411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119593496200891659206535607 179390244301337488809803411)
    ·
      refine ⟨269085366452006233214705117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179390244301337488809803411 269085366452006233214705117)
      ·
        refine ⟨100907012419502337455514419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269085366452006233214705117 100907012419502337455514419)
        ·
          refine ⟨151360518629253506183271629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100907012419502337455514419 151360518629253506183271629)
          ·
            refine ⟨56760194485970064818726861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151360518629253506183271629 56760194485970064818726861)
            ·
              refine ⟨21285072932238774307022573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56760194485970064818726861 21285072932238774307022573)
              ·
                refine ⟨7981902349589540365133465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21285072932238774307022573 7981902349589540365133465)
                ·
                  refine ⟨5986426762192155273850099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7981902349589540365133465 5986426762192155273850099)
                  ·
                    refine ⟨8979640143288232910775149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5986426762192155273850099 8979640143288232910775149)
                    ·
                      refine ⟨3367365053733087341540681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8979640143288232910775149 3367365053733087341540681)
                      ·
                        rfl

theorem cell23_6557920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_6557920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557920 prefixEnd_6557920 := by exact prefixLift 6557920
  have htrace : WordTrace (prefixWord ++ tailWord_6557920) baseStart_6557920 baseEnd_6557920 := by
    simpa [prefixWord, tailWord_6557920, baseEnd_6557920] using wordTrace_append hprefix tailTrace_6557920
  have hstable : (prefixWord ++ tailWord_6557920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557920).length < 2 ^ (prefixWord ++ tailWord_6557920).sum := by decide
  have hdescent : baseEnd_6557920 < baseStart_6557920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557930 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_6557930 : Nat := 118140960795 + 6557930 * 2 ^ 59
def prefixEnd_6557930 : Nat := 4983230072969 + 3 ^ 40 * 6557930 * 2
def baseEnd_6557930 : Nat := 3367370188539632302415635

theorem tailTrace_6557930 : CollatzResearch.WordTrace tailWord_6557930 prefixEnd_6557930 3367370188539632302415635 := by
  unfold tailWord_6557930
  simp only [CollatzResearch.WordTrace]
  refine ⟨59796839282936772530233811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159458238087831393413956829 59796839282936772530233811)
  ·
    refine ⟨89695258924405158795350717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59796839282936772530233811 89695258924405158795350717)
    ·
      refine ⟨33635722096651934548256519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89695258924405158795350717 33635722096651934548256519)
      ·
        refine ⟨50453583144977901822384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33635722096651934548256519 50453583144977901822384779)
        ·
          refine ⟨75680374717466852733577169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50453583144977901822384779 75680374717466852733577169)
          ·
            refine ⟨56760281038100139550182877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75680374717466852733577169 56760281038100139550182877)
            ·
              refine ⟨21285105389287552331318579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56760281038100139550182877 21285105389287552331318579)
              ·
                refine ⟨31927658083931328496977869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21285105389287552331318579 31927658083931328496977869)
                ·
                  refine ⟨11972871781474248186366701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31927658083931328496977869 11972871781474248186366701)
                  ·
                    refine ⟨4489826918052843069887513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11972871781474248186366701 4489826918052843069887513)
                    ·
                      refine ⟨3367370188539632302415635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489826918052843069887513 3367370188539632302415635)
                      ·
                        rfl

theorem cell23_6557930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_6557930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557930 prefixEnd_6557930 := by exact prefixLift 6557930
  have htrace : WordTrace (prefixWord ++ tailWord_6557930) baseStart_6557930 baseEnd_6557930 := by
    simpa [prefixWord, tailWord_6557930, baseEnd_6557930] using wordTrace_append hprefix tailTrace_6557930
  have hstable : (prefixWord ++ tailWord_6557930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557930).length < 2 ^ (prefixWord ++ tailWord_6557930).sum := by decide
  have hdescent : baseEnd_6557930 < baseStart_6557930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557954 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_6557954 : Nat := 118140960795 + 6557954 * 2 ^ 59
def prefixEnd_6557954 : Nat := 4983230072969 + 3 ^ 40 * 6557954 * 2
def baseEnd_6557954 : Nat := 3367382512075340208515525

theorem tailTrace_6557954 : CollatzResearch.WordTrace tailWord_6557954 prefixEnd_6557954 3367382512075340208515525 := by
  unfold tailWord_6557954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59797058120915035554952229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159458821655773428146539277 59797058120915035554952229)
  ·
    refine ⟨11211948397671569166553543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59797058120915035554952229 11211948397671569166553543)
    ·
      refine ⟨16817922596507353749830315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11211948397671569166553543 16817922596507353749830315)
      ·
        refine ⟨25226883894761030624745473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16817922596507353749830315 25226883894761030624745473)
        ·
          refine ⟨18920162921070772968559105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25226883894761030624745473 18920162921070772968559105)
          ·
            refine ⟨14190122190803079726419329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18920162921070772968559105 14190122190803079726419329)
            ·
              refine ⟨10642591643102309794814497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14190122190803079726419329 10642591643102309794814497)
              ·
                refine ⟨7981943732326732346110873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642591643102309794814497 7981943732326732346110873)
                ·
                  refine ⟨5986457799245049259583155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7981943732326732346110873 5986457799245049259583155)
                  ·
                    refine ⟨8979686698867573889374733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5986457799245049259583155 8979686698867573889374733)
                    ·
                      refine ⟨3367382512075340208515525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8979686698867573889374733 3367382512075340208515525)
                      ·
                        rfl

theorem cell23_6557954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_6557954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557954 prefixEnd_6557954 := by exact prefixLift 6557954
  have htrace : WordTrace (prefixWord ++ tailWord_6557954) baseStart_6557954 baseEnd_6557954 := by
    simpa [prefixWord, tailWord_6557954, baseEnd_6557954] using wordTrace_append hprefix tailTrace_6557954
  have hstable : (prefixWord ++ tailWord_6557954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557954).length < 2 ^ (prefixWord ++ tailWord_6557954).sum := by decide
  have hdescent : baseEnd_6557954 < baseStart_6557954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557983 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 7]
def baseStart_6557983 : Nat := 118140960795 + 6557983 * 2 ^ 59
def prefixEnd_6557983 : Nat := 4983230072969 + 3 ^ 40 * 6557983 * 2
def baseEnd_6557983 : Nat := 374155267001591177228099

theorem tailTrace_6557983 : CollatzResearch.WordTrace tailWord_6557983 prefixEnd_6557983 374155267001591177228099 := by
  unfold tailWord_6557983
  simp only [CollatzResearch.WordTrace]
  refine ⟨239189290200555080172614603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159459526800370053448409735 239189290200555080172614603)
  ·
    refine ⟨358783935300832620258921905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239189290200555080172614603 358783935300832620258921905)
    ·
      refine ⟨269087951475624465194191429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358783935300832620258921905 269087951475624465194191429)
      ·
        refine ⟨50453990901679587223910893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269087951475624465194191429 50453990901679587223910893)
        ·
          refine ⟨18920246588129845208966585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50453990901679587223910893 18920246588129845208966585)
          ·
            refine ⟨14190184941097383906724939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18920246588129845208966585 14190184941097383906724939)
            ·
              refine ⟨21285277411646075860087409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14190184941097383906724939 21285277411646075860087409)
              ·
                refine ⟨15963958058734556895065557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21285277411646075860087409 15963958058734556895065557)
                ·
                  refine ⟨374155267001591177228099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15963958058734556895065557 374155267001591177228099)
                  ·
                    rfl

theorem cell23_6557983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 7].length) (baseStart_6557983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557983 prefixEnd_6557983 := by exact prefixLift 6557983
  have htrace : WordTrace (prefixWord ++ tailWord_6557983) baseStart_6557983 baseEnd_6557983 := by
    simpa [prefixWord, tailWord_6557983, baseEnd_6557983] using wordTrace_append hprefix tailTrace_6557983
  have hstable : (prefixWord ++ tailWord_6557983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557983).length < 2 ^ (prefixWord ++ tailWord_6557983).sum := by decide
  have hdescent : baseEnd_6557983 < baseStart_6557983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557998 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6557998 : Nat := 118140960795 + 6557998 * 2 ^ 59
def prefixEnd_6557998 : Nat := 4983230072969 + 3 ^ 40 * 6557998 * 2
def baseEnd_6557998 : Nat := 3367405105224138036365323

theorem tailTrace_6557998 : CollatzResearch.WordTrace tailWord_6557998 prefixEnd_6557998 3367405105224138036365323 := by
  unfold tailWord_6557998
  simp only [CollatzResearch.WordTrace]
  refine ⟨29898729661937592216801331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159459891530333825156273765 29898729661937592216801331)
  ·
    refine ⟨44848094492906388325201997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29898729661937592216801331 44848094492906388325201997)
    ·
      refine ⟨16818035434839895621950749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44848094492906388325201997 16818035434839895621950749)
      ·
        refine ⟨6306763288064960858231531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16818035434839895621950749 6306763288064960858231531)
        ·
          refine ⟨9460144932097441287347297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6306763288064960858231531 9460144932097441287347297)
          ·
            refine ⟨7095108699073080965510473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9460144932097441287347297 7095108699073080965510473)
            ·
              refine ⟨5321331524304810724132855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095108699073080965510473 5321331524304810724132855)
              ·
                refine ⟨7981997286457216086199283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321331524304810724132855 7981997286457216086199283)
                ·
                  refine ⟨11972995929685824129298925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7981997286457216086199283 11972995929685824129298925)
                  ·
                    refine ⟨4489873473632184048487097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11972995929685824129298925 4489873473632184048487097)
                    ·
                      refine ⟨3367405105224138036365323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4489873473632184048487097 3367405105224138036365323)
                      ·
                        rfl

theorem cell23_6557998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6557998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557998 prefixEnd_6557998 := by exact prefixLift 6557998
  have htrace : WordTrace (prefixWord ++ tailWord_6557998) baseStart_6557998 baseEnd_6557998 := by
    simpa [prefixWord, tailWord_6557998, baseEnd_6557998] using wordTrace_append hprefix tailTrace_6557998
  have hstable : (prefixWord ++ tailWord_6557998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557998).length < 2 ^ (prefixWord ++ tailWord_6557998).sum := by decide
  have hdescent : baseEnd_6557998 < baseStart_6557998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558033 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_6558033 : Nat := 118140960795 + 6558033 * 2 ^ 59
def prefixEnd_6558033 : Nat := 4983230072969 + 3 ^ 40 * 6558033 * 2
def baseEnd_6558033 : Nat := 3367423077047045399427661

theorem tailTrace_6558033 : CollatzResearch.WordTrace tailWord_6558033 prefixEnd_6558033 3367423077047045399427661 := by
  unfold tailWord_6558033
  simp only [CollatzResearch.WordTrace]
  refine ⟨239191113850373938711934753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159460742566915959141289835 239191113850373938711934753)
  ·
    refine ⟨179393335387780454033951065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239191113850373938711934753 179393335387780454033951065)
    ·
      refine ⟨134545001540835340525463299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179393335387780454033951065 134545001540835340525463299)
      ·
        refine ⟨201817502311253010788194949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134545001540835340525463299 201817502311253010788194949)
        ·
          refine ⟨37840781683359939522786553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201817502311253010788194949 37840781683359939522786553)
          ·
            refine ⟨28380586262519954642089915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37840781683359939522786553 28380586262519954642089915)
            ·
              refine ⟨42570879393779931963134873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28380586262519954642089915 42570879393779931963134873)
              ·
                refine ⟨31928159545334948972351155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42570879393779931963134873 31928159545334948972351155)
                ·
                  refine ⟨47892239318002423458526733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31928159545334948972351155 47892239318002423458526733)
                  ·
                    refine ⟨17959589744250908796947525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47892239318002423458526733 17959589744250908796947525)
                    ·
                      refine ⟨3367423077047045399427661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17959589744250908796947525 3367423077047045399427661)
                      ·
                        rfl

theorem cell23_6558033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_6558033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558033 prefixEnd_6558033 := by exact prefixLift 6558033
  have htrace : WordTrace (prefixWord ++ tailWord_6558033) baseStart_6558033 baseEnd_6558033 := by
    simpa [prefixWord, tailWord_6558033, baseEnd_6558033] using wordTrace_append hprefix tailTrace_6558033
  have hstable : (prefixWord ++ tailWord_6558033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558033).length < 2 ^ (prefixWord ++ tailWord_6558033).sum := by decide
  have hdescent : baseEnd_6558033 < baseStart_6558033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558050 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6558050 : Nat := 118140960795 + 6558050 * 2 ^ 59
def prefixEnd_6558050 : Nat := 4983230072969 + 3 ^ 40 * 6558050 * 2
def baseEnd_6558050 : Nat := 3367431806218171832915083

theorem tailTrace_6558050 : CollatzResearch.WordTrace tailWord_6558050 prefixEnd_6558050 3367431806218171832915083 := by
  unfold tailWord_6558050
  simp only [CollatzResearch.WordTrace]
  refine ⟨59797933472828087653825901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159461155927541567076869069 59797933472828087653825901)
  ·
    refine ⟨22424225052310532870184713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59797933472828087653825901 22424225052310532870184713)
    ·
      refine ⟨16818168789232899652638535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22424225052310532870184713 16818168789232899652638535)
      ·
        refine ⟨25227253183849349478957803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16818168789232899652638535 25227253183849349478957803)
        ·
          refine ⟨37840879775774024218436705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25227253183849349478957803 37840879775774024218436705)
          ·
            refine ⟨28380659831830518163827529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37840879775774024218436705 28380659831830518163827529)
            ·
              refine ⟨21285494873872888622870647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28380659831830518163827529 21285494873872888622870647)
              ·
                refine ⟨31928242310809332934305971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21285494873872888622870647 31928242310809332934305971)
                ·
                  refine ⟨47892363466213999401458957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31928242310809332934305971 47892363466213999401458957)
                  ·
                    refine ⟨17959636299830249775547109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47892363466213999401458957 17959636299830249775547109)
                    ·
                      refine ⟨3367431806218171832915083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17959636299830249775547109 3367431806218171832915083)
                      ·
                        rfl

theorem cell23_6558050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6558050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558050 prefixEnd_6558050 := by exact prefixLift 6558050
  have htrace : WordTrace (prefixWord ++ tailWord_6558050) baseStart_6558050 baseEnd_6558050 := by
    simpa [prefixWord, tailWord_6558050, baseEnd_6558050] using wordTrace_append hprefix tailTrace_6558050
  have hstable : (prefixWord ++ tailWord_6558050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558050).length < 2 ^ (prefixWord ++ tailWord_6558050).sum := by decide
  have hdescent : baseEnd_6558050 < baseStart_6558050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558073 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 6]
def baseStart_6558073 : Nat := 118140960795 + 6558073 * 2 ^ 59
def prefixEnd_6558073 : Nat := 4983230072969 + 3 ^ 40 * 6558073 * 2
def baseEnd_6558073 : Nat := 374160401808136138103053

theorem tailTrace_6558073 : CollatzResearch.WordTrace tailWord_6558073 prefixEnd_6558073 374160401808136138103053 := by
  unfold tailWord_6558073
  simp only [CollatzResearch.WordTrace]
  refine ⟨239192572770229025543390873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159461715180152683695593915 239192572770229025543390873)
  ·
    refine ⟨179394429577671769157543155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239192572770229025543390873 179394429577671769157543155)
    ·
      refine ⟨269091644366507653736314733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179394429577671769157543155 269091644366507653736314733)
      ·
        refine ⟨100909366637440370151118025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269091644366507653736314733 100909366637440370151118025)
        ·
          refine ⟨75682024978080277613338519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100909366637440370151118025 75682024978080277613338519)
          ·
            refine ⟨113523037467120416420007779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75682024978080277613338519 113523037467120416420007779)
            ·
              refine ⟨170284556200680624630011669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113523037467120416420007779 170284556200680624630011669)
              ·
                refine ⟨7982088571906904279531797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170284556200680624630011669 7982088571906904279531797)
                ·
                  refine ⟨374160401808136138103053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7982088571906904279531797 374160401808136138103053)
                  ·
                    rfl

theorem cell23_6558073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_6558073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558073 prefixEnd_6558073 := by exact prefixLift 6558073
  have htrace : WordTrace (prefixWord ++ tailWord_6558073) baseStart_6558073 baseEnd_6558073 := by
    simpa [prefixWord, tailWord_6558073, baseEnd_6558073] using wordTrace_append hprefix tailTrace_6558073
  have hstable : (prefixWord ++ tailWord_6558073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558073).length < 2 ^ (prefixWord ++ tailWord_6558073).sum := by decide
  have hdescent : baseEnd_6558073 < baseStart_6558073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558077 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_6558077 : Nat := 118140960795 + 6558077 * 2 ^ 59
def prefixEnd_6558077 : Nat := 4983230072969 + 3 ^ 40 * 6558077 * 2
def baseEnd_6558077 : Nat := 1122481890065281075759153

theorem tailTrace_6558077 : CollatzResearch.WordTrace tailWord_6558077 prefixEnd_6558077 1122481890065281075759153 := by
  unfold tailWord_6558077
  simp only [CollatzResearch.WordTrace]
  refine ⟨239192718662214534226536485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159461812441476356151024323 239192718662214534226536485)
  ·
    refine ⟨44848634749165225167475591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239192718662214534226536485 44848634749165225167475591)
    ·
      refine ⟨67272952123747837751213387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44848634749165225167475591 67272952123747837751213387)
      ·
        refine ⟨100909428185621756626820081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67272952123747837751213387 100909428185621756626820081)
        ·
          refine ⟨75682071139216317470115061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100909428185621756626820081 75682071139216317470115061)
          ·
            refine ⟨7095194169301529762823287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75682071139216317470115061 7095194169301529762823287)
            ·
              refine ⟨10642791253952294644234931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095194169301529762823287 10642791253952294644234931)
              ·
                refine ⟨15964186880928441966352397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10642791253952294644234931 15964186880928441966352397)
                ·
                  refine ⟨5986570080348165737382149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15964186880928441966352397 5986570080348165737382149)
                  ·
                    refine ⟨1122481890065281075759153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986570080348165737382149 1122481890065281075759153)
                    ·
                      rfl

theorem cell23_6558077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_6558077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558077 prefixEnd_6558077 := by exact prefixLift 6558077
  have htrace : WordTrace (prefixWord ++ tailWord_6558077) baseStart_6558077 baseEnd_6558077 := by
    simpa [prefixWord, tailWord_6558077, baseEnd_6558077] using wordTrace_append hprefix tailTrace_6558077
  have hstable : (prefixWord ++ tailWord_6558077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558077).length < 2 ^ (prefixWord ++ tailWord_6558077).sum := by decide
  have hdescent : baseEnd_6558077 < baseStart_6558077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558153 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_6558153 : Nat := 118140960795 + 6558153 * 2 ^ 59
def prefixEnd_6558153 : Nat := 4983230072969 + 3 ^ 40 * 6558153 * 2
def baseEnd_6558153 : Nat := 3367484694725584929927109

theorem tailTrace_6558153 : CollatzResearch.WordTrace tailWord_6558153 prefixEnd_6558153 3367484694725584929927109 := by
  unfold tailWord_6558153
  simp only [CollatzResearch.WordTrace]
  refine ⟨239195490609939199206303113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159463660406626132804202075 239195490609939199206303113)
  ·
    refine ⟨179396617957454399404727335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239195490609939199206303113 179396617957454399404727335)
    ·
      refine ⟨269094926936181599107091003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179396617957454399404727335 269094926936181599107091003)
      ·
        refine ⟨403642390404272398660636505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269094926936181599107091003 403642390404272398660636505)
        ·
          refine ⟨302731792803204298995477379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403642390404272398660636505 302731792803204298995477379)
          ·
            refine ⟨454097689204806448493216069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302731792803204298995477379 454097689204806448493216069)
            ·
              refine ⟨85143316725901209092478013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 454097689204806448493216069 85143316725901209092478013)
              ·
                refine ⟨31928743772212953409679255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85143316725901209092478013 31928743772212953409679255)
                ·
                  refine ⟨47893115658319430114518883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31928743772212953409679255 47893115658319430114518883)
                  ·
                    refine ⟨71839673487479145171778325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47893115658319430114518883 71839673487479145171778325)
                    ·
                      refine ⟨3367484694725584929927109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71839673487479145171778325 3367484694725584929927109)
                      ·
                        rfl

theorem cell23_6558153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_6558153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558153 prefixEnd_6558153 := by exact prefixLift 6558153
  have htrace : WordTrace (prefixWord ++ tailWord_6558153) baseStart_6558153 baseEnd_6558153 := by
    simpa [prefixWord, tailWord_6558153, baseEnd_6558153] using wordTrace_append hprefix tailTrace_6558153
  have hstable : (prefixWord ++ tailWord_6558153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558153).length < 2 ^ (prefixWord ++ tailWord_6558153).sum := by decide
  have hdescent : baseEnd_6558153 < baseStart_6558153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558170 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_6558170 : Nat := 118140960795 + 6558170 * 2 ^ 59
def prefixEnd_6558170 : Nat := 4983230072969 + 3 ^ 40 * 6558170 * 2
def baseEnd_6558170 : Nat := 3367493423896711363414531

theorem tailTrace_6558170 : CollatzResearch.WordTrace tailWord_6558170 prefixEnd_6558170 3367493423896711363414531 := by
  unfold tailWord_6558170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59799027662719402777417991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159464073767251740739781309 59799027662719402777417991)
  ·
    refine ⟨89698541494079104166126987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59799027662719402777417991 89698541494079104166126987)
    ·
      refine ⟨134547812241118656249190481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89698541494079104166126987 134547812241118656249190481)
      ·
        refine ⟨100910859180838992186892861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134547812241118656249190481 100910859180838992186892861)
        ·
          refine ⟨37841572192814622070084823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100910859180838992186892861 37841572192814622070084823)
          ·
            refine ⟨56762358289221933105127235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37841572192814622070084823 56762358289221933105127235)
            ·
              refine ⟨85143537433832899657690853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56762358289221933105127235 85143537433832899657690853)
              ·
                refine ⟨15964413268843668685817035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85143537433832899657690853 15964413268843668685817035)
                ·
                  refine ⟨23946619903265503028725553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15964413268843668685817035 23946619903265503028725553)
                  ·
                    refine ⟨17959964927449127271544165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23946619903265503028725553 17959964927449127271544165)
                    ·
                      refine ⟨3367493423896711363414531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17959964927449127271544165 3367493423896711363414531)
                      ·
                        rfl

theorem cell23_6558170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_6558170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558170 prefixEnd_6558170 := by exact prefixLift 6558170
  have htrace : WordTrace (prefixWord ++ tailWord_6558170) baseStart_6558170 baseEnd_6558170 := by
    simpa [prefixWord, tailWord_6558170, baseEnd_6558170] using wordTrace_append hprefix tailTrace_6558170
  have hstable : (prefixWord ++ tailWord_6558170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558170).length < 2 ^ (prefixWord ++ tailWord_6558170).sum := by decide
  have hdescent : baseEnd_6558170 < baseStart_6558170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558177 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_6558177 : Nat := 118140960795 + 6558177 * 2 ^ 59
def prefixEnd_6558177 : Nat := 4983230072969 + 3 ^ 40 * 6558177 * 2
def baseEnd_6558177 : Nat := 3367497018261292836026999

theorem tailTrace_6558177 : CollatzResearch.WordTrace tailWord_6558177 prefixEnd_6558177 3367497018261292836026999 := by
  unfold tailWord_6558177
  simp only [CollatzResearch.WordTrace]
  refine ⟨239196365961852251305176785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159464243974568167536784523 239196365961852251305176785)
  ·
    refine ⟨179397274471389188478882589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239196365961852251305176785 179397274471389188478882589)
    ·
      refine ⟨67273977926770945679580971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179397274471389188478882589 67273977926770945679580971)
      ·
        refine ⟨100910966890156418519371457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67273977926770945679580971 100910966890156418519371457)
        ·
          refine ⟨75683225167617313889528593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100910966890156418519371457 75683225167617313889528593)
          ·
            refine ⟨56762418875712985417146445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75683225167617313889528593 56762418875712985417146445)
            ·
              refine ⟨21285907078392369531429917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56762418875712985417146445 21285907078392369531429917)
              ·
                refine ⟨7982215154397138574286219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21285907078392369531429917 7982215154397138574286219)
                ·
                  refine ⟨11973322731595707861429329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982215154397138574286219 11973322731595707861429329)
                  ·
                    refine ⟨8979992048696780896071997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11973322731595707861429329 8979992048696780896071997)
                    ·
                      refine ⟨3367497018261292836026999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8979992048696780896071997 3367497018261292836026999)
                      ·
                        rfl

theorem cell23_6558177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_6558177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558177 prefixEnd_6558177 := by exact prefixLift 6558177
  have htrace : WordTrace (prefixWord ++ tailWord_6558177) baseStart_6558177 baseEnd_6558177 := by
    simpa [prefixWord, tailWord_6558177, baseEnd_6558177] using wordTrace_append hprefix tailTrace_6558177
  have hstable : (prefixWord ++ tailWord_6558177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558177).length < 2 ^ (prefixWord ++ tailWord_6558177).sum := by decide
  have hdescent : baseEnd_6558177 < baseStart_6558177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558184 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_6558184 : Nat := 118140960795 + 6558184 * 2 ^ 59
def prefixEnd_6558184 : Nat := 4983230072969 + 3 ^ 40 * 6558184 * 2
def baseEnd_6558184 : Nat := 1122500204208624769546489

theorem tailTrace_6558184 : CollatzResearch.WordTrace tailWord_6558184 prefixEnd_6558184 1122500204208624769546489 := by
  unfold tailWord_6558184
  simp only [CollatzResearch.WordTrace]
  refine ⟨119598310636413445750340803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159464414181884594333787737 119598310636413445750340803)
  ·
    refine ⟨179397465954620168625511205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119598310636413445750340803 179397465954620168625511205)
    ·
      refine ⟨33637024866491281617283351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179397465954620168625511205 33637024866491281617283351)
      ·
        refine ⟨50455537299736922425925027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33637024866491281617283351 50455537299736922425925027)
        ·
          refine ⟨75683305949605383638887541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50455537299736922425925027 75683305949605383638887541)
          ·
            refine ⟨7095309932775504716145707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75683305949605383638887541 7095309932775504716145707)
            ·
              refine ⟨10642964899163257074218561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095309932775504716145707 10642964899163257074218561)
              ·
                refine ⟨7982223674372442805663921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642964899163257074218561 7982223674372442805663921)
                ·
                  refine ⟨5986667755779332104247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982223674372442805663921 5986667755779332104247941)
                  ·
                    refine ⟨1122500204208624769546489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986667755779332104247941 1122500204208624769546489)
                    ·
                      rfl

theorem cell23_6558184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_6558184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558184 prefixEnd_6558184 := by exact prefixLift 6558184
  have htrace : WordTrace (prefixWord ++ tailWord_6558184) baseStart_6558184 baseEnd_6558184 := by
    simpa [prefixWord, tailWord_6558184, baseEnd_6558184] using wordTrace_append hprefix tailTrace_6558184
  have hstable : (prefixWord ++ tailWord_6558184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558184).length < 2 ^ (prefixWord ++ tailWord_6558184).sum := by decide
  have hdescent : baseEnd_6558184 < baseStart_6558184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558203 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_6558203 : Nat := 118140960795 + 6558203 * 2 ^ 59
def prefixEnd_6558203 : Nat := 4983230072969 + 3 ^ 40 * 6558203 * 2
def baseEnd_6558203 : Nat := 3367510368758309734301879

theorem tailTrace_6558203 : CollatzResearch.WordTrace tailWord_6558203 prefixEnd_6558203 3367510368758309734301879 := by
  unfold tailWord_6558203
  simp only [CollatzResearch.WordTrace]
  refine ⟨239197314259758057745623263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159464876173172038497082175 239197314259758057745623263)
  ·
    refine ⟨358795971389637086618434895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239197314259758057745623263 358795971389637086618434895)
    ·
      refine ⟨538193957084455629927652343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358795971389637086618434895 538193957084455629927652343)
      ·
        refine ⟨807290935626683444891478515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538193957084455629927652343 807290935626683444891478515)
        ·
          refine ⟨1210936403440025167337217773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807290935626683444891478515 1210936403440025167337217773)
          ·
            refine ⟨454101151290009437751456665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210936403440025167337217773 454101151290009437751456665)
            ·
              refine ⟨340575863467507078313592499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454101151290009437751456665 340575863467507078313592499)
              ·
                refine ⟨510863795201260617470388749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340575863467507078313592499 510863795201260617470388749)
                ·
                  refine ⟨191573923200472731551395781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510863795201260617470388749 191573923200472731551395781)
                  ·
                    refine ⟨35920110600088637165886709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191573923200472731551395781 35920110600088637165886709)
                    ·
                      refine ⟨3367510368758309734301879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35920110600088637165886709 3367510368758309734301879)
                      ·
                        rfl

theorem cell23_6558203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_6558203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558203 prefixEnd_6558203 := by exact prefixLift 6558203
  have htrace : WordTrace (prefixWord ++ tailWord_6558203) baseStart_6558203 baseEnd_6558203 := by
    simpa [prefixWord, tailWord_6558203, baseEnd_6558203] using wordTrace_append hprefix tailTrace_6558203
  have hstable : (prefixWord ++ tailWord_6558203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558203).length < 2 ^ (prefixWord ++ tailWord_6558203).sum := by decide
  have hdescent : baseEnd_6558203 < baseStart_6558203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558220 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6558220 : Nat := 118140960795 + 6558220 * 2 ^ 59
def prefixEnd_6558220 : Nat := 4983230072969 + 3 ^ 40 * 6558220 * 2
def baseEnd_6558220 : Nat := 3367519097929436167789301

theorem tailTrace_6558220 : CollatzResearch.WordTrace tailWord_6558220 prefixEnd_6558220 3367519097929436167789301 := by
  unfold tailWord_6558220
  simp only [CollatzResearch.WordTrace]
  refine ⟨119598967150348234824496057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159465289533797646432661409 119598967150348234824496057)
  ·
    refine ⟨89699225362761176118372043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119598967150348234824496057 89699225362761176118372043)
    ·
      refine ⟨134548838044141764177558065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89699225362761176118372043 134548838044141764177558065)
      ·
        refine ⟨100911628533106323133168549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134548838044141764177558065 100911628533106323133168549)
        ·
          refine ⟨18920930349957435587469103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100911628533106323133168549 18920930349957435587469103)
          ·
            refine ⟨28381395524936153381203655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18920930349957435587469103 28381395524936153381203655)
            ·
              refine ⟨42572093287404230071805483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28381395524936153381203655 42572093287404230071805483)
              ·
                refine ⟨63858139931106345107708225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42572093287404230071805483 63858139931106345107708225)
                ·
                  refine ⟨47893604948329758830781169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63858139931106345107708225 47893604948329758830781169)
                  ·
                    refine ⟨35920203711247319123085877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47893604948329758830781169 35920203711247319123085877)
                    ·
                      refine ⟨3367519097929436167789301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35920203711247319123085877 3367519097929436167789301)
                      ·
                        rfl

theorem cell23_6558220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6558220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558220 prefixEnd_6558220 := by exact prefixLift 6558220
  have htrace : WordTrace (prefixWord ++ tailWord_6558220) baseStart_6558220 baseEnd_6558220 := by
    simpa [prefixWord, tailWord_6558220, baseEnd_6558220] using wordTrace_append hprefix tailTrace_6558220
  have hstable : (prefixWord ++ tailWord_6558220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558220).length < 2 ^ (prefixWord ++ tailWord_6558220).sum := by decide
  have hdescent : baseEnd_6558220 < baseStart_6558220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558223 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 8]
def baseStart_6558223 : Nat := 118140960795 + 6558223 * 2 ^ 59
def prefixEnd_6558223 : Nat := 4983230072969 + 3 ^ 40 * 6558223 * 2
def baseEnd_6558223 : Nat := 1122506879457133218683929

theorem tailTrace_6558223 : CollatzResearch.WordTrace tailWord_6558223 prefixEnd_6558223 1122506879457133218683929 := by
  unfold tailWord_6558223
  simp only [CollatzResearch.WordTrace]
  refine ⟨239198043719685601161351323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159465362479790400774234215 239198043719685601161351323)
  ·
    refine ⟨358797065579528401742026985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239198043719685601161351323 358797065579528401742026985)
    ·
      refine ⟨269097799184646301306520239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358797065579528401742026985 269097799184646301306520239)
      ·
        refine ⟨403646698776969451959780359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269097799184646301306520239 403646698776969451959780359)
        ·
          refine ⟨605470048165454177939670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403646698776969451959780359 605470048165454177939670539)
          ·
            refine ⟨908205072248181266909505809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605470048165454177939670539 908205072248181266909505809)
            ·
              refine ⟨681153804186135950182129357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908205072248181266909505809 681153804186135950182129357)
              ·
                refine ⟨255432676569800981318298509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 681153804186135950182129357 255432676569800981318298509)
                ·
                  refine ⟨95787253713675367994361941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255432676569800981318298509 95787253713675367994361941)
                  ·
                    refine ⟨1122506879457133218683929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95787253713675367994361941 1122506879457133218683929)
                    ·
                      rfl

theorem cell23_6558223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_6558223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558223 prefixEnd_6558223 := by exact prefixLift 6558223
  have htrace : WordTrace (prefixWord ++ tailWord_6558223) baseStart_6558223 baseEnd_6558223 := by
    simpa [prefixWord, tailWord_6558223, baseEnd_6558223] using wordTrace_append hprefix tailTrace_6558223
  have hstable : (prefixWord ++ tailWord_6558223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558223).length < 2 ^ (prefixWord ++ tailWord_6558223).sum := by decide
  have hdescent : baseEnd_6558223 < baseStart_6558223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558234 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_6558234 : Nat := 118140960795 + 6558234 * 2 ^ 59
def prefixEnd_6558234 : Nat := 4983230072969 + 3 ^ 40 * 6558234 * 2
def baseEnd_6558234 : Nat := 3367526286658599113014237

theorem tailTrace_6558234 : CollatzResearch.WordTrace tailWord_6558234 prefixEnd_6558234 3367526286658599113014237 := by
  unfold tailWord_6558234
  simp only [CollatzResearch.WordTrace]
  refine ⟨59799611230661437510000439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159465629948430500026667837 59799611230661437510000439)
  ·
    refine ⟨89699416845992156265000659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59799611230661437510000439 89699416845992156265000659)
    ·
      refine ⟨134549125268988234397500989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89699416845992156265000659 134549125268988234397500989)
      ·
        refine ⟨50455921975870587899062871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134549125268988234397500989 50455921975870587899062871)
        ·
          refine ⟨75683882963805881848594307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50455921975870587899062871 75683882963805881848594307)
          ·
            refine ⟨113525824445708822772891461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75683882963805881848594307 113525824445708822772891461)
            ·
              refine ⟨21286092083570404269917149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113525824445708822772891461 21286092083570404269917149)
              ·
                refine ⟨7982284531338901601218931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21286092083570404269917149 7982284531338901601218931)
                ·
                  refine ⟨11973426797008352401828397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982284531338901601218931 11973426797008352401828397)
                  ·
                    refine ⟨4490035048878132150685649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11973426797008352401828397 4490035048878132150685649)
                    ·
                      refine ⟨3367526286658599113014237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490035048878132150685649 3367526286658599113014237)
                      ·
                        rfl

theorem cell23_6558234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_6558234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558234 prefixEnd_6558234 := by exact prefixLift 6558234
  have htrace : WordTrace (prefixWord ++ tailWord_6558234) baseStart_6558234 baseEnd_6558234 := by
    simpa [prefixWord, tailWord_6558234, baseEnd_6558234] using wordTrace_append hprefix tailTrace_6558234
  have hstable : (prefixWord ++ tailWord_6558234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558234).length < 2 ^ (prefixWord ++ tailWord_6558234).sum := by decide
  have hdescent : baseEnd_6558234 < baseStart_6558234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558304 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 5]
def baseStart_6558304 : Nat := 118140960795 + 6558304 * 2 ^ 59
def prefixEnd_6558304 : Nat := 4983230072969 + 3 ^ 40 * 6558304 * 2
def baseEnd_6558304 : Nat := 374173581144934871015435

theorem tailTrace_6558304 : CollatzResearch.WordTrace tailWord_6558304 prefixEnd_6558304 374173581144934871015435 := by
  unfold tailWord_6558304
  simp only [CollatzResearch.WordTrace]
  refine ⟨119600499016196075997524983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159467332021594767996699977 119600499016196075997524983)
  ·
    refine ⟨179400748524294113996287475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119600499016196075997524983 179400748524294113996287475)
    ·
      refine ⟨269101122786441170994431213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179400748524294113996287475 269101122786441170994431213)
      ·
        refine ⟨100912921044915439122911705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269101122786441170994431213 100912921044915439122911705)
        ·
          refine ⟨75684690783686579342183779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100912921044915439122911705 75684690783686579342183779)
          ·
            refine ⟨113527036175529869013275669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75684690783686579342183779 113527036175529869013275669)
            ·
              refine ⟨5321579820727962609997297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113527036175529869013275669 5321579820727962609997297)
              ·
                refine ⟨3991184865545971957497973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5321579820727962609997297 3991184865545971957497973)
                ·
                  refine ⟨374173581144934871015435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3991184865545971957497973 374173581144934871015435)
                  ·
                    rfl

theorem cell23_6558304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 5].length) (baseStart_6558304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558304 prefixEnd_6558304 := by exact prefixLift 6558304
  have htrace : WordTrace (prefixWord ++ tailWord_6558304) baseStart_6558304 baseEnd_6558304 := by
    simpa [prefixWord, tailWord_6558304, baseEnd_6558304] using wordTrace_append hprefix tailTrace_6558304
  have hstable : (prefixWord ++ tailWord_6558304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558304).length < 2 ^ (prefixWord ++ tailWord_6558304).sum := by decide
  have hdescent : baseEnd_6558304 < baseStart_6558304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558307 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 7, 2]
def baseStart_6558307 : Nat := 118140960795 + 6558307 * 2 ^ 59
def prefixEnd_6558307 : Nat := 4983230072969 + 3 ^ 40 * 6558307 * 2
def baseEnd_6558307 : Nat := 3367563770746377327401401

theorem tailTrace_6558307 : CollatzResearch.WordTrace tailWord_6558307 prefixEnd_6558307 3367563770746377327401401 := by
  unfold tailWord_6558307
  simp only [CollatzResearch.WordTrace]
  refine ⟨239201107451381283507409175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159467404967587522338272783 239201107451381283507409175)
  ·
    refine ⟨358801661177071925261113763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239201107451381283507409175 358801661177071925261113763)
    ·
      refine ⟨538202491765607887891670645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358801661177071925261113763 538202491765607887891670645)
      ·
        refine ⟨50456483603025739489844123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 538202491765607887891670645 50456483603025739489844123)
        ·
          refine ⟨75684725404538609234766185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50456483603025739489844123 75684725404538609234766185)
          ·
            refine ⟨56763544053403956926074639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75684725404538609234766185 56763544053403956926074639)
            ·
              refine ⟨85145316080105935389111959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56763544053403956926074639 85145316080105935389111959)
              ·
                refine ⟨127717974120158903083667939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85145316080105935389111959 127717974120158903083667939)
                ·
                  refine ⟨191576961180238354625501909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127717974120158903083667939 191576961180238354625501909)
                  ·
                    refine ⟨4490085027661836436535201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 191576961180238354625501909 4490085027661836436535201)
                    ·
                      refine ⟨3367563770746377327401401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490085027661836436535201 3367563770746377327401401)
                      ·
                        rfl

theorem cell23_6558307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_6558307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558307 prefixEnd_6558307 := by exact prefixLift 6558307
  have htrace : WordTrace (prefixWord ++ tailWord_6558307) baseStart_6558307 baseEnd_6558307 := by
    simpa [prefixWord, tailWord_6558307, baseEnd_6558307] using wordTrace_append hprefix tailTrace_6558307
  have hstable : (prefixWord ++ tailWord_6558307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558307).length < 2 ^ (prefixWord ++ tailWord_6558307).sum := by decide
  have hdescent : baseEnd_6558307 < baseStart_6558307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558337 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_6558337 : Nat := 118140960795 + 6558337 * 2 ^ 59
def prefixEnd_6558337 : Nat := 4983230072969 + 3 ^ 40 * 6558337 * 2
def baseEnd_6558337 : Nat := 3367579175166012210026263

theorem tailTrace_6558337 : CollatzResearch.WordTrace tailWord_6558337 prefixEnd_6558337 3367579175166012210026263 := by
  unfold tailWord_6558337
  simp only [CollatzResearch.WordTrace]
  refine ⟨239202201641272598631001265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159468134427515065754000843 239202201641272598631001265)
  ·
    refine ⟨179401651230954448973250949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239202201641272598631001265 179401651230954448973250949)
    ·
      refine ⟨33637809605803959182484553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179401651230954448973250949 33637809605803959182484553)
      ·
        refine ⟨25228357204352969386863415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33637809605803959182484553 25228357204352969386863415)
        ·
          refine ⟨37842535806529454080295123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25228357204352969386863415 37842535806529454080295123)
          ·
            refine ⟨56763803709794181120442685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37842535806529454080295123 56763803709794181120442685)
            ·
              refine ⟨21286426391172817920166007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56763803709794181120442685 21286426391172817920166007)
              ·
                refine ⟨31929639586759226880249011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21286426391172817920166007 31929639586759226880249011)
                ·
                  refine ⟨47894459380138840320373517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31929639586759226880249011 47894459380138840320373517)
                  ·
                    refine ⟨17960422267552065120140069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47894459380138840320373517 17960422267552065120140069)
                    ·
                      refine ⟨3367579175166012210026263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17960422267552065120140069 3367579175166012210026263)
                      ·
                        rfl

theorem cell23_6558337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_6558337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558337 prefixEnd_6558337 := by exact prefixLift 6558337
  have htrace : WordTrace (prefixWord ++ tailWord_6558337) baseStart_6558337 baseEnd_6558337 := by
    simpa [prefixWord, tailWord_6558337, baseEnd_6558337] using wordTrace_append hprefix tailTrace_6558337
  have hstable : (prefixWord ++ tailWord_6558337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558337).length < 2 ^ (prefixWord ++ tailWord_6558337).sum := by decide
  have hdescent : baseEnd_6558337 < baseStart_6558337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558364 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_6558364 : Nat := 118140960795 + 6558364 * 2 ^ 59
def prefixEnd_6558364 : Nat := 4983230072969 + 3 ^ 40 * 6558364 * 2
def baseEnd_6558364 : Nat := 1122531013047894534796213

theorem tailTrace_6558364 : CollatzResearch.WordTrace tailWord_6558364 prefixEnd_6558364 1122531013047894534796213 := by
  unfold tailWord_6558364
  simp only [CollatzResearch.WordTrace]
  refine ⟨119601593206087391121117073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159468790941449854828156097 119601593206087391121117073)
  ·
    refine ⟨89701194904565543340837805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119601593206087391121117073 89701194904565543340837805)
    ·
      refine ⟨33637948089212078752814177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89701194904565543340837805 33637948089212078752814177)
      ·
        refine ⟨25228461066909059064610633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33637948089212078752814177 25228461066909059064610633)
        ·
          refine ⟨18921345800181794298457975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25228461066909059064610633 18921345800181794298457975)
          ·
            refine ⟨28382018700272691447686963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18921345800181794298457975 28382018700272691447686963)
            ·
              refine ⟨42573028050409037171530445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28382018700272691447686963 42573028050409037171530445)
              ·
                refine ⟨15964885518903388939323917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42573028050409037171530445 15964885518903388939323917)
                ·
                  refine ⟨5986832069588770852246469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15964885518903388939323917 5986832069588770852246469)
                  ·
                    refine ⟨1122531013047894534796213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986832069588770852246469 1122531013047894534796213)
                    ·
                      rfl

theorem cell23_6558364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_6558364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558364 prefixEnd_6558364 := by exact prefixLift 6558364
  have htrace : WordTrace (prefixWord ++ tailWord_6558364) baseStart_6558364 baseEnd_6558364 := by
    simpa [prefixWord, tailWord_6558364, baseEnd_6558364] using wordTrace_append hprefix tailTrace_6558364
  have hstable : (prefixWord ++ tailWord_6558364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558364).length < 2 ^ (prefixWord ++ tailWord_6558364).sum := by decide
  have hdescent : baseEnd_6558364 < baseStart_6558364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558428 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 6]
def baseStart_6558428 : Nat := 118140960795 + 6558428 * 2 ^ 59
def prefixEnd_6558428 : Nat := 4983230072969 + 3 ^ 40 * 6558428 * 2
def baseEnd_6558428 : Nat := 374180655767285705998705

theorem tailTrace_6558428 : CollatzResearch.WordTrace tailWord_6558428 prefixEnd_6558428 374180655767285705998705 := by
  unfold tailWord_6558428
  simp only [CollatzResearch.WordTrace]
  refine ⟨119602760341971460586281969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159470347122628614115042625 119602760341971460586281969)
  ·
    refine ⟨89702070256478595439711477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119602760341971460586281969 89702070256478595439711477)
    ·
      refine ⟨8409569086544868322472951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89702070256478595439711477 8409569086544868322472951)
      ·
        refine ⟨12614353629817302483709427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8409569086544868322472951 12614353629817302483709427)
        ·
          refine ⟨18921530444725953725564141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12614353629817302483709427 18921530444725953725564141)
          ·
            refine ⟨7095573916772232647086553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18921530444725953725564141 7095573916772232647086553)
            ·
              refine ⟨5321680437579174485314915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095573916772232647086553 5321680437579174485314915)
              ·
                refine ⟨7982520656368761727972373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321680437579174485314915 7982520656368761727972373)
                ·
                  refine ⟨374180655767285705998705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7982520656368761727972373 374180655767285705998705)
                  ·
                    rfl

theorem cell23_6558428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_6558428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558428 prefixEnd_6558428 := by exact prefixLift 6558428
  have htrace : WordTrace (prefixWord ++ tailWord_6558428) baseStart_6558428 baseEnd_6558428 := by
    simpa [prefixWord, tailWord_6558428, baseEnd_6558428] using wordTrace_append hprefix tailTrace_6558428
  have hstable : (prefixWord ++ tailWord_6558428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558428).length < 2 ^ (prefixWord ++ tailWord_6558428).sum := by decide
  have hdescent : baseEnd_6558428 < baseStart_6558428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558454 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6558454 : Nat := 118140960795 + 6558454 * 2 ^ 59
def prefixEnd_6558454 : Nat := 4983230072969 + 3 ^ 40 * 6558454 * 2
def baseEnd_6558454 : Nat := 1122546417467529417421075

theorem tailTrace_6558454 : CollatzResearch.WordTrace tailWord_6558454 prefixEnd_6558454 1122546417467529417421075 := by
  unfold tailWord_6558454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14950404311365545475813151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159470979321232485075340277 14950404311365545475813151)
  ·
    refine ⟨22425606467048318213719727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14950404311365545475813151 22425606467048318213719727)
    ·
      refine ⟨33638409700572477320579591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22425606467048318213719727 33638409700572477320579591)
      ·
        refine ⟨50457614550858715980869387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33638409700572477320579591 50457614550858715980869387)
        ·
          refine ⟨75686421826288073971304081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50457614550858715980869387 75686421826288073971304081)
          ·
            refine ⟨56764816369716055478478061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75686421826288073971304081 56764816369716055478478061)
            ·
              refine ⟨21286806138643520804429273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56764816369716055478478061 21286806138643520804429273)
              ·
                refine ⟨15965104603982640603321955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21286806138643520804429273 15965104603982640603321955)
                ·
                  refine ⟨23947656905973960904982933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15965104603982640603321955 23947656905973960904982933)
                  ·
                    refine ⟨1122546417467529417421075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23947656905973960904982933 1122546417467529417421075)
                    ·
                      rfl

theorem cell23_6558454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6558454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558454 prefixEnd_6558454 := by exact prefixLift 6558454
  have htrace : WordTrace (prefixWord ++ tailWord_6558454) baseStart_6558454 baseEnd_6558454 := by
    simpa [prefixWord, tailWord_6558454, baseEnd_6558454] using wordTrace_append hprefix tailTrace_6558454
  have hstable : (prefixWord ++ tailWord_6558454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558454).length < 2 ^ (prefixWord ++ tailWord_6558454).sum := by decide
  have hdescent : baseEnd_6558454 < baseStart_6558454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558461 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_6558461 : Nat := 118140960795 + 6558461 * 2 ^ 59
def prefixEnd_6558461 : Nat := 4983230072969 + 3 ^ 40 * 6558461 * 2
def baseEnd_6558461 : Nat := 3367642846767169724875693

theorem tailTrace_6558461 : CollatzResearch.WordTrace tailWord_6558461 prefixEnd_6558461 3367642846767169724875693 := by
  unfold tailWord_6558461
  simp only [CollatzResearch.WordTrace]
  refine ⟨239206724292823367808515237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159471149528548911872343491 239206724292823367808515237)
  ·
    refine ⟨44851260804904381464096607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239206724292823367808515237 44851260804904381464096607)
    ·
      refine ⟨67276891207356572196144911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44851260804904381464096607 67276891207356572196144911)
      ·
        refine ⟨100915336811034858294217367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67276891207356572196144911 100915336811034858294217367)
        ·
          refine ⟨151373005216552287441326051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100915336811034858294217367 151373005216552287441326051)
          ·
            refine ⟨227059507824828431161989077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151373005216552287441326051 227059507824828431161989077)
            ·
              refine ⟨5321707214644416355359119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 227059507824828431161989077 5321707214644416355359119)
              ·
                refine ⟨7982560821966624533038679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321707214644416355359119 7982560821966624533038679)
                ·
                  refine ⟨11973841232949936799558019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982560821966624533038679 11973841232949936799558019)
                  ·
                    refine ⟨17960761849424905199337029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11973841232949936799558019 17960761849424905199337029)
                    ·
                      refine ⟨3367642846767169724875693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17960761849424905199337029 3367642846767169724875693)
                      ·
                        rfl

theorem cell23_6558461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_6558461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558461 prefixEnd_6558461 := by exact prefixLift 6558461
  have htrace : WordTrace (prefixWord ++ tailWord_6558461) baseStart_6558461 baseEnd_6558461 := by
    simpa [prefixWord, tailWord_6558461, baseEnd_6558461] using wordTrace_append hprefix tailTrace_6558461
  have hstable : (prefixWord ++ tailWord_6558461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558461).length < 2 ^ (prefixWord ++ tailWord_6558461).sum := by decide
  have hdescent : baseEnd_6558461 < baseStart_6558461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558471 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 2, 4]
def baseStart_6558471 : Nat := 118140960795 + 6558471 * 2 ^ 59
def prefixEnd_6558471 : Nat := 4983230072969 + 3 ^ 40 * 6558471 * 2
def baseEnd_6558471 : Nat := 1122549327191238228583549

theorem tailTrace_6558471 : CollatzResearch.WordTrace tailWord_6558471 prefixEnd_6558471 1122549327191238228583549 := by
  unfold tailWord_6558471
  simp only [CollatzResearch.WordTrace]
  refine ⟨239207089022787139516379267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159471392681858093010919511 239207089022787139516379267)
  ·
    refine ⟨358810633534180709274568901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239207089022787139516379267 358810633534180709274568901)
    ·
      refine ⟨67276993787658882988981669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358810633534180709274568901 67276993787658882988981669)
      ·
        refine ⟨12614436335186040560434063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67276993787658882988981669 12614436335186040560434063)
        ·
          refine ⟨18921654502779060840651095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12614436335186040560434063 18921654502779060840651095)
          ·
            refine ⟨28382481754168591260976643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18921654502779060840651095 28382481754168591260976643)
            ·
              refine ⟨42573722631252886891464965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28382481754168591260976643 42573722631252886891464965)
              ·
                refine ⟨7982572993359916292149681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42573722631252886891464965 7982572993359916292149681)
                ·
                  refine ⟨5986929745019937219112261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982572993359916292149681 5986929745019937219112261)
                  ·
                    refine ⟨1122549327191238228583549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986929745019937219112261 1122549327191238228583549)
                    ·
                      rfl

theorem cell23_6558471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_6558471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558471 prefixEnd_6558471 := by exact prefixLift 6558471
  have htrace : WordTrace (prefixWord ++ tailWord_6558471) baseStart_6558471 baseEnd_6558471 := by
    simpa [prefixWord, tailWord_6558471, baseEnd_6558471] using wordTrace_append hprefix tailTrace_6558471
  have hstable : (prefixWord ++ tailWord_6558471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558471).length < 2 ^ (prefixWord ++ tailWord_6558471).sum := by decide
  have hdescent : baseEnd_6558471 < baseStart_6558471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558497 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_6558497 : Nat := 118140960795 + 6558497 * 2 ^ 59
def prefixEnd_6558497 : Nat := 4983230072969 + 3 ^ 40 * 6558497 * 2
def baseEnd_6558497 : Nat := 1122553777356910528008509

theorem tailTrace_6558497 : CollatzResearch.WordTrace tailWord_6558497 prefixEnd_6558497 1122553777356910528008509 := by
  unfold tailWord_6558497
  simp only [CollatzResearch.WordTrace]
  refine ⟨239208037320692945956825745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159472024880461963971217163 239208037320692945956825745)
  ·
    refine ⟨179406027990519709467619309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239208037320692945956825745 179406027990519709467619309)
    ·
      refine ⟨67277260496444891050357241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179406027990519709467619309 67277260496444891050357241)
      ·
        refine ⟨50457945372333668287767931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67277260496444891050357241 50457945372333668287767931)
        ·
          refine ⟨75686918058500502431651897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50457945372333668287767931 75686918058500502431651897)
          ·
            refine ⟨56765188543875376823738923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75686918058500502431651897 56765188543875376823738923)
            ·
              refine ⟨85147782815813065235608385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56765188543875376823738923 85147782815813065235608385)
              ·
                refine ⟨63860837111859798926706289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85147782815813065235608385 63860837111859798926706289)
                ·
                  refine ⟨47895627833894849195029717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63860837111859798926706289 47895627833894849195029717)
                  ·
                    refine ⟨1122553777356910528008509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47895627833894849195029717 1122553777356910528008509)
                    ·
                      rfl

theorem cell23_6558497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_6558497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558497 prefixEnd_6558497 := by exact prefixLift 6558497
  have htrace : WordTrace (prefixWord ++ tailWord_6558497) baseStart_6558497 baseEnd_6558497 := by
    simpa [prefixWord, tailWord_6558497, baseEnd_6558497] using wordTrace_append hprefix tailTrace_6558497
  have hstable : (prefixWord ++ tailWord_6558497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558497).length < 2 ^ (prefixWord ++ tailWord_6558497).sum := by decide
  have hdescent : baseEnd_6558497 < baseStart_6558497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558545 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_6558545 : Nat := 118140960795 + 6558545 * 2 ^ 59
def prefixEnd_6558545 : Nat := 4983230072969 + 3 ^ 40 * 6558545 * 2
def baseEnd_6558545 : Nat := 3367685979142147396225307

theorem tailTrace_6558545 : CollatzResearch.WordTrace tailWord_6558545 prefixEnd_6558545 3367685979142147396225307 := by
  unfold tailWord_6558545
  simp only [CollatzResearch.WordTrace]
  refine ⟨239209788024519050154573089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159473192016346033436382059 239209788024519050154573089)
  ·
    refine ⟨179407341018389287615929817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239209788024519050154573089 179407341018389287615929817)
    ·
      refine ⟨134555505763791965711947363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179407341018389287615929817 134555505763791965711947363)
      ·
        refine ⟨201833258645687948567921045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134555505763791965711947363 201833258645687948567921045)
        ·
          refine ⟨9460933999016622589121299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201833258645687948567921045 9460933999016622589121299)
          ·
            refine ⟨14191400998524933883681949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9460933999016622589121299 14191400998524933883681949)
            ·
              refine ⟨5321775374446850206380731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14191400998524933883681949 5321775374446850206380731)
              ·
                refine ⟨7982663061670275309571097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321775374446850206380731 7982663061670275309571097)
                ·
                  refine ⟨5986997296252706482178323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982663061670275309571097 5986997296252706482178323)
                  ·
                    refine ⟨8980495944379059723267485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5986997296252706482178323 8980495944379059723267485)
                    ·
                      refine ⟨3367685979142147396225307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8980495944379059723267485 3367685979142147396225307)
                      ·
                        rfl

theorem cell23_6558545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_6558545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558545 prefixEnd_6558545 := by exact prefixLift 6558545
  have htrace : WordTrace (prefixWord ++ tailWord_6558545) baseStart_6558545 baseEnd_6558545 := by
    simpa [prefixWord, tailWord_6558545, baseEnd_6558545] using wordTrace_append hprefix tailTrace_6558545
  have hstable : (prefixWord ++ tailWord_6558545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558545).length < 2 ^ (prefixWord ++ tailWord_6558545).sum := by decide
  have hdescent : baseEnd_6558545 < baseStart_6558545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558568 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6558568 : Nat := 118140960795 + 6558568 * 2 ^ 59
def prefixEnd_6558568 : Nat := 4983230072969 + 3 ^ 40 * 6558568 * 2
def baseEnd_6558568 : Nat := 3367697789197200806237701

theorem tailTrace_6558568 : CollatzResearch.WordTrace tailWord_6558568 prefixEnd_6558568 3367697789197200806237701 := by
  unfold tailWord_6558568
  simp only [CollatzResearch.WordTrace]
  refine ⟨119605313451717862541330179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159473751268957150055106905 119605313451717862541330179)
  ·
    refine ⟨179407970177576793811995269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119605313451717862541330179 179407970177576793811995269)
    ·
      refine ⟨33638994408295648839749113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179407970177576793811995269 33638994408295648839749113)
      ·
        refine ⟨25229245806221736629811835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33638994408295648839749113 25229245806221736629811835)
        ·
          refine ⟨37843868709332604944717753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25229245806221736629811835 37843868709332604944717753)
          ·
            refine ⟨28382901531999453708538315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37843868709332604944717753 28382901531999453708538315)
            ·
              refine ⟨42574352297999180562807473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28382901531999453708538315 42574352297999180562807473)
              ·
                refine ⟨31930764223499385422105605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42574352297999180562807473 31930764223499385422105605)
                ·
                  refine ⟨5987018291906134766644801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31930764223499385422105605 5987018291906134766644801)
                  ·
                    refine ⟨4490263718929601074983601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987018291906134766644801 4490263718929601074983601)
                    ·
                      refine ⟨3367697789197200806237701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490263718929601074983601 3367697789197200806237701)
                      ·
                        rfl

theorem cell23_6558568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6558568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558568 prefixEnd_6558568 := by exact prefixLift 6558568
  have htrace : WordTrace (prefixWord ++ tailWord_6558568) baseStart_6558568 baseEnd_6558568 := by
    simpa [prefixWord, tailWord_6558568, baseEnd_6558568] using wordTrace_append hprefix tailTrace_6558568
  have hstable : (prefixWord ++ tailWord_6558568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558568).length < 2 ^ (prefixWord ++ tailWord_6558568).sum := by decide
  have hdescent : baseEnd_6558568 < baseStart_6558568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558584 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_6558584 : Nat := 118140960795 + 6558584 * 2 ^ 59
def prefixEnd_6558584 : Nat := 4983230072969 + 3 ^ 40 * 6558584 * 2
def baseEnd_6558584 : Nat := 3367706004887672743637627

theorem tailTrace_6558584 : CollatzResearch.WordTrace tailWord_6558584 prefixEnd_6558584 3367706004887672743637627 := by
  unfold tailWord_6558584
  simp only [CollatzResearch.WordTrace]
  refine ⟨119605605235688879907621403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159474140314251839876828537 119605605235688879907621403)
  ·
    refine ⟨179408407853533319861432105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119605605235688879907621403 179408407853533319861432105)
    ·
      refine ⟨134556305890149989896074079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179408407853533319861432105 134556305890149989896074079)
      ·
        refine ⟨201834458835224984844111119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134556305890149989896074079 201834458835224984844111119)
        ·
          refine ⟨302751688252837477266166679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201834458835224984844111119 302751688252837477266166679)
          ·
            refine ⟨454127532379256215899250019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302751688252837477266166679 454127532379256215899250019)
            ·
              refine ⟨681191298568884323848875029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454127532379256215899250019 681191298568884323848875029)
              ·
                refine ⟨31930842120416452680416017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 681191298568884323848875029 31930842120416452680416017)
                ·
                  refine ⟨23948131590312339510312013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31930842120416452680416017 23948131590312339510312013)
                  ·
                    refine ⟨8980549346367127316367005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23948131590312339510312013 8980549346367127316367005)
                    ·
                      refine ⟨3367706004887672743637627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8980549346367127316367005 3367706004887672743637627)
                      ·
                        rfl

theorem cell23_6558584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_6558584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558584 prefixEnd_6558584 := by exact prefixLift 6558584
  have htrace : WordTrace (prefixWord ++ tailWord_6558584) baseStart_6558584 baseEnd_6558584 := by
    simpa [prefixWord, tailWord_6558584, baseEnd_6558584] using wordTrace_append hprefix tailTrace_6558584
  have hstable : (prefixWord ++ tailWord_6558584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558584).length < 2 ^ (prefixWord ++ tailWord_6558584).sum := by decide
  have hdescent : baseEnd_6558584 < baseStart_6558584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558602 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6558602 : Nat := 118140960795 + 6558602 * 2 ^ 59
def prefixEnd_6558602 : Nat := 4983230072969 + 3 ^ 40 * 6558602 * 2
def baseEnd_6558602 : Nat := 3367715247539453673212545

theorem tailTrace_6558602 : CollatzResearch.WordTrace tailWord_6558602 prefixEnd_6558602 3367715247539453673212545 := by
  unfold tailWord_6558602
  simp only [CollatzResearch.WordTrace]
  refine ⟨59802966746328137222349515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159474577990208365926265373 59802966746328137222349515)
  ·
    refine ⟨89704450119492205833524273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59802966746328137222349515 89704450119492205833524273)
    ·
      refine ⟨67278337589619154375143205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89704450119492205833524273 67278337589619154375143205)
      ·
        refine ⟨12614688298053591445339351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67278337589619154375143205 12614688298053591445339351)
        ·
          refine ⟨18922032447080387168009027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12614688298053591445339351 18922032447080387168009027)
          ·
            refine ⟨28383048670620580752013541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18922032447080387168009027 28383048670620580752013541)
            ·
              refine ⟨5321821625741358891002539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28383048670620580752013541 5321821625741358891002539)
              ·
                refine ⟨7982732438612038336503809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321821625741358891002539 7982732438612038336503809)
                ·
                  refine ⟨5987049328959028752377857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982732438612038336503809 5987049328959028752377857)
                  ·
                    refine ⟨4490286996719271564283393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987049328959028752377857 4490286996719271564283393)
                    ·
                      refine ⟨3367715247539453673212545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490286996719271564283393 3367715247539453673212545)
                      ·
                        rfl

theorem cell23_6558602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6558602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558602 prefixEnd_6558602 := by exact prefixLift 6558602
  have htrace : WordTrace (prefixWord ++ tailWord_6558602) baseStart_6558602 baseEnd_6558602 := by
    simpa [prefixWord, tailWord_6558602, baseEnd_6558602] using wordTrace_append hprefix tailTrace_6558602
  have hstable : (prefixWord ++ tailWord_6558602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558602).length < 2 ^ (prefixWord ++ tailWord_6558602).sum := by decide
  have hdescent : baseEnd_6558602 < baseStart_6558602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558621 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6558621 : Nat := 118140960795 + 6558621 * 2 ^ 59
def prefixEnd_6558621 : Nat := 4983230072969 + 3 ^ 40 * 6558621 * 2
def baseEnd_6558621 : Nat := 1122575001223963032958319

theorem tailTrace_6558621 : CollatzResearch.WordTrace tailWord_6558621 prefixEnd_6558621 1122575001223963032958319 := by
  unfold tailWord_6558621
  simp only [CollatzResearch.WordTrace]
  refine ⟨239212559972243715134339717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159475039981495810089559811 239212559972243715134339717)
  ·
    refine ⟨44852354994795696587688697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239212559972243715134339717 44852354994795696587688697)
    ·
      refine ⟨33639266246096772440766523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44852354994795696587688697 33639266246096772440766523)
      ·
        refine ⟨50458899369145158661149785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33639266246096772440766523 50458899369145158661149785)
        ·
          refine ⟨37844174526858868995862339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50458899369145158661149785 37844174526858868995862339)
          ·
            refine ⟨56766261790288303493793509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37844174526858868995862339 56766261790288303493793509)
            ·
              refine ⟨10643674085679056905086283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56766261790288303493793509 10643674085679056905086283)
              ·
                refine ⟨15965511128518585357629425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10643674085679056905086283 15965511128518585357629425)
                ·
                  refine ⟨11974133346388939018222069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15965511128518585357629425 11974133346388939018222069)
                  ·
                    refine ⟨1122575001223963032958319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11974133346388939018222069 1122575001223963032958319)
                    ·
                      rfl

theorem cell23_6558621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6558621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558621 prefixEnd_6558621 := by exact prefixLift 6558621
  have htrace : WordTrace (prefixWord ++ tailWord_6558621) baseStart_6558621 baseEnd_6558621 := by
    simpa [prefixWord, tailWord_6558621, baseEnd_6558621] using wordTrace_append hprefix tailTrace_6558621
  have hstable : (prefixWord ++ tailWord_6558621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558621).length < 2 ^ (prefixWord ++ tailWord_6558621).sum := by decide
  have hdescent : baseEnd_6558621 < baseStart_6558621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558624 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6558624 : Nat := 118140960795 + 6558624 * 2 ^ 59
def prefixEnd_6558624 : Nat := 4983230072969 + 3 ^ 40 * 6558624 * 2
def baseEnd_6558624 : Nat := 3367726544113852587137443

theorem tailTrace_6558624 : CollatzResearch.WordTrace tailWord_6558624 prefixEnd_6558624 3367726544113852587137443 := by
  unfold tailWord_6558624
  simp only [CollatzResearch.WordTrace]
  refine ⟨119606334695616423323349463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159475112927488564431132617 119606334695616423323349463)
  ·
    refine ⟨179409502043424634985024195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119606334695616423323349463 179409502043424634985024195)
    ·
      refine ⟨269114253065136952477536293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179409502043424634985024195 269114253065136952477536293)
      ·
        refine ⟨50458922449713178589538055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269114253065136952477536293 50458922449713178589538055)
        ·
          refine ⟨75688383674569767884307083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50458922449713178589538055 75688383674569767884307083)
          ·
            refine ⟨113532575511854651826460625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75688383674569767884307083 113532575511854651826460625)
            ·
              refine ⟨85149431633890988869845469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113532575511854651826460625 85149431633890988869845469)
              ·
                refine ⟨31931036862709120826192051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85149431633890988869845469 31931036862709120826192051)
                ·
                  refine ⟨47896555294063681239288077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31931036862709120826192051 47896555294063681239288077)
                  ·
                    refine ⟨17961208235273880464733029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47896555294063681239288077 17961208235273880464733029)
                    ·
                      refine ⟨3367726544113852587137443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17961208235273880464733029 3367726544113852587137443)
                      ·
                        rfl

theorem cell23_6558624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6558624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558624 prefixEnd_6558624 := by exact prefixLift 6558624
  have htrace : WordTrace (prefixWord ++ tailWord_6558624) baseStart_6558624 baseEnd_6558624 := by
    simpa [prefixWord, tailWord_6558624, baseEnd_6558624] using wordTrace_append hprefix tailTrace_6558624
  have hstable : (prefixWord ++ tailWord_6558624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558624).length < 2 ^ (prefixWord ++ tailWord_6558624).sum := by decide
  have hdescent : baseEnd_6558624 < baseStart_6558624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558685 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_6558685 : Nat := 118140960795 + 6558685 * 2 ^ 59
def prefixEnd_6558685 : Nat := 4983230072969 + 3 ^ 40 * 6558685 * 2
def baseEnd_6558685 : Nat := 1122585955477925616158221

theorem tailTrace_6558685 : CollatzResearch.WordTrace tailWord_6558685 prefixEnd_6558685 1122585955477925616158221 := by
  unfold tailWord_6558685
  simp only [CollatzResearch.WordTrace]
  refine ⟨239214894244011854064669509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159476596162674569376446339 239214894244011854064669509)
  ·
    refine ⟨44852792670752222637125533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239214894244011854064669509 44852792670752222637125533)
    ·
      refine ⟨16819797251532083488922075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44852792670752222637125533 16819797251532083488922075)
      ·
        refine ⟨25229695877298125233383113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16819797251532083488922075 25229695877298125233383113)
        ·
          refine ⟨18922271907973593925037335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25229695877298125233383113 18922271907973593925037335)
          ·
            refine ⟨28383407861960390887556003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18922271907973593925037335 28383407861960390887556003)
            ·
              refine ⟨42575111792940586331334005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28383407861960390887556003 42575111792940586331334005)
              ·
                refine ⟨3991416730588179968562563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42575111792940586331334005 3991416730588179968562563)
                ·
                  refine ⟨5987125095882269952843845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991416730588179968562563 5987125095882269952843845)
                  ·
                    refine ⟨1122585955477925616158221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5987125095882269952843845 1122585955477925616158221)
                    ·
                      rfl

theorem cell23_6558685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_6558685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558685 prefixEnd_6558685 := by exact prefixLift 6558685
  have htrace : WordTrace (prefixWord ++ tailWord_6558685) baseStart_6558685 baseEnd_6558685 := by
    simpa [prefixWord, tailWord_6558685, baseEnd_6558685] using wordTrace_append hprefix tailTrace_6558685
  have hstable : (prefixWord ++ tailWord_6558685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558685).length < 2 ^ (prefixWord ++ tailWord_6558685).sum := by decide
  have hdescent : baseEnd_6558685 < baseStart_6558685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558698 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_6558698 : Nat := 118140960795 + 6558698 * 2 ^ 59
def prefixEnd_6558698 : Nat := 4983230072969 + 3 ^ 40 * 6558698 * 2
def baseEnd_6558698 : Nat := 374196060186920588623567

theorem tailTrace_6558698 : CollatzResearch.WordTrace tailWord_6558698 prefixEnd_6558698 374196060186920588623567 := by
  unfold tailWord_6558698
  simp only [CollatzResearch.WordTrace]
  refine ⟨59803842098241189321223187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159476912261976504856595165 59803842098241189321223187)
  ·
    refine ⟨89705763147361783981834781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59803842098241189321223187 89705763147361783981834781)
    ·
      refine ⟨33639661180260668993188043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89705763147361783981834781 33639661180260668993188043)
      ·
        refine ⟨50459491770391003489782065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33639661180260668993188043 50459491770391003489782065)
        ·
          refine ⟨37844618827793252617336549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50459491770391003489782065 37844618827793252617336549)
          ·
            refine ⟨7095866030211234865750603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37844618827793252617336549 7095866030211234865750603)
            ·
              refine ⟨10643799045316852298625905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095866030211234865750603 10643799045316852298625905)
              ·
                refine ⟨7982849283987639223969429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643799045316852298625905 7982849283987639223969429)
                ·
                  refine ⟨374196060186920588623567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7982849283987639223969429 374196060186920588623567)
                  ·
                    rfl

theorem cell23_6558698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_6558698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558698 prefixEnd_6558698 := by exact prefixLift 6558698
  have htrace : WordTrace (prefixWord ++ tailWord_6558698) baseStart_6558698 baseEnd_6558698 := by
    simpa [prefixWord, tailWord_6558698, baseEnd_6558698] using wordTrace_append hprefix tailTrace_6558698
  have hstable : (prefixWord ++ tailWord_6558698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558698).length < 2 ^ (prefixWord ++ tailWord_6558698).sum := by decide
  have hdescent : baseEnd_6558698 < baseStart_6558698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558728 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_6558728 : Nat := 118140960795 + 6558728 * 2 ^ 59
def prefixEnd_6558728 : Nat := 4983230072969 + 3 ^ 40 * 6558728 * 2
def baseEnd_6558728 : Nat := 1122593315367306726745655

theorem tailTrace_6558728 : CollatzResearch.WordTrace tailWord_6558728 prefixEnd_6558728 1122593315367306726745655 := by
  unfold tailWord_6558728
  simp only [CollatzResearch.WordTrace]
  refine ⟨119608231291428036204242419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159477641721904048272323225 119608231291428036204242419)
  ·
    refine ⟨179412346937142054306363629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119608231291428036204242419 179412346937142054306363629)
    ·
      refine ⟨67279630101428270364886361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179412346937142054306363629 67279630101428270364886361)
      ·
        refine ⟨50459722576071202773664771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67279630101428270364886361 50459722576071202773664771)
        ·
          refine ⟨75689583864106804160497157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50459722576071202773664771 75689583864106804160497157)
          ·
            refine ⟨14191796974520025780093217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75689583864106804160497157 14191796974520025780093217)
            ·
              refine ⟨10643847730890019335069913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14191796974520025780093217 10643847730890019335069913)
              ·
                refine ⟨7982885798167514501302435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643847730890019335069913 7982885798167514501302435)
                ·
                  refine ⟨11974328697251271751953653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982885798167514501302435 11974328697251271751953653)
                  ·
                    refine ⟨1122593315367306726745655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11974328697251271751953653 1122593315367306726745655)
                    ·
                      rfl

theorem cell23_6558728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_6558728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558728 prefixEnd_6558728 := by exact prefixLift 6558728
  have htrace : WordTrace (prefixWord ++ tailWord_6558728) baseStart_6558728 baseEnd_6558728 := by
    simpa [prefixWord, tailWord_6558728, baseEnd_6558728] using wordTrace_append hprefix tailTrace_6558728
  have hstable : (prefixWord ++ tailWord_6558728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558728).length < 2 ^ (prefixWord ++ tailWord_6558728).sum := by decide
  have hdescent : baseEnd_6558728 < baseStart_6558728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558751 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_6558751 : Nat := 118140960795 + 6558751 * 2 ^ 59
def prefixEnd_6558751 : Nat := 4983230072969 + 3 ^ 40 * 6558751 * 2
def baseEnd_6558751 : Nat := 3367791756156973590249359

theorem tailTrace_6558751 : CollatzResearch.WordTrace tailWord_6558751 prefixEnd_6558751 3367791756156973590249359 := by
  unfold tailWord_6558751
  simp only [CollatzResearch.WordTrace]
  refine ⟨239217301461772747336572107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159478200974515164891048071 239217301461772747336572107)
  ·
    refine ⟨358825952192659121004858161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239217301461772747336572107 358825952192659121004858161)
    ·
      refine ⟨269119464144494340753643621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358825952192659121004858161 269119464144494340753643621)
      ·
        refine ⟨50459899527092688891308179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269119464144494340753643621 50459899527092688891308179)
        ·
          refine ⟨75689849290639033336962269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50459899527092688891308179 75689849290639033336962269)
          ·
            refine ⟨28383693483989637501360851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75689849290639033336962269 28383693483989637501360851)
            ·
              refine ⟨42575540225984456252041277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28383693483989637501360851 42575540225984456252041277)
              ·
                refine ⟨15965827584744171094515479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42575540225984456252041277 15965827584744171094515479)
                ·
                  refine ⟨23948741377116256641773219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15965827584744171094515479 23948741377116256641773219)
                  ·
                    refine ⟨35923112065674384962659829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23948741377116256641773219 35923112065674384962659829)
                    ·
                      refine ⟨3367791756156973590249359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35923112065674384962659829 3367791756156973590249359)
                      ·
                        rfl

theorem cell23_6558751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_6558751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558751 prefixEnd_6558751 := by exact prefixLift 6558751
  have htrace : WordTrace (prefixWord ++ tailWord_6558751) baseStart_6558751 baseEnd_6558751 := by
    simpa [prefixWord, tailWord_6558751, baseEnd_6558751] using wordTrace_append hprefix tailTrace_6558751
  have hstable : (prefixWord ++ tailWord_6558751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558751).length < 2 ^ (prefixWord ++ tailWord_6558751).sum := by decide
  have hdescent : baseEnd_6558751 < baseStart_6558751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558752 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6558752 : Nat := 118140960795 + 6558752 * 2 ^ 59
def prefixEnd_6558752 : Nat := 4983230072969 + 3 ^ 40 * 6558752 * 2
def baseEnd_6558752 : Nat := 3367792269637628086336855

theorem tailTrace_6558752 : CollatzResearch.WordTrace tailWord_6558752 prefixEnd_6558752 3367792269637628086336855 := by
  unfold tailWord_6558752
  simp only [CollatzResearch.WordTrace]
  refine ⟨119608668967384562253679255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159478225289846083004905673 119608668967384562253679255)
  ·
    refine ⟨179413003451076843380518883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119608668967384562253679255 179413003451076843380518883)
    ·
      refine ⟨269119505176615265070778325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179413003451076843380518883 269119505176615265070778325)
      ·
        refine ⟨6307488402576920275096367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 269119505176615265070778325 6307488402576920275096367)
        ·
          refine ⟨9461232603865380412644551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6307488402576920275096367 9461232603865380412644551)
          ·
            refine ⟨14191848905798070618966827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461232603865380412644551 14191848905798070618966827)
            ·
              refine ⟨21287773358697105928450241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14191848905798070618966827 21287773358697105928450241)
              ·
                refine ⟨15965830019022829446337681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21287773358697105928450241 15965830019022829446337681)
                ·
                  refine ⟨11974372514267122084753261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15965830019022829446337681 11974372514267122084753261)
                  ·
                    refine ⟨4490389692850170781782473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11974372514267122084753261 4490389692850170781782473)
                    ·
                      refine ⟨3367792269637628086336855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490389692850170781782473 3367792269637628086336855)
                      ·
                        rfl

theorem cell23_6558752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6558752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558752 prefixEnd_6558752 := by exact prefixLift 6558752
  have htrace : WordTrace (prefixWord ++ tailWord_6558752) baseStart_6558752 baseEnd_6558752 := by
    simpa [prefixWord, tailWord_6558752, baseEnd_6558752] using wordTrace_append hprefix tailTrace_6558752
  have hstable : (prefixWord ++ tailWord_6558752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558752).length < 2 ^ (prefixWord ++ tailWord_6558752).sum := by decide
  have hdescent : baseEnd_6558752 < baseStart_6558752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558782 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6558782 : Nat := 118140960795 + 6558782 * 2 ^ 59
def prefixEnd_6558782 : Nat := 4983230072969 + 3 ^ 40 * 6558782 * 2
def baseEnd_6558782 : Nat := 3367807674057262968961717

theorem tailTrace_6558782 : CollatzResearch.WordTrace tailWord_6558782 prefixEnd_6558782 3367807674057262968961717 := by
  unfold tailWord_6558782
  simp only [CollatzResearch.WordTrace]
  refine ⟨29902304015582554953868825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159478954749773626420633733 29902304015582554953868825)
  ·
    refine ⟨22426728011686916215401619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29902304015582554953868825 22426728011686916215401619)
    ·
      refine ⟨33640092017530374323102429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22426728011686916215401619 33640092017530374323102429)
      ·
        refine ⟨12615034506573890371163411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33640092017530374323102429 12615034506573890371163411)
        ·
          refine ⟨18922551759860835556745117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12615034506573890371163411 18922551759860835556745117)
          ·
            refine ⟨7095956909947813333779419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18922551759860835556745117 7095956909947813333779419)
            ·
              refine ⟨10643935364921720000669129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095956909947813333779419 10643935364921720000669129)
              ·
                refine ⟨7982951523691290000501847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643935364921720000669129 7982951523691290000501847)
                ·
                  refine ⟨11974427285536935000752771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982951523691290000501847 11974427285536935000752771)
                  ·
                    refine ⟨17961640928305402501129157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11974427285536935000752771 17961640928305402501129157)
                    ·
                      refine ⟨3367807674057262968961717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17961640928305402501129157 3367807674057262968961717)
                      ·
                        rfl

theorem cell23_6558782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6558782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558782 prefixEnd_6558782 := by exact prefixLift 6558782
  have htrace : WordTrace (prefixWord ++ tailWord_6558782) baseStart_6558782 baseEnd_6558782 := by
    simpa [prefixWord, tailWord_6558782, baseEnd_6558782] using wordTrace_append hprefix tailTrace_6558782
  have hstable : (prefixWord ++ tailWord_6558782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558782).length < 2 ^ (prefixWord ++ tailWord_6558782).sum := by decide
  have hdescent : baseEnd_6558782 < baseStart_6558782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558785 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6558785 : Nat := 118140960795 + 6558785 * 2 ^ 59
def prefixEnd_6558785 : Nat := 4983230072969 + 3 ^ 40 * 6558785 * 2
def baseEnd_6558785 : Nat := 3367809214499226457224203

theorem tailTrace_6558785 : CollatzResearch.WordTrace tailWord_6558785 prefixEnd_6558785 3367809214499226457224203 := by
  unfold tailWord_6558785
  simp only [CollatzResearch.WordTrace]
  refine ⟨239218541543649571143309809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159479027695766380762206539 239218541543649571143309809)
  ·
    refine ⟨179413906157737178357482357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239218541543649571143309809 179413906157737178357482357)
    ·
      refine ⟨16820053702287860471013971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179413906157737178357482357 16820053702287860471013971)
      ·
        refine ⟨25230080553431790706520957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16820053702287860471013971 25230080553431790706520957)
        ·
          refine ⟨9461280207536921514945359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25230080553431790706520957 9461280207536921514945359)
          ·
            refine ⟨14191920311305382272418039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461280207536921514945359 14191920311305382272418039)
            ·
              refine ⟨21287880466958073408627059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14191920311305382272418039 21287880466958073408627059)
              ·
                refine ⟨31931820700437110112940589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21287880466958073408627059 31931820700437110112940589)
                ·
                  refine ⟨11974432762663916292352721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31931820700437110112940589 11974432762663916292352721)
                  ·
                    refine ⟨8980824571997937219264541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11974432762663916292352721 8980824571997937219264541)
                    ·
                      refine ⟨3367809214499226457224203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8980824571997937219264541 3367809214499226457224203)
                      ·
                        rfl

theorem cell23_6558785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6558785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558785 prefixEnd_6558785 := by exact prefixLift 6558785
  have htrace : WordTrace (prefixWord ++ tailWord_6558785) baseStart_6558785 baseEnd_6558785 := by
    simpa [prefixWord, tailWord_6558785, baseEnd_6558785] using wordTrace_append hprefix tailTrace_6558785
  have hstable : (prefixWord ++ tailWord_6558785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558785).length < 2 ^ (prefixWord ++ tailWord_6558785).sum := by decide
  have hdescent : baseEnd_6558785 < baseStart_6558785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558798 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_6558798 : Nat := 118140960795 + 6558798 * 2 ^ 59
def prefixEnd_6558798 : Nat := 4983230072969 + 3 ^ 40 * 6558798 * 2
def baseEnd_6558798 : Nat := 3367815889747734906361643

theorem tailTrace_6558798 : CollatzResearch.WordTrace tailWord_6558798 prefixEnd_6558798 3367815889747734906361643 := by
  unfold tailWord_6558798
  simp only [CollatzResearch.WordTrace]
  refine ⟨29902376961575309295441631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159479343795068316242355365 29902376961575309295441631)
  ·
    refine ⟨44853565442362963943162447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29902376961575309295441631 44853565442362963943162447)
    ·
      refine ⟨67280348163544445914743671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44853565442362963943162447 67280348163544445914743671)
      ·
        refine ⟨100920522245316668872115507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67280348163544445914743671 100920522245316668872115507)
        ·
          refine ⟨151380783367975003308173261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100920522245316668872115507 151380783367975003308173261)
          ·
            refine ⟨56767793762990626240564973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151380783367975003308173261 56767793762990626240564973)
            ·
              refine ⟨21287922661121484840211865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56767793762990626240564973 21287922661121484840211865)
              ·
                refine ⟨15965941995841113630158899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21287922661121484840211865 15965941995841113630158899)
                ·
                  refine ⟨23948912993761670445238349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15965941995841113630158899 23948912993761670445238349)
                  ·
                    refine ⟨8980842372660626416964381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23948912993761670445238349 8980842372660626416964381)
                    ·
                      refine ⟨3367815889747734906361643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8980842372660626416964381 3367815889747734906361643)
                      ·
                        rfl

theorem cell23_6558798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_6558798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558798 prefixEnd_6558798 := by exact prefixLift 6558798
  have htrace : WordTrace (prefixWord ++ tailWord_6558798) baseStart_6558798 baseEnd_6558798 := by
    simpa [prefixWord, tailWord_6558798, baseEnd_6558798] using wordTrace_append hprefix tailTrace_6558798
  have hstable : (prefixWord ++ tailWord_6558798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558798).length < 2 ^ (prefixWord ++ tailWord_6558798).sum := by decide
  have hdescent : baseEnd_6558798 < baseStart_6558798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558802 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_6558802 : Nat := 118140960795 + 6558802 * 2 ^ 59
def prefixEnd_6558802 : Nat := 4983230072969 + 3 ^ 40 * 6558802 * 2
def baseEnd_6558802 : Nat := 3367817943670352890711625

theorem tailTrace_6558802 : CollatzResearch.WordTrace tailWord_6558802 prefixEnd_6558802 3367817943670352890711625 := by
  unfold tailWord_6558802
  simp only [CollatzResearch.WordTrace]
  refine ⟨59804790396146995761669665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159479441056391988697785773 59804790396146995761669665)
  ·
    refine ⟨44853592797110246821252249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59804790396146995761669665 44853592797110246821252249)
    ·
      refine ⟨33640194597832685115939187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44853592797110246821252249 33640194597832685115939187)
      ·
        refine ⟨50460291896749027673908781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33640194597832685115939187 50460291896749027673908781)
        ·
          refine ⟨18922609461280885377715793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50460291896749027673908781 18922609461280885377715793)
          ·
            refine ⟨14191957095960664033286845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18922609461280885377715793 14191957095960664033286845)
            ·
              refine ⟨5321983910985249012482567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14191957095960664033286845 5321983910985249012482567)
              ·
                refine ⟨7982975866477873518723851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321983910985249012482567 7982975866477873518723851)
                ·
                  refine ⟨11974463799716810278085777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982975866477873518723851 11974463799716810278085777)
                  ·
                    refine ⟨8980847849787607708564333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11974463799716810278085777 8980847849787607708564333)
                    ·
                      refine ⟨3367817943670352890711625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8980847849787607708564333 3367817943670352890711625)
                      ·
                        rfl

theorem cell23_6558802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_6558802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558802 prefixEnd_6558802 := by exact prefixLift 6558802
  have htrace : WordTrace (prefixWord ++ tailWord_6558802) baseStart_6558802 baseEnd_6558802 := by
    simpa [prefixWord, tailWord_6558802, baseEnd_6558802] using wordTrace_append hprefix tailTrace_6558802
  have hstable : (prefixWord ++ tailWord_6558802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558802).length < 2 ^ (prefixWord ++ tailWord_6558802).sum := by decide
  have hdescent : baseEnd_6558802 < baseStart_6558802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558815 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 3]
def baseStart_6558815 : Nat := 118140960795 + 6558815 * 2 ^ 59
def prefixEnd_6558815 : Nat := 4983230072969 + 3 ^ 40 * 6558815 * 2
def baseEnd_6558815 : Nat := 3367824618918861339849065

theorem tailTrace_6558815 : CollatzResearch.WordTrace tailWord_6558815 prefixEnd_6558815 3367824618918861339849065 := by
  unfold tailWord_6558815
  simp only [CollatzResearch.WordTrace]
  refine ⟨239219635733540886266901899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159479757155693924177934599 239219635733540886266901899)
  ·
    refine ⟨358829453600311329400352849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239219635733540886266901899 358829453600311329400352849)
    ·
      refine ⟨269122090200233497050264637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358829453600311329400352849 269122090200233497050264637)
      ·
        refine ⟨100920783825087561393849239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269122090200233497050264637 100920783825087561393849239)
        ·
          refine ⟨151381175737631342090773859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100920783825087561393849239 151381175737631342090773859)
          ·
            refine ⟨227071763606447013136160789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151381175737631342090773859 227071763606447013136160789)
            ·
              refine ⟨10643988919052203740757537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 227071763606447013136160789 10643988919052203740757537)
              ·
                refine ⟨7982991689289152805568153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643988919052203740757537 7982991689289152805568153)
                ·
                  refine ⟨5987243766966864604176115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982991689289152805568153 5987243766966864604176115)
                  ·
                    refine ⟨8980865650450296906264173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987243766966864604176115 8980865650450296906264173)
                    ·
                      refine ⟨3367824618918861339849065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8980865650450296906264173 3367824618918861339849065)
                      ·
                        rfl

theorem cell23_6558815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_6558815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558815 prefixEnd_6558815 := by exact prefixLift 6558815
  have htrace : WordTrace (prefixWord ++ tailWord_6558815) baseStart_6558815 baseEnd_6558815 := by
    simpa [prefixWord, tailWord_6558815, baseEnd_6558815] using wordTrace_append hprefix tailTrace_6558815
  have hstable : (prefixWord ++ tailWord_6558815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558815).length < 2 ^ (prefixWord ++ tailWord_6558815).sum := by decide
  have hdescent : baseEnd_6558815 < baseStart_6558815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558818 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6558818 : Nat := 118140960795 + 6558818 * 2 ^ 59
def prefixEnd_6558818 : Nat := 4983230072969 + 3 ^ 40 * 6558818 * 2
def baseEnd_6558818 : Nat := 1122608719786941609370517

theorem tailTrace_6558818 : CollatzResearch.WordTrace tailWord_6558818 prefixEnd_6558818 1122608719786941609370517 := by
  unfold tailWord_6558818
  simp only [CollatzResearch.WordTrace]
  refine ⟨59804936288132504444815277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159479830101686678519507405 59804936288132504444815277)
  ·
    refine ⟨22426851108049689166805729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59804936288132504444815277 22426851108049689166805729)
    ·
      refine ⟨16820138331037266875104297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22426851108049689166805729 16820138331037266875104297)
      ·
        refine ⟨12615103748277950156328223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16820138331037266875104297 12615103748277950156328223)
        ·
          refine ⟨18922655622416925234492335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12615103748277950156328223 18922655622416925234492335)
          ·
            refine ⟨28383983433625387851738503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18922655622416925234492335 28383983433625387851738503)
            ·
              refine ⟨42575975150438081777607755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28383983433625387851738503 42575975150438081777607755)
              ·
                refine ⟨63863962725657122666411633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42575975150438081777607755 63863962725657122666411633)
                ·
                  refine ⟨47897972044242841999808725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63863962725657122666411633 47897972044242841999808725)
                  ·
                    refine ⟨1122608719786941609370517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47897972044242841999808725 1122608719786941609370517)
                    ·
                      rfl

theorem cell23_6558818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6558818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558818 prefixEnd_6558818 := by exact prefixLift 6558818
  have htrace : WordTrace (prefixWord ++ tailWord_6558818) baseStart_6558818 baseEnd_6558818 := by
    simpa [prefixWord, tailWord_6558818, baseEnd_6558818] using wordTrace_append hprefix tailTrace_6558818
  have hstable : (prefixWord ++ tailWord_6558818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558818).length < 2 ^ (prefixWord ++ tailWord_6558818).sum := by decide
  have hdescent : baseEnd_6558818 < baseStart_6558818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558821 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6558821 : Nat := 118140960795 + 6558821 * 2 ^ 59
def prefixEnd_6558821 : Nat := 4983230072969 + 3 ^ 40 * 6558821 * 2
def baseEnd_6558821 : Nat := 3367827699802788316374037

theorem tailTrace_6558821 : CollatzResearch.WordTrace tailWord_6558821 prefixEnd_6558821 3367827699802788316374037 := by
  unfold tailWord_6558821
  simp only [CollatzResearch.WordTrace]
  refine ⟨239219854571519149291620317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159479903047679432861080211 239219854571519149291620317)
  ·
    refine ⟨89707445464319680984357619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239219854571519149291620317 89707445464319680984357619)
    ·
      refine ⟨134561168196479521476536429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89707445464319680984357619 134561168196479521476536429)
      ·
        refine ⟨50460438073679820553701161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134561168196479521476536429 50460438073679820553701161)
        ·
          refine ⟨37845328555259865415275871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50460438073679820553701161 37845328555259865415275871)
          ·
            refine ⟨56767992832889798122913807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37845328555259865415275871 56767992832889798122913807)
            ·
              refine ⟨85151989249334697184370711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56767992832889798122913807 85151989249334697184370711)
              ·
                refine ⟨127727983874002045776556067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85151989249334697184370711 127727983874002045776556067)
                ·
                  refine ⟨191591975811003068664834101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127727983874002045776556067 191591975811003068664834101)
                  ·
                    refine ⟨17961747732281537687328197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 191591975811003068664834101 17961747732281537687328197)
                    ·
                      refine ⟨3367827699802788316374037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17961747732281537687328197 3367827699802788316374037)
                      ·
                        rfl

theorem cell23_6558821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6558821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558821 prefixEnd_6558821 := by exact prefixLift 6558821
  have htrace : WordTrace (prefixWord ++ tailWord_6558821) baseStart_6558821 baseEnd_6558821 := by
    simpa [prefixWord, tailWord_6558821, baseEnd_6558821] using wordTrace_append hprefix tailTrace_6558821
  have hstable : (prefixWord ++ tailWord_6558821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558821).length < 2 ^ (prefixWord ++ tailWord_6558821).sum := by decide
  have hdescent : baseEnd_6558821 < baseStart_6558821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558831 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 2, 6]
def baseStart_6558831 : Nat := 118140960795 + 6558831 * 2 ^ 59
def prefixEnd_6558831 : Nat := 4983230072969 + 3 ^ 40 * 6558831 * 2
def baseEnd_6558831 : Nat := 1122610944869777759082997

theorem tailTrace_6558831 : CollatzResearch.WordTrace tailWord_6558831 prefixEnd_6558831 1122610944869777759082997 := by
  unfold tailWord_6558831
  simp only [CollatzResearch.WordTrace]
  refine ⟨239220219301482920999484347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159480146200988613999656231 239220219301482920999484347)
  ·
    refine ⟨358830328952224381499226521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239220219301482920999484347 358830328952224381499226521)
    ·
      refine ⟨269122746714168286124419891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358830328952224381499226521 269122746714168286124419891)
      ·
        refine ⟨403684120071252429186629837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269122746714168286124419891 403684120071252429186629837)
        ·
          refine ⟨151381545026719660944986189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403684120071252429186629837 151381545026719660944986189)
          ·
            refine ⟨56768079385019872854369821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151381545026719660944986189 56768079385019872854369821)
            ·
              refine ⟨21288029769382452320388683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56768079385019872854369821 21288029769382452320388683)
              ·
                refine ⟨31932044654073678480583025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21288029769382452320388683 31932044654073678480583025)
                ·
                  refine ⟨23949033490555258860437269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31932044654073678480583025 23949033490555258860437269)
                  ·
                    refine ⟨1122610944869777759082997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23949033490555258860437269 1122610944869777759082997)
                    ·
                      rfl

theorem cell23_6558831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_6558831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558831 prefixEnd_6558831 := by exact prefixLift 6558831
  have htrace : WordTrace (prefixWord ++ tailWord_6558831) baseStart_6558831 baseEnd_6558831 := by
    simpa [prefixWord, tailWord_6558831, baseEnd_6558831] using wordTrace_append hprefix tailTrace_6558831
  have hstable : (prefixWord ++ tailWord_6558831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558831).length < 2 ^ (prefixWord ++ tailWord_6558831).sum := by decide
  have hdescent : baseEnd_6558831 < baseStart_6558831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558838 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6558838 : Nat := 118140960795 + 6558838 * 2 ^ 59
def prefixEnd_6558838 : Nat := 4983230072969 + 3 ^ 40 * 6558838 * 2
def baseEnd_6558838 : Nat := 3367836428973914749861459

theorem tailTrace_6558838 : CollatzResearch.WordTrace tailWord_6558838 prefixEnd_6558838 3367836428973914749861459 := by
  unfold tailWord_6558838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14951279663278597574686823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159480316408305040796659445 14951279663278597574686823)
  ·
    refine ⟨22426919494917896362030235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14951279663278597574686823 22426919494917896362030235)
    ·
      refine ⟨33640379242376844543045353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22426919494917896362030235 33640379242376844543045353)
      ·
        refine ⟨25230284431782633407284015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33640379242376844543045353 25230284431782633407284015)
        ·
          refine ⟨37845426647673950110926023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25230284431782633407284015 37845426647673950110926023)
          ·
            refine ⟨56768139971510925166389035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37845426647673950110926023 56768139971510925166389035)
            ·
              refine ⟨85152209957266387749583553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56768139971510925166389035 85152209957266387749583553)
              ·
                refine ⟨63864157467949790812187665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85152209957266387749583553 63864157467949790812187665)
                ·
                  refine ⟨47898118100962343109140749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63864157467949790812187665 47898118100962343109140749)
                  ·
                    refine ⟨17961794287860878665927781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47898118100962343109140749 17961794287860878665927781)
                    ·
                      refine ⟨3367836428973914749861459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17961794287860878665927781 3367836428973914749861459)
                      ·
                        rfl

theorem cell23_6558838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6558838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558838 prefixEnd_6558838 := by exact prefixLift 6558838
  have htrace : WordTrace (prefixWord ++ tailWord_6558838) baseStart_6558838 baseEnd_6558838 := by
    simpa [prefixWord, tailWord_6558838, baseEnd_6558838] using wordTrace_append hprefix tailTrace_6558838
  have hstable : (prefixWord ++ tailWord_6558838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558838).length < 2 ^ (prefixWord ++ tailWord_6558838).sum := by decide
  have hdescent : baseEnd_6558838 < baseStart_6558838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558851 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_6558851 : Nat := 118140960795 + 6558851 * 2 ^ 59
def prefixEnd_6558851 : Nat := 4983230072969 + 3 ^ 40 * 6558851 * 2
def baseEnd_6558851 : Nat := 3367843104222423198998899

theorem tailTrace_6558851 : CollatzResearch.WordTrace tailWord_6558851 prefixEnd_6558851 3367843104222423198998899 := by
  unfold tailWord_6558851
  simp only [CollatzResearch.WordTrace]
  refine ⟨239220948761410464415212407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159480632507606976276808271 239220948761410464415212407)
  ·
    refine ⟨358831423142115696622818611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239220948761410464415212407 358831423142115696622818611)
    ·
      refine ⟨538247134713173544934227917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358831423142115696622818611 538247134713173544934227917)
      ·
        refine ⟨201842675517440079350335469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538247134713173544934227917 201842675517440079350335469)
        ·
          refine ⟨75691003319040029756375801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201842675517440079350335469 75691003319040029756375801)
          ·
            refine ⟨56768252489280022317281851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75691003319040029756375801 56768252489280022317281851)
            ·
              refine ⟨85152378733920033475922777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56768252489280022317281851 85152378733920033475922777)
              ·
                refine ⟨63864284050440025106942083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85152378733920033475922777 63864284050440025106942083)
                ·
                  refine ⟨95796426075660037660413125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63864284050440025106942083 95796426075660037660413125)
                  ·
                    refine ⟨17961829889186257061327461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95796426075660037660413125 17961829889186257061327461)
                    ·
                      refine ⟨3367843104222423198998899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17961829889186257061327461 3367843104222423198998899)
                      ·
                        rfl

theorem cell23_6558851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_6558851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558851 prefixEnd_6558851 := by exact prefixLift 6558851
  have htrace : WordTrace (prefixWord ++ tailWord_6558851) baseStart_6558851 baseEnd_6558851 := by
    simpa [prefixWord, tailWord_6558851, baseEnd_6558851] using wordTrace_append hprefix tailTrace_6558851
  have hstable : (prefixWord ++ tailWord_6558851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558851).length < 2 ^ (prefixWord ++ tailWord_6558851).sum := by decide
  have hdescent : baseEnd_6558851 < baseStart_6558851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558855 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_6558855 : Nat := 118140960795 + 6558855 * 2 ^ 59
def prefixEnd_6558855 : Nat := 4983230072969 + 3 ^ 40 * 6558855 * 2
def baseEnd_6558855 : Nat := 3367845158145041183348881

theorem tailTrace_6558855 : CollatzResearch.WordTrace tailWord_6558855 prefixEnd_6558855 3367845158145041183348881 := by
  unfold tailWord_6558855
  simp only [CollatzResearch.WordTrace]
  refine ⟨239221094653395973098358019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159480729768930648732238679 239221094653395973098358019)
  ·
    refine ⟨358831641980093959647537029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239221094653395973098358019 358831641980093959647537029)
    ·
      refine ⟨67280932871267617433913193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358831641980093959647537029 67280932871267617433913193)
      ·
        refine ⟨50460699653450713075434895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67280932871267617433913193 50460699653450713075434895)
        ·
          refine ⟨75691049480176069613152343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50460699653450713075434895 75691049480176069613152343)
          ·
            refine ⟨113536574220264104419728515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75691049480176069613152343 113536574220264104419728515)
            ·
              refine ⟨170304861330396156629592773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113536574220264104419728515 170304861330396156629592773)
              ·
                refine ⟨31932161499449279368048645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170304861330396156629592773 31932161499449279368048645)
                ·
                  refine ⟨5987280281146739881509121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31932161499449279368048645 5987280281146739881509121)
                  ·
                    refine ⟨4490460210860054911131841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987280281146739881509121 4490460210860054911131841)
                    ·
                      refine ⟨3367845158145041183348881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490460210860054911131841 3367845158145041183348881)
                      ·
                        rfl

theorem cell23_6558855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_6558855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558855 prefixEnd_6558855 := by exact prefixLift 6558855
  have htrace : WordTrace (prefixWord ++ tailWord_6558855) baseStart_6558855 baseEnd_6558855 := by
    simpa [prefixWord, tailWord_6558855, baseEnd_6558855] using wordTrace_append hprefix tailTrace_6558855
  have hstable : (prefixWord ++ tailWord_6558855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558855).length < 2 ^ (prefixWord ++ tailWord_6558855).sum := by decide
  have hdescent : baseEnd_6558855 < baseStart_6558855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558872 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6558872 : Nat := 118140960795 + 6558872 * 2 ^ 59
def prefixEnd_6558872 : Nat := 4983230072969 + 3 ^ 40 * 6558872 * 2
def baseEnd_6558872 : Nat := 3367853887316167616836303

theorem tailTrace_6558872 : CollatzResearch.WordTrace tailWord_6558872 prefixEnd_6558872 3367853887316167616836303 := by
  unfold tailWord_6558872
  simp only [CollatzResearch.WordTrace]
  refine ⟨119610857347167192500863435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159481143129556256667817913 119610857347167192500863435)
  ·
    refine ⟨179416286020750788751295153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119610857347167192500863435 179416286020750788751295153)
    ·
      refine ⟨134562214515563091563471365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179416286020750788751295153 134562214515563091563471365)
      ·
        refine ⟨25230415221668079668150881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134562214515563091563471365 25230415221668079668150881)
        ·
          refine ⟨18922811416251059751113161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25230415221668079668150881 18922811416251059751113161)
          ·
            refine ⟨14192108562188294813334871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18922811416251059751113161 14192108562188294813334871)
            ·
              refine ⟨21288162843282442220002307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14192108562188294813334871 21288162843282442220002307)
              ·
                refine ⟨31932244264923663330003461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21288162843282442220002307 31932244264923663330003461)
                ·
                  refine ⟨5987295799673186874375649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31932244264923663330003461 5987295799673186874375649)
                  ·
                    refine ⟨4490471849754890155781737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987295799673186874375649 4490471849754890155781737)
                    ·
                      refine ⟨3367853887316167616836303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490471849754890155781737 3367853887316167616836303)
                      ·
                        rfl

theorem cell23_6558872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6558872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558872 prefixEnd_6558872 := by exact prefixLift 6558872
  have htrace : WordTrace (prefixWord ++ tailWord_6558872) baseStart_6558872 baseEnd_6558872 := by
    simpa [prefixWord, tailWord_6558872, baseEnd_6558872] using wordTrace_append hprefix tailTrace_6558872
  have hstable : (prefixWord ++ tailWord_6558872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558872).length < 2 ^ (prefixWord ++ tailWord_6558872).sum := by decide
  have hdescent : baseEnd_6558872 < baseStart_6558872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558908 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_6558908 : Nat := 118140960795 + 6558908 * 2 ^ 59
def prefixEnd_6558908 : Nat := 4983230072969 + 3 ^ 40 * 6558908 * 2
def baseEnd_6558908 : Nat := 1122624124206576491995379

theorem tailTrace_6558908 : CollatzResearch.WordTrace tailWord_6558908 prefixEnd_6558908 1122624124206576491995379 := by
  unfold tailWord_6558908
  simp only [CollatzResearch.WordTrace]
  refine ⟨119611513861101981575018689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159482018481469308766691585 119611513861101981575018689)
  ·
    refine ⟨89708635395826486181264017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119611513861101981575018689 89708635395826486181264017)
    ·
      refine ⟨67281476546869864635948013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89708635395826486181264017 67281476546869864635948013)
      ·
        refine ⟨25230553705076199238480505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67281476546869864635948013 25230553705076199238480505)
        ·
          refine ⟨18922915278807149428860379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25230553705076199238480505 18922915278807149428860379)
          ·
            refine ⟨28384372918210724143290569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18922915278807149428860379 28384372918210724143290569)
            ·
              refine ⟨21288279688658043107467927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28384372918210724143290569 21288279688658043107467927)
              ·
                refine ⟨31932419532987064661201891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21288279688658043107467927 31932419532987064661201891)
                ·
                  refine ⟨47898629299480596991802837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31932419532987064661201891 47898629299480596991802837)
                  ·
                    refine ⟨1122624124206576491995379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47898629299480596991802837 1122624124206576491995379)
                    ·
                      rfl

theorem cell23_6558908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_6558908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558908 prefixEnd_6558908 := by exact prefixLift 6558908
  have htrace : WordTrace (prefixWord ++ tailWord_6558908) baseStart_6558908 baseEnd_6558908 := by
    simpa [prefixWord, tailWord_6558908, baseEnd_6558908] using wordTrace_append hprefix tailTrace_6558908
  have hstable : (prefixWord ++ tailWord_6558908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558908).length < 2 ^ (prefixWord ++ tailWord_6558908).sum := by decide
  have hdescent : baseEnd_6558908 < baseStart_6558908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558912 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 5]
def baseStart_6558912 : Nat := 118140960795 + 6558912 * 2 ^ 59
def prefixEnd_6558912 : Nat := 4983230072969 + 3 ^ 40 * 6558912 * 2
def baseEnd_6558912 : Nat := 374208269615816384481791

theorem tailTrace_6558912 : CollatzResearch.WordTrace tailWord_6558912 prefixEnd_6558912 374208269615816384481791 := by
  unfold tailWord_6558912
  simp only [CollatzResearch.WordTrace]
  refine ⟨119611586807094735916591495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159482115742792981222121993 119611586807094735916591495)
  ·
    refine ⟨179417380210642103874887243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119611586807094735916591495 179417380210642103874887243)
    ·
      refine ⟨269126070315963155812330865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179417380210642103874887243 269126070315963155812330865)
      ·
        refine ⟨201844552736972366859248149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269126070315963155812330865 201844552736972366859248149)
        ·
          refine ⟨9461463409545579696527257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201844552736972366859248149 9461463409545579696527257)
          ·
            refine ⟨7096097557159184772395443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9461463409545579696527257 7096097557159184772395443)
            ·
              refine ⟨10644146335738777158593165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096097557159184772395443 10644146335738777158593165)
              ·
                refine ⟨3991554875902041434472437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10644146335738777158593165 3991554875902041434472437)
                ·
                  refine ⟨374208269615816384481791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3991554875902041434472437 374208269615816384481791)
                  ·
                    rfl

theorem cell23_6558912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 5].length) (baseStart_6558912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558912 prefixEnd_6558912 := by exact prefixLift 6558912
  have htrace : WordTrace (prefixWord ++ tailWord_6558912) baseStart_6558912 baseEnd_6558912 := by
    simpa [prefixWord, tailWord_6558912, baseEnd_6558912] using wordTrace_append hprefix tailTrace_6558912
  have hstable : (prefixWord ++ tailWord_6558912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558912).length < 2 ^ (prefixWord ++ tailWord_6558912).sum := by decide
  have hdescent : baseEnd_6558912 < baseStart_6558912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558931 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_6558931 : Nat := 118140960795 + 6558931 * 2 ^ 59
def prefixEnd_6558931 : Nat := 4983230072969 + 3 ^ 40 * 6558931 * 2
def baseEnd_6558931 : Nat := 3367884182674782885998531

theorem tailTrace_6558931 : CollatzResearch.WordTrace tailWord_6558931 prefixEnd_6558931 3367884182674782885998531 := by
  unfold tailWord_6558931
  simp only [CollatzResearch.WordTrace]
  refine ⟨239223866601120638078124647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159482577734080425385416431 239223866601120638078124647)
  ·
    refine ⟨358835799901680957117186971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239223866601120638078124647 358835799901680957117186971)
    ·
      refine ⟨538253699852521435675780457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358835799901680957117186971 538253699852521435675780457)
      ·
        refine ⟨403690274889391076756835343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538253699852521435675780457 403690274889391076756835343)
        ·
          refine ⟨605535412334086615135253015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403690274889391076756835343 605535412334086615135253015)
          ·
            refine ⟨908303118501129922702879523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605535412334086615135253015 908303118501129922702879523)
            ·
              refine ⟨1362454677751694884054319285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908303118501129922702879523 1362454677751694884054319285)
              ·
                refine ⟨127730126039221395380092433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1362454677751694884054319285 127730126039221395380092433)
                ·
                  refine ⟨95797594529416046535069325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127730126039221395380092433 95797594529416046535069325)
                  ·
                    refine ⟨35924097948531017450650997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95797594529416046535069325 35924097948531017450650997)
                    ·
                      refine ⟨3367884182674782885998531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35924097948531017450650997 3367884182674782885998531)
                      ·
                        rfl

theorem cell23_6558931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_6558931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558931 prefixEnd_6558931 := by exact prefixLift 6558931
  have htrace : WordTrace (prefixWord ++ tailWord_6558931) baseStart_6558931 baseEnd_6558931 := by
    simpa [prefixWord, tailWord_6558931, baseEnd_6558931] using wordTrace_append hprefix tailTrace_6558931
  have hstable : (prefixWord ++ tailWord_6558931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558931).length < 2 ^ (prefixWord ++ tailWord_6558931).sum := by decide
  have hdescent : baseEnd_6558931 < baseStart_6558931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558948 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_6558948 : Nat := 118140960795 + 6558948 * 2 ^ 59
def prefixEnd_6558948 : Nat := 4983230072969 + 3 ^ 40 * 6558948 * 2
def baseEnd_6558948 : Nat := 3367892911845909319485953

theorem tailTrace_6558948 : CollatzResearch.WordTrace tailWord_6558948 prefixEnd_6558948 3367892911845909319485953 := by
  unfold tailWord_6558948
  simp only [CollatzResearch.WordTrace]
  refine ⟨119612243321029524990746749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159482991094706033320995665 119612243321029524990746749)
  ·
    refine ⟨44854591245386071871530031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119612243321029524990746749 44854591245386071871530031)
    ·
      refine ⟨67281886868079107807295047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44854591245386071871530031 67281886868079107807295047)
      ·
        refine ⟨100922830302118661710942571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67281886868079107807295047 100922830302118661710942571)
        ·
          refine ⟨151384245453177992566413857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100922830302118661710942571 151384245453177992566413857)
          ·
            refine ⟨113538184089883494424810393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151384245453177992566413857 113538184089883494424810393)
            ·
              refine ⟨85153638067412620818607795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113538184089883494424810393 85153638067412620818607795)
              ·
                refine ⟨127730457101118931227911693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85153638067412620818607795 127730457101118931227911693)
                ·
                  refine ⟨47898921412919599210466885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127730457101118931227911693 47898921412919599210466885)
                  ·
                    refine ⟨8981047764922424851962541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47898921412919599210466885 8981047764922424851962541)
                    ·
                      refine ⟨3367892911845909319485953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981047764922424851962541 3367892911845909319485953)
                      ·
                        rfl

theorem cell23_6558948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_6558948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558948 prefixEnd_6558948 := by exact prefixLift 6558948
  have htrace : WordTrace (prefixWord ++ tailWord_6558948) baseStart_6558948 baseEnd_6558948 := by
    simpa [prefixWord, tailWord_6558948, baseEnd_6558948] using wordTrace_append hprefix tailTrace_6558948
  have hstable : (prefixWord ++ tailWord_6558948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558948).length < 2 ^ (prefixWord ++ tailWord_6558948).sum := by decide
  have hdescent : baseEnd_6558948 < baseStart_6558948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558958 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6558958 : Nat := 118140960795 + 6558958 * 2 ^ 59
def prefixEnd_6558958 : Nat := 4983230072969 + 3 ^ 40 * 6558958 * 2
def baseEnd_6558958 : Nat := 3367898046652454280360907

theorem tailTrace_6558958 : CollatzResearch.WordTrace tailWord_6558958 prefixEnd_6558958 3367898046652454280360907 := by
  unfold tailWord_6558958
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903106421502852711169691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159483234248015214459571685 29903106421502852711169691)
  ·
    refine ⟨44854659632254279066754537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29903106421502852711169691 44854659632254279066754537)
    ·
      refine ⟨33640994724190709300065903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44854659632254279066754537 33640994724190709300065903)
      ·
        refine ⟨50461492086286063950098855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33640994724190709300065903 50461492086286063950098855)
        ·
          refine ⟨75692238129429095925148283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50461492086286063950098855 75692238129429095925148283)
          ·
            refine ⟨113538357194143643887722425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75692238129429095925148283 113538357194143643887722425)
            ·
              refine ⟨85153767895607732915791819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113538357194143643887722425 85153767895607732915791819)
              ·
                refine ⟨127730651843411599373687729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85153767895607732915791819 127730651843411599373687729)
                ·
                  refine ⟨95797988882558699530265797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127730651843411599373687729 95797988882558699530265797)
                  ·
                    refine ⟨17962122915479756161924837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95797988882558699530265797 17962122915479756161924837)
                    ·
                      refine ⟨3367898046652454280360907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17962122915479756161924837 3367898046652454280360907)
                      ·
                        rfl

theorem cell23_6558958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6558958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558958 prefixEnd_6558958 := by exact prefixLift 6558958
  have htrace : WordTrace (prefixWord ++ tailWord_6558958) baseStart_6558958 baseEnd_6558958 := by
    simpa [prefixWord, tailWord_6558958, baseEnd_6558958] using wordTrace_append hprefix tailTrace_6558958
  have hstable : (prefixWord ++ tailWord_6558958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558958).length < 2 ^ (prefixWord ++ tailWord_6558958).sum := by decide
  have hdescent : baseEnd_6558958 < baseStart_6558958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6558962 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_6558962 : Nat := 118140960795 + 6558962 * 2 ^ 59
def prefixEnd_6558962 : Nat := 4983230072969 + 3 ^ 40 * 6558962 * 2
def baseEnd_6558962 : Nat := 3367900100575072264710889

theorem tailTrace_6558962 : CollatzResearch.WordTrace tailWord_6558962 prefixEnd_6558962 3367900100575072264710889 := by
  unfold tailWord_6558962
  simp only [CollatzResearch.WordTrace]
  refine ⟨59806249316002082593125785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159483331509338886915002093 59806249316002082593125785)
  ·
    refine ⟨44854686987001561944844339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59806249316002082593125785 44854686987001561944844339)
    ·
      refine ⟨67282030480502342917266509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44854686987001561944844339 67282030480502342917266509)
      ·
        refine ⟨25230761430188378593974941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67282030480502342917266509 25230761430188378593974941)
        ·
          refine ⟨9461535536320641972740603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25230761430188378593974941 9461535536320641972740603)
          ·
            refine ⟨14192303304480962959110905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461535536320641972740603 14192303304480962959110905)
            ·
              refine ⟨10644227478360722219333179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14192303304480962959110905 10644227478360722219333179)
              ·
                refine ⟨15966341217541083328999769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10644227478360722219333179 15966341217541083328999769)
                ·
                  refine ⟨11974755913155812496749827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15966341217541083328999769 11974755913155812496749827)
                  ·
                    refine ⟨17962133869733718745124741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11974755913155812496749827 17962133869733718745124741)
                    ·
                      refine ⟨3367900100575072264710889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17962133869733718745124741 3367900100575072264710889)
                      ·
                        rfl

theorem cell23_6558962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_6558962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6558962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6558962 prefixEnd_6558962 := by exact prefixLift 6558962
  have htrace : WordTrace (prefixWord ++ tailWord_6558962) baseStart_6558962 baseEnd_6558962 := by
    simpa [prefixWord, tailWord_6558962, baseEnd_6558962] using wordTrace_append hprefix tailTrace_6558962
  have hstable : (prefixWord ++ tailWord_6558962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6558962).length < 2 ^ (prefixWord ++ tailWord_6558962).sum := by decide
  have hdescent : baseEnd_6558962 < baseStart_6558962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6558962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559012 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_6559012 : Nat := 118140960795 + 6559012 * 2 ^ 59
def prefixEnd_6559012 : Nat := 4983230072969 + 3 ^ 40 * 6559012 * 2
def baseEnd_6559012 : Nat := 3367925774607797069085659

theorem tailTrace_6559012 : CollatzResearch.WordTrace tailWord_6559012 prefixEnd_6559012 3367925774607797069085659 := by
  unfold tailWord_6559012
  simp only [CollatzResearch.WordTrace]
  refine ⟨119613410456913594455911645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159484547275884792607882193 119613410456913594455911645)
  ·
    refine ⟨44855028921342597920966867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119613410456913594455911645 44855028921342597920966867)
    ·
      refine ⟨67282543382013896881450301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44855028921342597920966867 67282543382013896881450301)
      ·
        refine ⟨25230953768255211330543863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67282543382013896881450301 25230953768255211330543863)
        ·
          refine ⟨37846430652382816995815795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25230953768255211330543863 37846430652382816995815795)
          ·
            refine ⟨56769645978574225493723693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37846430652382816995815795 56769645978574225493723693)
            ·
              refine ⟨21288617241965334560146385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56769645978574225493723693 21288617241965334560146385)
              ·
                refine ⟨15966462931474000920109789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21288617241965334560146385 15966462931474000920109789)
                ·
                  refine ⟨5987423599302750345041171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15966462931474000920109789 5987423599302750345041171)
                  ·
                    refine ⟨8981135398954125517561757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987423599302750345041171 8981135398954125517561757)
                    ·
                      refine ⟨3367925774607797069085659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981135398954125517561757 3367925774607797069085659)
                      ·
                        rfl

theorem cell23_6559012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_6559012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559012 prefixEnd_6559012 := by exact prefixLift 6559012
  have htrace : WordTrace (prefixWord ++ tailWord_6559012) baseStart_6559012 baseEnd_6559012 := by
    simpa [prefixWord, tailWord_6559012, baseEnd_6559012] using wordTrace_append hprefix tailTrace_6559012
  have hstable : (prefixWord ++ tailWord_6559012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559012).length < 2 ^ (prefixWord ++ tailWord_6559012).sum := by decide
  have hdescent : baseEnd_6559012 < baseStart_6559012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559029 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_6559029 : Nat := 118140960795 + 6559029 * 2 ^ 59
def prefixEnd_6559029 : Nat := 4983230072969 + 3 ^ 40 * 6559029 * 2
def baseEnd_6559029 : Nat := 3367934503778923502573081

theorem tailTrace_6559029 : CollatzResearch.WordTrace tailWord_6559029 prefixEnd_6559029 3367934503778923502573081 := by
  unfold tailWord_6559029
  simp only [CollatzResearch.WordTrace]
  refine ⟨239227440954765600815192141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159484960636510400543461427 239227440954765600815192141)
  ·
    refine ⟨89710290358037100305697053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239227440954765600815192141 89710290358037100305697053)
    ·
      refine ⟨33641358884263912614636395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89710290358037100305697053 33641358884263912614636395)
      ·
        refine ⟨50462038326395868921954593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33641358884263912614636395 50462038326395868921954593)
        ·
          refine ⟨37846528744796901691465945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50462038326395868921954593 37846528744796901691465945)
          ·
            refine ⟨28384896558597676268599459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37846528744796901691465945 28384896558597676268599459)
            ·
              refine ⟨42577344837896514402899189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28384896558597676268599459 42577344837896514402899189)
              ·
                refine ⟨3991626078552798225271799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42577344837896514402899189 3991626078552798225271799)
                ·
                  refine ⟨5987439117829197337907699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991626078552798225271799 5987439117829197337907699)
                  ·
                    refine ⟨8981158676743796006861549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987439117829197337907699 8981158676743796006861549)
                    ·
                      refine ⟨3367934503778923502573081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981158676743796006861549 3367934503778923502573081)
                      ·
                        rfl

theorem cell23_6559029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_6559029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559029 prefixEnd_6559029 := by exact prefixLift 6559029
  have htrace : WordTrace (prefixWord ++ tailWord_6559029) baseStart_6559029 baseEnd_6559029 := by
    simpa [prefixWord, tailWord_6559029, baseEnd_6559029] using wordTrace_append hprefix tailTrace_6559029
  have hstable : (prefixWord ++ tailWord_6559029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559029).length < 2 ^ (prefixWord ++ tailWord_6559029).sum := by decide
  have hdescent : baseEnd_6559029 < baseStart_6559029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559048 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_6559048 : Nat := 118140960795 + 6559048 * 2 ^ 59
def prefixEnd_6559048 : Nat := 4983230072969 + 3 ^ 40 * 6559048 * 2
def baseEnd_6559048 : Nat := 3367944259911358928235493

theorem tailTrace_6559048 : CollatzResearch.WordTrace tailWord_6559048 prefixEnd_6559048 3367944259911358928235493 := by
  unfold tailWord_6559048
  simp only [CollatzResearch.WordTrace]
  refine ⟨119614066970848383530066899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159485422627797844706755865 119614066970848383530066899)
  ·
    refine ⟨179421100456272575295100349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119614066970848383530066899 179421100456272575295100349)
    ·
      refine ⟨67282912671102215735662631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179421100456272575295100349 67282912671102215735662631)
      ·
        refine ⟨100924369006653323603493947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67282912671102215735662631 100924369006653323603493947)
        ·
          refine ⟨151386553509979985405240921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100924369006653323603493947 151386553509979985405240921)
          ·
            refine ⟨113539915132484989053930691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151386553509979985405240921 113539915132484989053930691)
            ·
              refine ⟨170309872698727483580896037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113539915132484989053930691 170309872698727483580896037)
              ·
                refine ⟨31933101131011403171418007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170309872698727483580896037 31933101131011403171418007)
                ·
                  refine ⟨47899651696517104757127011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31933101131011403171418007 47899651696517104757127011)
                  ·
                    refine ⟨71849477544775657135690517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47899651696517104757127011 71849477544775657135690517)
                    ·
                      refine ⟨3367944259911358928235493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71849477544775657135690517 3367944259911358928235493)
                      ·
                        rfl

theorem cell23_6559048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_6559048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559048 prefixEnd_6559048 := by exact prefixLift 6559048
  have htrace : WordTrace (prefixWord ++ tailWord_6559048) baseStart_6559048 baseEnd_6559048 := by
    simpa [prefixWord, tailWord_6559048, baseEnd_6559048] using wordTrace_append hprefix tailTrace_6559048
  have hstable : (prefixWord ++ tailWord_6559048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559048).length < 2 ^ (prefixWord ++ tailWord_6559048).sum := by decide
  have hdescent : baseEnd_6559048 < baseStart_6559048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559058 : List Nat := [3, 2, 2, 1, 1, 1, 1, 12]
def baseStart_6559058 : Nat := 118140960795 + 6559058 * 2 ^ 59
def prefixEnd_6559058 : Nat := 4983230072969 + 3 ^ 40 * 6559058 * 2
def baseEnd_6559058 : Nat := 124738866471033477374461

theorem tailTrace_6559058 : CollatzResearch.WordTrace tailWord_6559058 prefixEnd_6559058 124738866471033477374461 := by
  unfold tailWord_6559058
  simp only [CollatzResearch.WordTrace]
  refine ⟨59807124667915134691999457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159485665781107025845331885 59807124667915134691999457)
  ·
    refine ⟨44855343500936351018999593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59807124667915134691999457 44855343500936351018999593)
    ·
      refine ⟨33641507625702263264249695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44855343500936351018999593 33641507625702263264249695)
      ·
        refine ⟨50462261438553394896374543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33641507625702263264249695 50462261438553394896374543)
        ·
          refine ⟨75693392157830092344561815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50462261438553394896374543 75693392157830092344561815)
          ·
            refine ⟨113540088236745138516842723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75693392157830092344561815 113540088236745138516842723)
            ·
              refine ⟨170310132355117707775264085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113540088236745138516842723 170310132355117707775264085)
              ·
                refine ⟨124738866471033477374461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 170310132355117707775264085 124738866471033477374461)
                ·
                  rfl

theorem cell23_6559058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_6559058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559058 prefixEnd_6559058 := by exact prefixLift 6559058
  have htrace : WordTrace (prefixWord ++ tailWord_6559058) baseStart_6559058 baseEnd_6559058 := by
    simpa [prefixWord, tailWord_6559058, baseEnd_6559058] using wordTrace_append hprefix tailTrace_6559058
  have hstable : (prefixWord ++ tailWord_6559058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559058).length < 2 ^ (prefixWord ++ tailWord_6559058).sum := by decide
  have hdescent : baseEnd_6559058 < baseStart_6559058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559065 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_6559065 : Nat := 118140960795 + 6559065 * 2 ^ 59
def prefixEnd_6559065 : Nat := 4983230072969 + 3 ^ 40 * 6559065 * 2
def baseEnd_6559065 : Nat := 3367952989082485361722915

theorem tailTrace_6559065 : CollatzResearch.WordTrace tailWord_6559065 prefixEnd_6559065 3367952989082485361722915 := by
  unfold tailWord_6559065
  simp only [CollatzResearch.WordTrace]
  refine ⟨239228753982635178963502649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159485835988423452642335099 239228753982635178963502649)
  ·
    refine ⟨179421565486976384222626987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239228753982635178963502649 179421565486976384222626987)
    ·
      refine ⟨269132348230464576333940481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179421565486976384222626987 269132348230464576333940481)
      ·
        refine ⟨201849261172848432250455361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269132348230464576333940481 201849261172848432250455361)
        ·
          refine ⟨151386945879636324187841521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201849261172848432250455361 151386945879636324187841521)
          ·
            refine ⟨113540209409727243140881141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151386945879636324187841521 113540209409727243140881141)
            ·
              refine ⟨10644394632161929044457607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113540209409727243140881141 10644394632161929044457607)
              ·
                refine ⟨15966591948242893566686411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10644394632161929044457607 15966591948242893566686411)
                ·
                  refine ⟨23949887922364340350029617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15966591948242893566686411 23949887922364340350029617)
                  ·
                    refine ⟨17962415941773255262522213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23949887922364340350029617 17962415941773255262522213)
                    ·
                      refine ⟨3367952989082485361722915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17962415941773255262522213 3367952989082485361722915)
                      ·
                        rfl

theorem cell23_6559065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_6559065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559065 prefixEnd_6559065 := by exact prefixLift 6559065
  have htrace : WordTrace (prefixWord ++ tailWord_6559065) baseStart_6559065 baseEnd_6559065 := by
    simpa [prefixWord, tailWord_6559065, baseEnd_6559065] using wordTrace_append hprefix tailTrace_6559065
  have hstable : (prefixWord ++ tailWord_6559065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559065).length < 2 ^ (prefixWord ++ tailWord_6559065).sum := by decide
  have hdescent : baseEnd_6559065 < baseStart_6559065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559072 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_6559072 : Nat := 118140960795 + 6559072 * 2 ^ 59
def prefixEnd_6559072 : Nat := 4983230072969 + 3 ^ 40 * 6559072 * 2
def baseEnd_6559072 : Nat := 3367956583447066834335383

theorem tailTrace_6559072 : CollatzResearch.WordTrace tailWord_6559072 prefixEnd_6559072 3367956583447066834335383 := by
  unfold tailWord_6559072
  simp only [CollatzResearch.WordTrace]
  refine ⟨119614504646804909579503735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159486006195739879439338313 119614504646804909579503735)
  ·
    refine ⟨179421756970207364369255603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119614504646804909579503735 179421756970207364369255603)
    ·
      refine ⟨269132635455311046553883405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179421756970207364369255603 269132635455311046553883405)
      ·
        refine ⟨100924738295741642457706277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269132635455311046553883405 100924738295741642457706277)
        ·
          refine ⟨18923388430451557960819927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100924738295741642457706277 18923388430451557960819927)
          ·
            refine ⟨28385082645677336941229891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18923388430451557960819927 28385082645677336941229891)
            ·
              refine ⟨42577623968516005411844837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28385082645677336941229891 42577623968516005411844837)
              ·
                refine ⟨7983304494096751014720907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42577623968516005411844837 7983304494096751014720907)
                ·
                  refine ⟨11974956741145126522081361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983304494096751014720907 11974956741145126522081361)
                  ·
                    refine ⟨8981217555858844891561021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11974956741145126522081361 8981217555858844891561021)
                    ·
                      refine ⟨3367956583447066834335383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981217555858844891561021 3367956583447066834335383)
                      ·
                        rfl

theorem cell23_6559072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_6559072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559072 prefixEnd_6559072 := by exact prefixLift 6559072
  have htrace : WordTrace (prefixWord ++ tailWord_6559072) baseStart_6559072 baseEnd_6559072 := by
    simpa [prefixWord, tailWord_6559072, baseEnd_6559072] using wordTrace_append hprefix tailTrace_6559072
  have hstable : (prefixWord ++ tailWord_6559072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559072).length < 2 ^ (prefixWord ++ tailWord_6559072).sum := by decide
  have hdescent : baseEnd_6559072 < baseStart_6559072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559075 : List Nat := [1, 1, 1, 5, 2, 2, 4, 7]
def baseStart_6559075 : Nat := 118140960795 + 6559075 * 2 ^ 59
def prefixEnd_6559075 : Nat := 4983230072969 + 3 ^ 40 * 6559075 * 2
def baseEnd_6559075 : Nat := 124739189773667789725847

theorem tailTrace_6559075 : CollatzResearch.WordTrace tailWord_6559075 prefixEnd_6559075 124739189773667789725847 := by
  unfold tailWord_6559075
  simp only [CollatzResearch.WordTrace]
  refine ⟨239229118712598950671366679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159486079141732633780911119 239229118712598950671366679)
  ·
    refine ⟨358843678068898426007050019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239229118712598950671366679 358843678068898426007050019)
    ·
      refine ⟨538265517103347639010575029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358843678068898426007050019 538265517103347639010575029)
      ·
        refine ⟨50462392228438841157241409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 538265517103347639010575029 50462392228438841157241409)
        ·
          refine ⟨37846794171329130867931057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50462392228438841157241409 37846794171329130867931057)
          ·
            refine ⟨28385095628496848150948293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37846794171329130867931057 28385095628496848150948293)
            ·
              refine ⟨5322205430343159028302805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28385095628496848150948293 5322205430343159028302805)
              ·
                refine ⟨124739189773667789725847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5322205430343159028302805 124739189773667789725847)
                ·
                  rfl

theorem cell23_6559075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 7].length) (baseStart_6559075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559075 prefixEnd_6559075 := by exact prefixLift 6559075
  have htrace : WordTrace (prefixWord ++ tailWord_6559075) baseStart_6559075 baseEnd_6559075 := by
    simpa [prefixWord, tailWord_6559075, baseEnd_6559075] using wordTrace_append hprefix tailTrace_6559075
  have hstable : (prefixWord ++ tailWord_6559075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559075).length < 2 ^ (prefixWord ++ tailWord_6559075).sum := by decide
  have hdescent : baseEnd_6559075 < baseStart_6559075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559129 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 1, 3, 2]
def baseStart_6559129 : Nat := 118140960795 + 6559129 * 2 ^ 59
def prefixEnd_6559129 : Nat := 4983230072969 + 3 ^ 40 * 6559129 * 2
def baseEnd_6559129 : Nat := 3367985851844373111322621

theorem tailTrace_6559129 : CollatzResearch.WordTrace tailWord_6559129 prefixEnd_6559129 3367985851844373111322621 := by
  unfold tailWord_6559129
  simp only [CollatzResearch.WordTrace]
  refine ⟨239231088254403317893832441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159487392169602211929221627 239231088254403317893832441)
  ·
    refine ⟨179423316190802488420374331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239231088254403317893832441 179423316190802488420374331)
    ·
      refine ⟨269134974286203732630561497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179423316190802488420374331 269134974286203732630561497)
      ·
        refine ⟨201851230714652799472921123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269134974286203732630561497 201851230714652799472921123)
        ·
          refine ⟨302776846071979199209381685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201851230714652799472921123 302776846071979199209381685)
          ·
            refine ⟨28385329319248049925879533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302776846071979199209381685 28385329319248049925879533)
            ·
              refine ⟨10644498494718018722204825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28385329319248049925879533 10644498494718018722204825)
              ·
                refine ⟨7983373871038514041653619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10644498494718018722204825 7983373871038514041653619)
                ·
                  refine ⟨11975060806557771062480429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983373871038514041653619 11975060806557771062480429)
                  ·
                    refine ⟨4490647802459164148430161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11975060806557771062480429 4490647802459164148430161)
                    ·
                      refine ⟨3367985851844373111322621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490647802459164148430161 3367985851844373111322621)
                      ·
                        rfl

theorem cell23_6559129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_6559129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559129 prefixEnd_6559129 := by exact prefixLift 6559129
  have htrace : WordTrace (prefixWord ++ tailWord_6559129) baseStart_6559129 baseEnd_6559129 := by
    simpa [prefixWord, tailWord_6559129, baseEnd_6559129] using wordTrace_append hprefix tailTrace_6559129
  have hstable : (prefixWord ++ tailWord_6559129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559129).length < 2 ^ (prefixWord ++ tailWord_6559129).sum := by decide
  have hdescent : baseEnd_6559129 < baseStart_6559129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559165 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 7]
def baseStart_6559165 : Nat := 118140960795 + 6559165 * 2 ^ 59
def prefixEnd_6559165 : Nat := 4983230072969 + 3 ^ 40 * 6559165 * 2
def baseEnd_6559165 : Nat := 374222704127548330052495

theorem tailTrace_6559165 : CollatzResearch.WordTrace tailWord_6559165 prefixEnd_6559165 374222704127548330052495 := by
  unfold tailWord_6559165
  simp only [CollatzResearch.WordTrace]
  refine ⟨239232401282272896042142949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159488267521515264028095299 239232401282272896042142949)
  ·
    refine ⟨44856075240426168007901803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239232401282272896042142949 44856075240426168007901803)
    ·
      refine ⟨67284112860639252011852705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44856075240426168007901803 67284112860639252011852705)
      ·
        refine ⟨50463084645479439008889529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67284112860639252011852705 50463084645479439008889529)
        ·
          refine ⟨37847313484109579256667147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50463084645479439008889529 37847313484109579256667147)
          ·
            refine ⟨56770970226164368885000721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37847313484109579256667147 56770970226164368885000721)
            ·
              refine ⟨42578227669623276663750541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56770970226164368885000721 42578227669623276663750541)
              ·
                refine ⟨15966835376108728748906453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42578227669623276663750541 15966835376108728748906453)
                ·
                  refine ⟨374222704127548330052495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15966835376108728748906453 374222704127548330052495)
                  ·
                    rfl

theorem cell23_6559165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_6559165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559165 prefixEnd_6559165 := by exact prefixLift 6559165
  have htrace : WordTrace (prefixWord ++ tailWord_6559165) baseStart_6559165 baseEnd_6559165 := by
    simpa [prefixWord, tailWord_6559165, baseEnd_6559165] using wordTrace_append hprefix tailTrace_6559165
  have hstable : (prefixWord ++ tailWord_6559165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559165).length < 2 ^ (prefixWord ++ tailWord_6559165).sum := by decide
  have hdescent : baseEnd_6559165 < baseStart_6559165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559170 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6559170 : Nat := 118140960795 + 6559170 * 2 ^ 59
def prefixEnd_6559170 : Nat := 4983230072969 + 3 ^ 40 * 6559170 * 2
def baseEnd_6559170 : Nat := 3368006904551207450909933

theorem tailTrace_6559170 : CollatzResearch.WordTrace tailWord_6559170 prefixEnd_6559170 3368006904551207450909933 := by
  unfold tailWord_6559170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59808145911813695474018741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159488389098169854597383309 59808145911813695474018741)
  ·
    refine ⟨5607013679232533950689257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59808145911813695474018741 5607013679232533950689257)
    ·
      refine ⟨4205260259424400463016943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5607013679232533950689257 4205260259424400463016943)
      ·
        refine ⟨6307890389136600694525415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205260259424400463016943 6307890389136600694525415)
        ·
          refine ⟨9461835583704901041788123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6307890389136600694525415 9461835583704901041788123)
          ·
            refine ⟨14192753375557351562682185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461835583704901041788123 14192753375557351562682185)
            ·
              refine ⟨10644565031668013672011639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14192753375557351562682185 10644565031668013672011639)
              ·
                refine ⟨15966847547502020508017459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10644565031668013672011639 15966847547502020508017459)
                ·
                  refine ⟨23950271321253030762026189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15966847547502020508017459 23950271321253030762026189)
                  ·
                    refine ⟨8981351745469886535759821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23950271321253030762026189 8981351745469886535759821)
                    ·
                      refine ⟨3368006904551207450909933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981351745469886535759821 3368006904551207450909933)
                      ·
                        rfl

theorem cell23_6559170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6559170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559170 prefixEnd_6559170 := by exact prefixLift 6559170
  have htrace : WordTrace (prefixWord ++ tailWord_6559170) baseStart_6559170 baseEnd_6559170 := by
    simpa [prefixWord, tailWord_6559170, baseEnd_6559170] using wordTrace_append hprefix tailTrace_6559170
  have hstable : (prefixWord ++ tailWord_6559170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559170).length < 2 ^ (prefixWord ++ tailWord_6559170).sum := by decide
  have hdescent : baseEnd_6559170 < baseStart_6559170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559172 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6559172 : Nat := 118140960795 + 6559172 * 2 ^ 59
def prefixEnd_6559172 : Nat := 4983230072969 + 3 ^ 40 * 6559172 * 2
def baseEnd_6559172 : Nat := 3368007931512516443084923

theorem tailTrace_6559172 : CollatzResearch.WordTrace tailWord_6559172 prefixEnd_6559172 3368007931512516443084923 := by
  unfold tailWord_6559172
  simp only [CollatzResearch.WordTrace]
  refine ⟨119616328296623768118823885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159488437728831690825098513 119616328296623768118823885)
  ·
    refine ⟨44856123111233913044558957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119616328296623768118823885 44856123111233913044558957)
    ·
      refine ⟨16821046166712717391709609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44856123111233913044558957 16821046166712717391709609)
      ·
        refine ⟨12615784625034538043782207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16821046166712717391709609 12615784625034538043782207)
        ·
          refine ⟨18923676937551807065673311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12615784625034538043782207 18923676937551807065673311)
          ·
            refine ⟨28385515406327710598509967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18923676937551807065673311 28385515406327710598509967)
            ·
              refine ⟨42578273109491565897764951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28385515406327710598509967 42578273109491565897764951)
              ·
                refine ⟨63867409664237348846647427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42578273109491565897764951 63867409664237348846647427)
                ·
                  refine ⟨95801114496356023269971141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63867409664237348846647427 95801114496356023269971141)
                  ·
                    refine ⟨17962708968066754363119589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95801114496356023269971141 17962708968066754363119589)
                    ·
                      refine ⟨3368007931512516443084923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17962708968066754363119589 3368007931512516443084923)
                      ·
                        rfl

theorem cell23_6559172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6559172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559172 prefixEnd_6559172 := by exact prefixLift 6559172
  have htrace : WordTrace (prefixWord ++ tailWord_6559172) baseStart_6559172 baseEnd_6559172 := by
    simpa [prefixWord, tailWord_6559172, baseEnd_6559172] using wordTrace_append hprefix tailTrace_6559172
  have hstable : (prefixWord ++ tailWord_6559172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559172).length < 2 ^ (prefixWord ++ tailWord_6559172).sum := by decide
  have hdescent : baseEnd_6559172 < baseStart_6559172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559210 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_6559210 : Nat := 118140960795 + 6559210 * 2 ^ 59
def prefixEnd_6559210 : Nat := 4983230072969 + 3 ^ 40 * 6559210 * 2
def baseEnd_6559210 : Nat := 3368027443777387294409749

theorem tailTrace_6559210 : CollatzResearch.WordTrace tailWord_6559210 prefixEnd_6559210 3368027443777387294409749 := by
  unfold tailWord_6559210
  simp only [CollatzResearch.WordTrace]
  refine ⟨59808510641777467181882771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159489361711406579151687389 59808510641777467181882771)
  ·
    refine ⟨89712765962666200772824157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59808510641777467181882771 89712765962666200772824157)
    ·
      refine ⟨33642287235999825289809059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89712765962666200772824157 33642287235999825289809059)
      ·
        refine ⟨50463430853999737934713589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33642287235999825289809059 50463430853999737934713589)
        ·
          refine ⟨4730946642562475431379399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50463430853999737934713589 4730946642562475431379399)
          ·
            refine ⟨7096419963843713147069099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730946642562475431379399 7096419963843713147069099)
            ·
              refine ⟨10644629945765569720603649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096419963843713147069099 10644629945765569720603649)
              ·
                refine ⟨7983472459324177290452737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10644629945765569720603649 7983472459324177290452737)
                ·
                  refine ⟨5987604344493132967839553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7983472459324177290452737 5987604344493132967839553)
                  ·
                    refine ⟨4490703258369849725879665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987604344493132967839553 4490703258369849725879665)
                    ·
                      refine ⟨3368027443777387294409749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490703258369849725879665 3368027443777387294409749)
                      ·
                        rfl

theorem cell23_6559210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_6559210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559210 prefixEnd_6559210 := by exact prefixLift 6559210
  have htrace : WordTrace (prefixWord ++ tailWord_6559210) baseStart_6559210 baseEnd_6559210 := by
    simpa [prefixWord, tailWord_6559210, baseEnd_6559210] using wordTrace_append hprefix tailTrace_6559210
  have hstable : (prefixWord ++ tailWord_6559210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559210).length < 2 ^ (prefixWord ++ tailWord_6559210).sum := by decide
  have hdescent : baseEnd_6559210 < baseStart_6559210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559289 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 6]
def baseStart_6559289 : Nat := 118140960795 + 6559289 * 2 ^ 59
def prefixEnd_6559289 : Nat := 4983230072969 + 3 ^ 40 * 6559289 * 2
def baseEnd_6559289 : Nat := 374229778749899165035765

theorem tailTrace_6559289 : CollatzResearch.WordTrace tailWord_6559289 prefixEnd_6559289 374229778749899165035765 := by
  unfold tailWord_6559289
  simp only [CollatzResearch.WordTrace]
  refine ⟨239236923933823665219656921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159491282622549110146437947 239236923933823665219656921)
  ·
    refine ⟨179427692950367748914742691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239236923933823665219656921 179427692950367748914742691)
    ·
      refine ⟨269141539425551623372114037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179427692950367748914742691 269141539425551623372114037)
      ·
        refine ⟨25232019321145464691135691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269141539425551623372114037 25232019321145464691135691)
        ·
          refine ⟨37848028981718197036703537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25232019321145464691135691 37848028981718197036703537)
          ·
            refine ⟨28386021736288647777527653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37848028981718197036703537 28386021736288647777527653)
            ·
              refine ⟨5322379075554121458286435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28386021736288647777527653 5322379075554121458286435)
              ·
                refine ⟨7983568613331182187429653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322379075554121458286435 7983568613331182187429653)
                ·
                  refine ⟨374229778749899165035765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7983568613331182187429653 374229778749899165035765)
                  ·
                    rfl

theorem cell23_6559289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 6].length) (baseStart_6559289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559289 prefixEnd_6559289 := by exact prefixLift 6559289
  have htrace : WordTrace (prefixWord ++ tailWord_6559289) baseStart_6559289 baseEnd_6559289 := by
    simpa [prefixWord, tailWord_6559289, baseEnd_6559289] using wordTrace_append hprefix tailTrace_6559289
  have hstable : (prefixWord ++ tailWord_6559289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559289).length < 2 ^ (prefixWord ++ tailWord_6559289).sum := by decide
  have hdescent : baseEnd_6559289 < baseStart_6559289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559333 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 1, 1, 3]
def baseStart_6559333 : Nat := 118140960795 + 6559333 * 2 ^ 59
def prefixEnd_6559333 : Nat := 4983230072969 + 3 ^ 40 * 6559333 * 2
def baseEnd_6559333 : Nat := 3368090601897890313171683

theorem tailTrace_6559333 : CollatzResearch.WordTrace tailWord_6559333 prefixEnd_6559333 3368090601897890313171683 := by
  unfold tailWord_6559333
  simp only [CollatzResearch.WordTrace]
  refine ⟨239238528745664260734258653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159492352497109507156172435 239238528745664260734258653)
  ·
    refine ⟨89714448279624097775346995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239238528745664260734258653 89714448279624097775346995)
    ·
      refine ⟨134571672419436146663020493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89714448279624097775346995 134571672419436146663020493)
      ·
        refine ⟨50464377157288554998632685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134571672419436146663020493 50464377157288554998632685)
        ·
          refine ⟨18924141433983208124487257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50464377157288554998632685 18924141433983208124487257)
          ·
            refine ⟨14193106075487406093365443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18924141433983208124487257 14193106075487406093365443)
            ·
              refine ⟨21289659113231109140048165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14193106075487406093365443 21289659113231109140048165)
              ·
                refine ⟨3991811083730832963759031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21289659113231109140048165 3991811083730832963759031)
                ·
                  refine ⟨5987716625596249445638547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991811083730832963759031 5987716625596249445638547)
                  ·
                    refine ⟨8981574938394374168457821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987716625596249445638547 8981574938394374168457821)
                    ·
                      refine ⟨3368090601897890313171683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981574938394374168457821 3368090601897890313171683)
                      ·
                        rfl

theorem cell23_6559333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_6559333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559333 prefixEnd_6559333 := by exact prefixLift 6559333
  have htrace : WordTrace (prefixWord ++ tailWord_6559333) baseStart_6559333 baseEnd_6559333 := by
    simpa [prefixWord, tailWord_6559333, baseEnd_6559333] using wordTrace_append hprefix tailTrace_6559333
  have hstable : (prefixWord ++ tailWord_6559333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559333).length < 2 ^ (prefixWord ++ tailWord_6559333).sum := by decide
  have hdescent : baseEnd_6559333 < baseStart_6559333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559349 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6559349 : Nat := 118140960795 + 6559349 * 2 ^ 59
def prefixEnd_6559349 : Nat := 4983230072969 + 3 ^ 40 * 6559349 * 2
def baseEnd_6559349 : Nat := 1122699605862787416857203

theorem tailTrace_6559349 : CollatzResearch.WordTrace tailWord_6559349 prefixEnd_6559349 1122699605862787416857203 := by
  unfold tailWord_6559349
  simp only [CollatzResearch.WordTrace]
  refine ⟨239239112313606295466841101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159492741542404196977894067 239239112313606295466841101)
  ·
    refine ⟨89714667117602360800065413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239239112313606295466841101 89714667117602360800065413)
    ·
      refine ⟨16821500084550442650012265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89714667117602360800065413 16821500084550442650012265)
      ·
        refine ⟨12616125063412831987509199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16821500084550442650012265 12616125063412831987509199)
        ·
          refine ⟨18924187595119247981263799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616125063412831987509199 18924187595119247981263799)
          ·
            refine ⟨28386281392678871971895699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18924187595119247981263799 28386281392678871971895699)
            ·
              refine ⟨42579422089018307957843549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28386281392678871971895699 42579422089018307957843549)
              ·
                refine ⟨15967283283381865484191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42579422089018307957843549 15967283283381865484191331)
                ·
                  refine ⟨23950924925072798226286997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15967283283381865484191331 23950924925072798226286997)
                  ·
                    refine ⟨1122699605862787416857203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23950924925072798226286997 1122699605862787416857203)
                    ·
                      rfl

theorem cell23_6559349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6559349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559349 prefixEnd_6559349 := by exact prefixLift 6559349
  have htrace : WordTrace (prefixWord ++ tailWord_6559349) baseStart_6559349 baseEnd_6559349 := by
    simpa [prefixWord, tailWord_6559349, baseEnd_6559349] using wordTrace_append hprefix tailTrace_6559349
  have hstable : (prefixWord ++ tailWord_6559349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559349).length < 2 ^ (prefixWord ++ tailWord_6559349).sum := by decide
  have hdescent : baseEnd_6559349 < baseStart_6559349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559390 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6559390 : Nat := 118140960795 + 6559390 * 2 ^ 59
def prefixEnd_6559390 : Nat := 4983230072969 + 3 ^ 40 * 6559390 * 2
def baseEnd_6559390 : Nat := 3368119870295196590158921

theorem tailTrace_6559390 : CollatzResearch.WordTrace tailWord_6559390 prefixEnd_6559390 3368119870295196590158921 := by
  unfold tailWord_6559390
  simp only [CollatzResearch.WordTrace]
  refine ⟨29905075963307219933635453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159493738470971839646055749 29905075963307219933635453)
  ·
    refine ⟨11214403486240207475113295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29905075963307219933635453 11214403486240207475113295)
    ·
      refine ⟨16821605229360311212669943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11214403486240207475113295 16821605229360311212669943)
      ·
        refine ⟨25232407844040466819004915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16821605229360311212669943 25232407844040466819004915)
        ·
          refine ⟨37848611766060700228507373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25232407844040466819004915 37848611766060700228507373)
          ·
            refine ⟨14193229412272762585690265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37848611766060700228507373 14193229412272762585690265)
            ·
              refine ⟨10644922059204571939267699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14193229412272762585690265 10644922059204571939267699)
              ·
                refine ⟨15967383088806857908901549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10644922059204571939267699 15967383088806857908901549)
                ·
                  refine ⟨5987768658302571715838081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15967383088806857908901549 5987768658302571715838081)
                  ·
                    refine ⟨4490826493726928786878561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987768658302571715838081 4490826493726928786878561)
                    ·
                      refine ⟨3368119870295196590158921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4490826493726928786878561 3368119870295196590158921)
                      ·
                        rfl

theorem cell23_6559390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6559390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559390 prefixEnd_6559390 := by exact prefixLift 6559390
  have htrace : WordTrace (prefixWord ++ tailWord_6559390) baseStart_6559390 baseEnd_6559390 := by
    simpa [prefixWord, tailWord_6559390, baseEnd_6559390] using wordTrace_append hprefix tailTrace_6559390
  have hstable : (prefixWord ++ tailWord_6559390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559390).length < 2 ^ (prefixWord ++ tailWord_6559390).sum := by decide
  have hdescent : baseEnd_6559390 < baseStart_6559390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559400 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6559400 : Nat := 118140960795 + 6559400 * 2 ^ 59
def prefixEnd_6559400 : Nat := 4983230072969 + 3 ^ 40 * 6559400 * 2
def baseEnd_6559400 : Nat := 1122708335033913850344625

theorem tailTrace_6559400 : CollatzResearch.WordTrace tailWord_6559400 prefixEnd_6559400 1122708335033913850344625 := by
  unfold tailWord_6559400
  simp only [CollatzResearch.WordTrace]
  refine ⟨119620486218210765588473827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159493981624281020784631769 119620486218210765588473827)
  ·
    refine ⟨179430729327316148382710741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119620486218210765588473827 179430729327316148382710741)
    ·
      refine ⟨4205407718608972227719783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 179430729327316148382710741 4205407718608972227719783)
      ·
        refine ⟨6308111577913458341579675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205407718608972227719783 6308111577913458341579675)
        ·
          refine ⟨9462167366870187512369513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308111577913458341579675 9462167366870187512369513)
          ·
            refine ⟨7096625525152640634277135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462167366870187512369513 7096625525152640634277135)
            ·
              refine ⟨10644938287728960951415703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096625525152640634277135 10644938287728960951415703)
              ·
                refine ⟨15967407431593441427123555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10644938287728960951415703 15967407431593441427123555)
                ·
                  refine ⟨23951111147390162140685333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15967407431593441427123555 23951111147390162140685333)
                  ·
                    refine ⟨1122708335033913850344625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23951111147390162140685333 1122708335033913850344625)
                    ·
                      rfl

theorem cell23_6559400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6559400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559400 prefixEnd_6559400 := by exact prefixLift 6559400
  have htrace : WordTrace (prefixWord ++ tailWord_6559400) baseStart_6559400 baseEnd_6559400 := by
    simpa [prefixWord, tailWord_6559400, baseEnd_6559400] using wordTrace_append hprefix tailTrace_6559400
  have hstable : (prefixWord ++ tailWord_6559400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559400).length < 2 ^ (prefixWord ++ tailWord_6559400).sum := by decide
  have hdescent : baseEnd_6559400 < baseStart_6559400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559413 : List Nat := [1, 3, 3, 3, 3, 1, 2, 7]
def baseStart_6559413 : Nat := 118140960795 + 6559413 * 2 ^ 59
def prefixEnd_6559413 : Nat := 4983230072969 + 3 ^ 40 * 6559413 * 2
def baseEnd_6559413 : Nat := 124745617790750000006345

theorem tailTrace_6559413 : CollatzResearch.WordTrace tailWord_6559413 prefixEnd_6559413 124745617790750000006345 := by
  unfold tailWord_6559413
  simp only [CollatzResearch.WordTrace]
  refine ⟨239241446585374434397170893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159494297723582956264780595 239241446585374434397170893)
  ·
    refine ⟨89715542469515412898939085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239241446585374434397170893 89715542469515412898939085)
    ·
      refine ⟨33643328426068279837102157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89715542469515412898939085 33643328426068279837102157)
      ·
        refine ⟨12616248159775604938913309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33643328426068279837102157 12616248159775604938913309)
        ·
          refine ⟨4731093059915851852092491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12616248159775604938913309 4731093059915851852092491)
          ·
            refine ⟨7096639589873777778138737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731093059915851852092491 7096639589873777778138737)
            ·
              refine ⟨5322479692405333333604053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7096639589873777778138737 5322479692405333333604053)
              ·
                refine ⟨124745617790750000006345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5322479692405333333604053 124745617790750000006345)
                ·
                  rfl

theorem cell23_6559413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 7].length) (baseStart_6559413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559413 prefixEnd_6559413 := by exact prefixLift 6559413
  have htrace : WordTrace (prefixWord ++ tailWord_6559413) baseStart_6559413 baseEnd_6559413 := by
    simpa [prefixWord, tailWord_6559413, baseEnd_6559413] using wordTrace_append hprefix tailTrace_6559413
  have hstable : (prefixWord ++ tailWord_6559413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559413).length < 2 ^ (prefixWord ++ tailWord_6559413).sum := by decide
  have hdescent : baseEnd_6559413 < baseStart_6559413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559457 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_6559457 : Nat := 118140960795 + 6559457 * 2 ^ 59
def prefixEnd_6559457 : Nat := 4983230072969 + 3 ^ 40 * 6559457 * 2
def baseEnd_6559457 : Nat := 3368154273499047828021113

theorem tailTrace_6559457 : CollatzResearch.WordTrace tailWord_6559457 prefixEnd_6559457 3368154273499047828021113 := by
  unfold tailWord_6559457
  simp only [CollatzResearch.WordTrace]
  refine ⟨239243051397215029911772625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159495367598143353274515083 239243051397215029911772625)
  ·
    refine ⟨179432288547911272433829469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239243051397215029911772625 179432288547911272433829469)
    ·
      refine ⟨67287108205466727162686051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179432288547911272433829469 67287108205466727162686051)
      ·
        refine ⟨100930662308200090744029077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67287108205466727162686051 100930662308200090744029077)
        ·
          refine ⟨4731124795696879253626363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100930662308200090744029077 4731124795696879253626363)
          ·
            refine ⟨7096687193545318880439545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731124795696879253626363 7096687193545318880439545)
            ·
              refine ⟨5322515395158989160329659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7096687193545318880439545 5322515395158989160329659)
              ·
                refine ⟨7983773092738483740494489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322515395158989160329659 7983773092738483740494489)
                ·
                  refine ⟨5987829819553862805370867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7983773092738483740494489 5987829819553862805370867)
                  ·
                    refine ⟨8981744729330794208056301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987829819553862805370867 8981744729330794208056301)
                    ·
                      refine ⟨3368154273499047828021113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981744729330794208056301 3368154273499047828021113)
                      ·
                        rfl

theorem cell23_6559457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_6559457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559457 prefixEnd_6559457 := by exact prefixLift 6559457
  have htrace : WordTrace (prefixWord ++ tailWord_6559457) baseStart_6559457 baseEnd_6559457 := by
    simpa [prefixWord, tailWord_6559457, baseEnd_6559457] using wordTrace_append hprefix tailTrace_6559457
  have hstable : (prefixWord ++ tailWord_6559457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559457).length < 2 ^ (prefixWord ++ tailWord_6559457).sum := by decide
  have hdescent : baseEnd_6559457 < baseStart_6559457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559499 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 2, 5]
def baseStart_6559499 : Nat := 118140960795 + 6559499 * 2 ^ 59
def prefixEnd_6559499 : Nat := 4983230072969 + 3 ^ 40 * 6559499 * 2
def baseEnd_6559499 : Nat := 1122725279895512221231973

theorem tailTrace_6559499 : CollatzResearch.WordTrace tailWord_6559499 prefixEnd_6559499 1122725279895512221231973 := by
  unfold tailWord_6559499
  simp only [CollatzResearch.WordTrace]
  refine ⟨239244583263062871084801551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159496388842041914056534367 239244583263062871084801551)
  ·
    refine ⟨358866874894594306627202327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239244583263062871084801551 358866874894594306627202327)
    ·
      refine ⟨538300312341891459940803491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358866874894594306627202327 538300312341891459940803491)
      ·
        refine ⟨807450468512837189911205237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538300312341891459940803491 807450468512837189911205237)
        ·
          refine ⟨75698481423078486554175491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 807450468512837189911205237 75698481423078486554175491)
          ·
            refine ⟨113547722134617729831263237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75698481423078486554175491 113547722134617729831263237)
            ·
              refine ⟨21290197900240824343361857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113547722134617729831263237 21290197900240824343361857)
              ·
                refine ⟨15967648425180618257521393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21290197900240824343361857 15967648425180618257521393)
                ·
                  refine ⟨11975736318885463693141045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15967648425180618257521393 11975736318885463693141045)
                  ·
                    refine ⟨1122725279895512221231973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11975736318885463693141045 1122725279895512221231973)
                    ·
                      rfl

theorem cell23_6559499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 5].length) (baseStart_6559499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559499 prefixEnd_6559499 := by exact prefixLift 6559499
  have htrace : WordTrace (prefixWord ++ tailWord_6559499) baseStart_6559499 baseEnd_6559499 := by
    simpa [prefixWord, tailWord_6559499, baseEnd_6559499] using wordTrace_append hprefix tailTrace_6559499
  have hstable : (prefixWord ++ tailWord_6559499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559499).length < 2 ^ (prefixWord ++ tailWord_6559499).sum := by decide
  have hdescent : baseEnd_6559499 < baseStart_6559499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559509 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_6559509 : Nat := 118140960795 + 6559509 * 2 ^ 59
def prefixEnd_6559509 : Nat := 4983230072969 + 3 ^ 40 * 6559509 * 2
def baseEnd_6559509 : Nat := 3368180974493081624570873

theorem tailTrace_6559509 : CollatzResearch.WordTrace tailWord_6559509 prefixEnd_6559509 3368180974493081624570873 := by
  unfold tailWord_6559509
  simp only [CollatzResearch.WordTrace]
  refine ⟨239244947993026642792665581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159496631995351095195110387 239244947993026642792665581)
  ·
    refine ⟨89716855497384991047249593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239244947993026642792665581 89716855497384991047249593)
    ·
      refine ⟨67287641623038743285437195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89716855497384991047249593 67287641623038743285437195)
      ·
        refine ⟨100931462434558114928155793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67287641623038743285437195 100931462434558114928155793)
        ·
          refine ⟨75698596825918586196116845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100931462434558114928155793 75698596825918586196116845)
          ·
            refine ⟨28386973809719469823543817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75698596825918586196116845 28386973809719469823543817)
            ·
              refine ⟨21290230357289602367657863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28386973809719469823543817 21290230357289602367657863)
              ·
                refine ⟨31935345535934403551486795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21290230357289602367657863 31935345535934403551486795)
                ·
                  refine ⟨47903018303901605327230193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31935345535934403551486795 47903018303901605327230193)
                  ·
                    refine ⟨35927263727926203995422645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47903018303901605327230193 35927263727926203995422645)
                    ·
                      refine ⟨3368180974493081624570873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35927263727926203995422645 3368180974493081624570873)
                      ·
                        rfl

theorem cell23_6559509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_6559509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559509 prefixEnd_6559509 := by exact prefixLift 6559509
  have htrace : WordTrace (prefixWord ++ tailWord_6559509) baseStart_6559509 baseEnd_6559509 := by
    simpa [prefixWord, tailWord_6559509, baseEnd_6559509] using wordTrace_append hprefix tailTrace_6559509
  have hstable : (prefixWord ++ tailWord_6559509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559509).length < 2 ^ (prefixWord ++ tailWord_6559509).sum := by decide
  have hdescent : baseEnd_6559509 < baseStart_6559509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559519 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_6559519 : Nat := 118140960795 + 6559519 * 2 ^ 59
def prefixEnd_6559519 : Nat := 4983230072969 + 3 ^ 40 * 6559519 * 2
def baseEnd_6559519 : Nat := 3368186109299626585445827

theorem tailTrace_6559519 : CollatzResearch.WordTrace tailWord_6559519 prefixEnd_6559519 3368186109299626585445827 := by
  unfold tailWord_6559519
  simp only [CollatzResearch.WordTrace]
  refine ⟨239245312722990414500529611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159496875148660276333686407 239245312722990414500529611)
  ·
    refine ⟨358867969084485621750794417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239245312722990414500529611 358867969084485621750794417)
    ·
      refine ⟨269150976813364216313095813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358867969084485621750794417 269150976813364216313095813)
      ·
        refine ⟨50465808152505790558705465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269150976813364216313095813 50465808152505790558705465)
        ·
          refine ⟨37849356114379342919029099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50465808152505790558705465 37849356114379342919029099)
          ·
            refine ⟨56774034171569014378543649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37849356114379342919029099 56774034171569014378543649)
            ·
              refine ⟨42580525628676760783907737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56774034171569014378543649 42580525628676760783907737)
              ·
                refine ⟨31935394221507570587930803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42580525628676760783907737 31935394221507570587930803)
                ·
                  refine ⟨47903091332261355881896205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31935394221507570587930803 47903091332261355881896205)
                  ·
                    refine ⟨17963659249598008455711077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47903091332261355881896205 17963659249598008455711077)
                    ·
                      refine ⟨3368186109299626585445827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17963659249598008455711077 3368186109299626585445827)
                      ·
                        rfl

theorem cell23_6559519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_6559519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559519 prefixEnd_6559519 := by exact prefixLift 6559519
  have htrace : WordTrace (prefixWord ++ tailWord_6559519) baseStart_6559519 baseEnd_6559519 := by
    simpa [prefixWord, tailWord_6559519, baseEnd_6559519] using wordTrace_append hprefix tailTrace_6559519
  have hstable : (prefixWord ++ tailWord_6559519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559519).length < 2 ^ (prefixWord ++ tailWord_6559519).sum := by decide
  have hdescent : baseEnd_6559519 < baseStart_6559519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559614 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6559614 : Nat := 118140960795 + 6559614 * 2 ^ 59
def prefixEnd_6559614 : Nat := 4983230072969 + 3 ^ 40 * 6559614 * 2
def baseEnd_6559614 : Nat := 1122744963320601237919297

theorem tailTrace_6559614 : CollatzResearch.WordTrace tailWord_6559614 prefixEnd_6559614 1122744963320601237919297 := by
  unfold tailWord_6559614
  simp only [CollatzResearch.WordTrace]
  refine ⟨29906097207205780715654737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159499185105097497150158597 29906097207205780715654737)
  ·
    refine ⟨22429572905404335536741053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29906097207205780715654737 22429572905404335536741053)
    ·
      refine ⟨8411089839526625826277895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22429572905404335536741053 8411089839526625826277895)
      ·
        refine ⟨12616634759289938739416843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411089839526625826277895 12616634759289938739416843)
        ·
          refine ⟨18924952138934908109125265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616634759289938739416843 18924952138934908109125265)
          ·
            refine ⟨14193714104201181081843949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18924952138934908109125265 14193714104201181081843949)
            ·
              refine ⟨5322642789075442905691481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14193714104201181081843949 5322642789075442905691481)
              ·
                refine ⟨3991982091806582179268611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5322642789075442905691481 3991982091806582179268611)
                ·
                  refine ⟨5987973137709873268902917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991982091806582179268611 5987973137709873268902917)
                  ·
                    refine ⟨1122744963320601237919297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5987973137709873268902917 1122744963320601237919297)
                    ·
                      rfl

theorem cell23_6559614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6559614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559614 prefixEnd_6559614 := by exact prefixLift 6559614
  have htrace : WordTrace (prefixWord ++ tailWord_6559614) baseStart_6559614 baseEnd_6559614 := by
    simpa [prefixWord, tailWord_6559614, baseEnd_6559614] using wordTrace_append hprefix tailTrace_6559614
  have hstable : (prefixWord ++ tailWord_6559614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559614).length < 2 ^ (prefixWord ++ tailWord_6559614).sum := by decide
  have hdescent : baseEnd_6559614 < baseStart_6559614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559620 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_6559620 : Nat := 118140960795 + 6559620 * 2 ^ 59
def prefixEnd_6559620 : Nat := 4983230072969 + 3 ^ 40 * 6559620 * 2
def baseEnd_6559620 : Nat := 3368237970845730690282863

theorem tailTrace_6559620 : CollatzResearch.WordTrace tailWord_6559620 prefixEnd_6559620 3368237970845730690282863 := by
  unfold tailWord_6559620
  simp only [CollatzResearch.WordTrace]
  refine ⟨119624498247812254374978157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159499330997083005833304209 119624498247812254374978157)
  ·
    refine ⟨44859186842929595390616809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119624498247812254374978157 44859186842929595390616809)
    ·
      refine ⟨33644390132197196542962607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44859186842929595390616809 33644390132197196542962607)
      ·
        refine ⟨50466585198295794814443911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33644390132197196542962607 50466585198295794814443911)
        ·
          refine ⟨75699877797443692221665867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50466585198295794814443911 75699877797443692221665867)
          ·
            refine ⟨113549816696165538332498801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75699877797443692221665867 113549816696165538332498801)
            ·
              refine ⟨85162362522124153749374101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113549816696165538332498801 85162362522124153749374101)
              ·
                refine ⟨3991985743224569707001911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85162362522124153749374101 3991985743224569707001911)
                ·
                  refine ⟨5987978614836854560502867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991985743224569707001911 5987978614836854560502867)
                  ·
                    refine ⟨8981967922255281840754301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987978614836854560502867 8981967922255281840754301)
                    ·
                      refine ⟨3368237970845730690282863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8981967922255281840754301 3368237970845730690282863)
                      ·
                        rfl

theorem cell23_6559620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_6559620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559620 prefixEnd_6559620 := by exact prefixLift 6559620
  have htrace : WordTrace (prefixWord ++ tailWord_6559620) baseStart_6559620 baseEnd_6559620 := by
    simpa [prefixWord, tailWord_6559620, baseEnd_6559620] using wordTrace_append hprefix tailTrace_6559620
  have hstable : (prefixWord ++ tailWord_6559620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559620).length < 2 ^ (prefixWord ++ tailWord_6559620).sum := by decide
  have hdescent : baseEnd_6559620 < baseStart_6559620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559679 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 9]
def baseStart_6559679 : Nat := 118140960795 + 6559679 * 2 ^ 59
def prefixEnd_6559679 : Nat := 4983230072969 + 3 ^ 40 * 6559679 * 2
def baseEnd_6559679 : Nat := 1122756088734781986481697

theorem tailTrace_6559679 : CollatzResearch.WordTrace tailWord_6559679 prefixEnd_6559679 1122756088734781986481697 := by
  unfold tailWord_6559679
  simp only [CollatzResearch.WordTrace]
  refine ⟨239251148402410761826354091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159500765601607174550902727 239251148402410761826354091)
  ·
    refine ⟨358876722603616142739531137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239251148402410761826354091 358876722603616142739531137)
    ·
      refine ⟨269157541952712107054648353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358876722603616142739531137 269157541952712107054648353)
      ·
        refine ⟨201868156464534080290986265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269157541952712107054648353 201868156464534080290986265)
        ·
          refine ⟨151401117348400560218239699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201868156464534080290986265 151401117348400560218239699)
          ·
            refine ⟨227101676022600840327359549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151401117348400560218239699 227101676022600840327359549)
            ·
              refine ⟨85163128508475315122759831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227101676022600840327359549 85163128508475315122759831)
              ·
                refine ⟨127744692762712972684139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85163128508475315122759831 127744692762712972684139747)
                ·
                  refine ⟨191617039144069459026209621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127744692762712972684139747 191617039144069459026209621)
                  ·
                    refine ⟨1122756088734781986481697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 191617039144069459026209621 1122756088734781986481697)
                    ·
                      rfl

theorem cell23_6559679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_6559679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559679 prefixEnd_6559679 := by exact prefixLift 6559679
  have htrace : WordTrace (prefixWord ++ tailWord_6559679) baseStart_6559679 baseEnd_6559679 := by
    simpa [prefixWord, tailWord_6559679, baseEnd_6559679] using wordTrace_append hprefix tailTrace_6559679
  have hstable : (prefixWord ++ tailWord_6559679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559679).length < 2 ^ (prefixWord ++ tailWord_6559679).sum := by decide
  have hdescent : baseEnd_6559679 < baseStart_6559679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559703 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_6559703 : Nat := 118140960795 + 6559703 * 2 ^ 59
def prefixEnd_6559703 : Nat := 4983230072969 + 3 ^ 40 * 6559703 * 2
def baseEnd_6559703 : Nat := 3368280589740053865544981

theorem tailTrace_6559703 : CollatzResearch.WordTrace tailWord_6559703 prefixEnd_6559703 3368280589740053865544981 := by
  unfold tailWord_6559703
  simp only [CollatzResearch.WordTrace]
  refine ⟨239252023754323813925227763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159501349169549209283485175 239252023754323813925227763)
  ·
    refine ⟨358878035631485720887841645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239252023754323813925227763 358878035631485720887841645)
    ·
      refine ⟨134579263361807145332940617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358878035631485720887841645 134579263361807145332940617)
      ·
        refine ⟨100934447521355358999705463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134579263361807145332940617 100934447521355358999705463)
        ·
          refine ⟨151401671282033038499558195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100934447521355358999705463 151401671282033038499558195)
          ·
            refine ⟨227102506923049557749337293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151401671282033038499558195 227102506923049557749337293)
            ·
              refine ⟨85163440096143584156001485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227102506923049557749337293 85163440096143584156001485)
              ·
                refine ⟨31936290036053844058500557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85163440096143584156001485 31936290036053844058500557)
                ·
                  refine ⟨11976108763520191521937709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31936290036053844058500557 11976108763520191521937709)
                  ·
                    refine ⟨4491040786320071820726641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11976108763520191521937709 4491040786320071820726641)
                    ·
                      refine ⟨3368280589740053865544981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491040786320071820726641 3368280589740053865544981)
                      ·
                        rfl

theorem cell23_6559703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_6559703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559703 prefixEnd_6559703 := by exact prefixLift 6559703
  have htrace : WordTrace (prefixWord ++ tailWord_6559703) baseStart_6559703 baseEnd_6559703 := by
    simpa [prefixWord, tailWord_6559703, baseEnd_6559703] using wordTrace_append hprefix tailTrace_6559703
  have hstable : (prefixWord ++ tailWord_6559703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559703).length < 2 ^ (prefixWord ++ tailWord_6559703).sum := by decide
  have hdescent : baseEnd_6559703 < baseStart_6559703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559736 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_6559736 : Nat := 118140960795 + 6559736 * 2 ^ 59
def prefixEnd_6559736 : Nat := 4983230072969 + 3 ^ 40 * 6559736 * 2
def baseEnd_6559736 : Nat := 3368297534601652236432329

theorem tailTrace_6559736 : CollatzResearch.WordTrace tailWord_6559736 prefixEnd_6559736 3368297534601652236432329 := by
  unfold tailWord_6559736
  simp only [CollatzResearch.WordTrace]
  refine ⟨119626613681602130280589531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159502151575469507040786041 119626613681602130280589531)
  ·
    refine ⟨179439920522403195420884297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119626613681602130280589531 179439920522403195420884297)
    ·
      refine ⟨134579940391802396565663223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179439920522403195420884297 134579940391802396565663223)
      ·
        refine ⟨201869910587703594848494835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134579940391802396565663223 201869910587703594848494835)
        ·
          refine ⟨302804865881555392272742253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201869910587703594848494835 302804865881555392272742253)
          ·
            refine ⟨113551824705583272102278345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302804865881555392272742253 113551824705583272102278345)
            ·
              refine ⟨85163868529187454076708759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113551824705583272102278345 85163868529187454076708759)
              ·
                refine ⟨127745802793781181115063139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85163868529187454076708759 127745802793781181115063139)
                ·
                  refine ⟨191618704190671771672594709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127745802793781181115063139 191618704190671771672594709)
                  ·
                    refine ⟨8982126758937739297152877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 191618704190671771672594709 8982126758937739297152877)
                    ·
                      refine ⟨3368297534601652236432329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8982126758937739297152877 3368297534601652236432329)
                      ·
                        rfl

theorem cell23_6559736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_6559736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559736 prefixEnd_6559736 := by exact prefixLift 6559736
  have htrace : WordTrace (prefixWord ++ tailWord_6559736) baseStart_6559736 baseEnd_6559736 := by
    simpa [prefixWord, tailWord_6559736, baseEnd_6559736] using wordTrace_append hprefix tailTrace_6559736
  have hstable : (prefixWord ++ tailWord_6559736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559736).length < 2 ^ (prefixWord ++ tailWord_6559736).sum := by decide
  have hdescent : baseEnd_6559736 < baseStart_6559736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559756 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 7]
def baseStart_6559756 : Nat := 118140960795 + 6559756 * 2 ^ 59
def prefixEnd_6559756 : Nat := 4983230072969 + 3 ^ 40 * 6559756 * 2
def baseEnd_6559756 : Nat := 374256422690526906464693

theorem tailTrace_6559756 : CollatzResearch.WordTrace tailWord_6559756 prefixEnd_6559756 374256422690526906464693 := by
  unfold tailWord_6559756
  simp only [CollatzResearch.WordTrace]
  refine ⟨119626978411565901988453561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159502637882087869317938081 119626978411565901988453561)
  ·
    refine ⟨89720233808674426491340171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119626978411565901988453561 89720233808674426491340171)
    ·
      refine ⟨134580350713011639737010257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89720233808674426491340171 134580350713011639737010257)
      ·
        refine ⟨100935263034758729802757693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134580350713011639737010257 100935263034758729802757693)
        ·
          refine ⟨37850723638034523676034135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100935263034758729802757693 37850723638034523676034135)
          ·
            refine ⟨56776085457051785514051203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37850723638034523676034135 56776085457051785514051203)
            ·
              refine ⟨85164128185577678271076805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56776085457051785514051203 85164128185577678271076805)
              ·
                refine ⟨15968274034795814675826901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85164128185577678271076805 15968274034795814675826901)
                ·
                  refine ⟨374256422690526906464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15968274034795814675826901 374256422690526906464693)
                  ·
                    rfl

theorem cell23_6559756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_6559756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559756 prefixEnd_6559756 := by exact prefixLift 6559756
  have htrace : WordTrace (prefixWord ++ tailWord_6559756) baseStart_6559756 baseEnd_6559756 := by
    simpa [prefixWord, tailWord_6559756, baseEnd_6559756] using wordTrace_append hprefix tailTrace_6559756
  have hstable : (prefixWord ++ tailWord_6559756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559756).length < 2 ^ (prefixWord ++ tailWord_6559756).sum := by decide
  have hdescent : baseEnd_6559756 < baseStart_6559756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559790 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_6559790 : Nat := 118140960795 + 6559790 * 2 ^ 59
def prefixEnd_6559790 : Nat := 4983230072969 + 3 ^ 40 * 6559790 * 2
def baseEnd_6559790 : Nat := 374258362506332780573009

theorem tailTrace_6559790 : CollatzResearch.WordTrace tailWord_6559790 prefixEnd_6559790 374258362506332780573009 := by
  unfold tailWord_6559790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29906899613126078472955603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159503464603339085189096549 29906899613126078472955603)
  ·
    refine ⟨44860349419689117709433405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29906899613126078472955603 44860349419689117709433405)
    ·
      refine ⟨16822631032383419141037527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44860349419689117709433405 16822631032383419141037527)
      ·
        refine ⟨25233946548575128711556291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16822631032383419141037527 25233946548575128711556291)
        ·
          refine ⟨37850919822862693067334437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25233946548575128711556291 37850919822862693067334437)
          ·
            refine ⟨7097047466786754950125207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37850919822862693067334437 7097047466786754950125207)
            ·
              refine ⟨10645571200180132425187811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097047466786754950125207 10645571200180132425187811)
              ·
                refine ⟨15968356800270198637781717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10645571200180132425187811 15968356800270198637781717)
                ·
                  refine ⟨374258362506332780573009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15968356800270198637781717 374258362506332780573009)
                  ·
                    rfl

theorem cell23_6559790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_6559790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559790 prefixEnd_6559790 := by exact prefixLift 6559790
  have htrace : WordTrace (prefixWord ++ tailWord_6559790) baseStart_6559790 baseEnd_6559790 := by
    simpa [prefixWord, tailWord_6559790, baseEnd_6559790] using wordTrace_append hprefix tailTrace_6559790
  have hstable : (prefixWord ++ tailWord_6559790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559790).length < 2 ^ (prefixWord ++ tailWord_6559790).sum := by decide
  have hdescent : baseEnd_6559790 < baseStart_6559790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559801 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6559801 : Nat := 118140960795 + 6559801 * 2 ^ 59
def prefixEnd_6559801 : Nat := 4983230072969 + 3 ^ 40 * 6559801 * 2
def baseEnd_6559801 : Nat := 3368330910844194482119531

theorem tailTrace_6559801 : CollatzResearch.WordTrace tailWord_6559801 prefixEnd_6559801 3368330910844194482119531 := by
  unfold tailWord_6559801
  simp only [CollatzResearch.WordTrace]
  refine ⟨239255598107968776662295257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159503732071979184441530171 239255598107968776662295257)
  ·
    refine ⟨179441698580976582496721443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239255598107968776662295257 179441698580976582496721443)
    ·
      refine ⟨269162547871464873745082165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179441698580976582496721443 269162547871464873745082165)
      ·
        refine ⟨25233988862949831913601453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269162547871464873745082165 25233988862949831913601453)
        ·
          refine ⟨9462745823606186967600545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25233988862949831913601453 9462745823606186967600545)
          ·
            refine ⟨7097059367704640225700409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462745823606186967600545 7097059367704640225700409)
            ·
              refine ⟨5322794525778480169275307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097059367704640225700409 5322794525778480169275307)
              ·
                refine ⟨7984191788667720253912961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322794525778480169275307 7984191788667720253912961)
                ·
                  refine ⟨5988143841500790190434721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7984191788667720253912961 5988143841500790190434721)
                  ·
                    refine ⟨4491107881125592642826041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988143841500790190434721 4491107881125592642826041)
                    ·
                      refine ⟨3368330910844194482119531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491107881125592642826041 3368330910844194482119531)
                      ·
                        rfl

theorem cell23_6559801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6559801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559801 prefixEnd_6559801 := by exact prefixLift 6559801
  have htrace : WordTrace (prefixWord ++ tailWord_6559801) baseStart_6559801 baseEnd_6559801 := by
    simpa [prefixWord, tailWord_6559801, baseEnd_6559801] using wordTrace_append hprefix tailTrace_6559801
  have hstable : (prefixWord ++ tailWord_6559801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559801).length < 2 ^ (prefixWord ++ tailWord_6559801).sum := by decide
  have hdescent : baseEnd_6559801 < baseStart_6559801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559823 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 6, 2]
def baseStart_6559823 : Nat := 118140960795 + 6559823 * 2 ^ 59
def prefixEnd_6559823 : Nat := 4983230072969 + 3 ^ 40 * 6559823 * 2
def baseEnd_6559823 : Nat := 3368342207418593396044429

theorem tailTrace_6559823 : CollatzResearch.WordTrace tailWord_6559823 prefixEnd_6559823 3368342207418593396044429 := by
  unfold tailWord_6559823
  simp only [CollatzResearch.WordTrace]
  refine ⟨239256400513889074419596123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159504267009259382946397415 239256400513889074419596123)
  ·
    refine ⟨358884600770833611629394185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239256400513889074419596123 358884600770833611629394185)
    ·
      refine ⟨269163450578125208722045639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358884600770833611629394185 269163450578125208722045639)
      ·
        refine ⟨403745175867187813083068459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269163450578125208722045639 403745175867187813083068459)
        ·
          refine ⟨605617763800781719624602689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403745175867187813083068459 605617763800781719624602689)
          ·
            refine ⟨454213322850586289718452017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605617763800781719624602689 454213322850586289718452017)
            ·
              refine ⟨340659992137939717288839013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454213322850586289718452017 340659992137939717288839013)
              ·
                refine ⟨63873748525863696991657315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340659992137939717288839013 63873748525863696991657315)
                ·
                  refine ⟨95810622788795545487485973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63873748525863696991657315 95810622788795545487485973)
                  ·
                    refine ⟨4491122943224791194725905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95810622788795545487485973 4491122943224791194725905)
                    ·
                      refine ⟨3368342207418593396044429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491122943224791194725905 3368342207418593396044429)
                      ·
                        rfl

theorem cell23_6559823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6, 2].length) (baseStart_6559823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559823 prefixEnd_6559823 := by exact prefixLift 6559823
  have htrace : WordTrace (prefixWord ++ tailWord_6559823) baseStart_6559823 baseEnd_6559823 := by
    simpa [prefixWord, tailWord_6559823, baseEnd_6559823] using wordTrace_append hprefix tailTrace_6559823
  have hstable : (prefixWord ++ tailWord_6559823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559823).length < 2 ^ (prefixWord ++ tailWord_6559823).sum := by decide
  have hdescent : baseEnd_6559823 < baseStart_6559823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559863 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 6]
def baseStart_6559863 : Nat := 118140960795 + 6559863 * 2 ^ 59
def prefixEnd_6559863 : Nat := 4983230072969 + 3 ^ 40 * 6559863 * 2
def baseEnd_6559863 : Nat := 374262527404974804393805

theorem tailTrace_6559863 : CollatzResearch.WordTrace tailWord_6559863 prefixEnd_6559863 374262527404974804393805 := by
  unfold tailWord_6559863
  simp only [CollatzResearch.WordTrace]
  refine ⟨239257859433744161251052243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159505239622496107500701495 239257859433744161251052243)
  ·
    refine ⟨358886789150616241876578365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239257859433744161251052243 358886789150616241876578365)
    ·
      refine ⟨134582545931481090703716887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358886789150616241876578365 134582545931481090703716887)
      ·
        refine ⟨201873818897221636055575331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134582545931481090703716887 201873818897221636055575331)
        ·
          refine ⟨302810728345832454083362997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201873818897221636055575331 302810728345832454083362997)
          ·
            refine ⟨28388505782421792570315281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302810728345832454083362997 28388505782421792570315281)
            ·
              refine ⟨21291379336816344427736461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28388505782421792570315281 21291379336816344427736461)
              ·
                refine ⟨7984267251306129160401173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21291379336816344427736461 7984267251306129160401173)
                ·
                  refine ⟨374262527404974804393805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7984267251306129160401173 374262527404974804393805)
                  ·
                    rfl

theorem cell23_6559863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 6].length) (baseStart_6559863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559863 prefixEnd_6559863 := by exact prefixLift 6559863
  have htrace : WordTrace (prefixWord ++ tailWord_6559863) baseStart_6559863 baseEnd_6559863 := by
    simpa [prefixWord, tailWord_6559863, baseEnd_6559863] using wordTrace_append hprefix tailTrace_6559863
  have hstable : (prefixWord ++ tailWord_6559863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559863).length < 2 ^ (prefixWord ++ tailWord_6559863).sum := by decide
  have hdescent : baseEnd_6559863 < baseStart_6559863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559877 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_6559877 : Nat := 118140960795 + 6559877 * 2 ^ 59
def prefixEnd_6559877 : Nat := 4983230072969 + 3 ^ 40 * 6559877 * 2
def baseEnd_6559877 : Nat := 3368369935373936184769181

theorem tailTrace_6559877 : CollatzResearch.WordTrace tailWord_6559877 prefixEnd_6559877 3368369935373936184769181 := by
  unfold tailWord_6559877
  simp only [CollatzResearch.WordTrace]
  refine ⟨239258370055693441642061885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159505580037128961094707923 239258370055693441642061885)
  ·
    refine ⟨89721888770885040615773207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239258370055693441642061885 89721888770885040615773207)
    ·
      refine ⟨134582833156327560923659811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89721888770885040615773207 134582833156327560923659811)
      ·
        refine ⟨201874249734491341385489717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134582833156327560923659811 201874249734491341385489717)
        ·
          refine ⟨18925710912608563254889661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201874249734491341385489717 18925710912608563254889661)
          ·
            refine ⟨7097141592228211220583623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18925710912608563254889661 7097141592228211220583623)
            ·
              refine ⟨10645712388342316830875435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097141592228211220583623 10645712388342316830875435)
              ·
                refine ⟨15968568582513475246313153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10645712388342316830875435 15968568582513475246313153)
                ·
                  refine ⟨11976426436885106434734865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15968568582513475246313153 11976426436885106434734865)
                  ·
                    refine ⟨8982319827663829826051149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11976426436885106434734865 8982319827663829826051149)
                    ·
                      refine ⟨3368369935373936184769181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8982319827663829826051149 3368369935373936184769181)
                      ·
                        rfl

theorem cell23_6559877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_6559877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559877 prefixEnd_6559877 := by exact prefixLift 6559877
  have htrace : WordTrace (prefixWord ++ tailWord_6559877) baseStart_6559877 baseEnd_6559877 := by
    simpa [prefixWord, tailWord_6559877, baseEnd_6559877] using wordTrace_append hprefix tailTrace_6559877
  have hstable : (prefixWord ++ tailWord_6559877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559877).length < 2 ^ (prefixWord ++ tailWord_6559877).sum := by decide
  have hdescent : baseEnd_6559877 < baseStart_6559877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559914 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_6559914 : Nat := 118140960795 + 6559914 * 2 ^ 59
def prefixEnd_6559914 : Nat := 4983230072969 + 3 ^ 40 * 6559914 * 2
def baseEnd_6559914 : Nat := 374265437128683615556279

theorem tailTrace_6559914 : CollatzResearch.WordTrace tailWord_6559914 prefixEnd_6559914 374265437128683615556279 := by
  unfold tailWord_6559914
  simp only [CollatzResearch.WordTrace]
  refine ⟨59814929889139849240289699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159506479704372931307439197 59814929889139849240289699)
  ·
    refine ⟨89722394833709773860434549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59814929889139849240289699 89722394833709773860434549)
    ·
      refine ⟨8411474515660291299415739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89722394833709773860434549 8411474515660291299415739)
      ·
        refine ⟨12617211773490436949123609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411474515660291299415739 12617211773490436949123609)
        ·
          refine ⟨9462908830117827711842707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12617211773490436949123609 9462908830117827711842707)
          ·
            refine ⟨14194363245176741567764061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462908830117827711842707 14194363245176741567764061)
            ·
              refine ⟨5322886216941278087911523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14194363245176741567764061 5322886216941278087911523)
              ·
                refine ⟨7984329325411917131867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322886216941278087911523 7984329325411917131867285)
                ·
                  refine ⟨374265437128683615556279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7984329325411917131867285 374265437128683615556279)
                  ·
                    rfl

theorem cell23_6559914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_6559914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559914 prefixEnd_6559914 := by exact prefixLift 6559914
  have htrace : WordTrace (prefixWord ++ tailWord_6559914) baseStart_6559914 baseEnd_6559914 := by
    simpa [prefixWord, tailWord_6559914, baseEnd_6559914] using wordTrace_append hprefix tailTrace_6559914
  have hstable : (prefixWord ++ tailWord_6559914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559914).length < 2 ^ (prefixWord ++ tailWord_6559914).sum := by decide
  have hdescent : baseEnd_6559914 < baseStart_6559914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559917 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_6559917 : Nat := 118140960795 + 6559917 * 2 ^ 59
def prefixEnd_6559917 : Nat := 4983230072969 + 3 ^ 40 * 6559917 * 2
def baseEnd_6559917 : Nat := 3368390474600116028268997

theorem tailTrace_6559917 : CollatzResearch.WordTrace tailWord_6559917 prefixEnd_6559917 3368390474600116028268997 := by
  unfold tailWord_6559917
  simp only [CollatzResearch.WordTrace]
  refine ⟨239259828975548528473518005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159506552650365685649012003 239259828975548528473518005)
  ·
    refine ⟨22430608966457674544392313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239259828975548528473518005 22430608966457674544392313)
    ·
      refine ⟨16822956724843255908294235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22430608966457674544392313 16822956724843255908294235)
      ·
        refine ⟨25234435087264883862441353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16822956724843255908294235 25234435087264883862441353)
        ·
          refine ⟨18925826315448662896831015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25234435087264883862441353 18925826315448662896831015)
          ·
            refine ⟨28388739473172994345246523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925826315448662896831015 28388739473172994345246523)
            ·
              refine ⟨42583109209759491517869785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28388739473172994345246523 42583109209759491517869785)
              ·
                refine ⟨31937331907319618638402339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42583109209759491517869785 31937331907319618638402339)
                ·
                  refine ⟨47905997860979427957603509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31937331907319618638402339 47905997860979427957603509)
                  ·
                    refine ⟨4491187299466821371025329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47905997860979427957603509 4491187299466821371025329)
                    ·
                      refine ⟨3368390474600116028268997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491187299466821371025329 3368390474600116028268997)
                      ·
                        rfl

theorem cell23_6559917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_6559917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559917 prefixEnd_6559917 := by exact prefixLift 6559917
  have htrace : WordTrace (prefixWord ++ tailWord_6559917) baseStart_6559917 baseEnd_6559917 := by
    simpa [prefixWord, tailWord_6559917, baseEnd_6559917] using wordTrace_append hprefix tailTrace_6559917
  have hstable : (prefixWord ++ tailWord_6559917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559917).length < 2 ^ (prefixWord ++ tailWord_6559917).sum := by decide
  have hdescent : baseEnd_6559917 < baseStart_6559917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559930 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_6559930 : Nat := 118140960795 + 6559930 * 2 ^ 59
def prefixEnd_6559930 : Nat := 4983230072969 + 3 ^ 40 * 6559930 * 2
def baseEnd_6559930 : Nat := 3368397149848624477406437

theorem tailTrace_6559930 : CollatzResearch.WordTrace tailWord_6559930 prefixEnd_6559930 3368397149848624477406437 := by
  unfold tailWord_6559930
  simp only [CollatzResearch.WordTrace]
  refine ⟨59815075781125357923435311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159506868749667621129160829 59815075781125357923435311)
  ·
    refine ⟨89722613671688036885152967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59815075781125357923435311 89722613671688036885152967)
    ·
      refine ⟨134583920507532055327729451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89722613671688036885152967 134583920507532055327729451)
      ·
        refine ⟨201875880761298082991594177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134583920507532055327729451 201875880761298082991594177)
        ·
          refine ⟨151406910570973562243695633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201875880761298082991594177 151406910570973562243695633)
          ·
            refine ⟨113555182928230171682771725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151406910570973562243695633 113555182928230171682771725)
            ·
              refine ⟨42583193598086314381039397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113555182928230171682771725 42583193598086314381039397)
              ·
                refine ⟨7984348799641183946444887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42583193598086314381039397 7984348799641183946444887)
                ·
                  refine ⟨11976523199461775919667331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7984348799641183946444887 11976523199461775919667331)
                  ·
                    refine ⟨17964784799192663879500997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11976523199461775919667331 17964784799192663879500997)
                    ·
                      refine ⟨3368397149848624477406437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17964784799192663879500997 3368397149848624477406437)
                      ·
                        rfl

theorem cell23_6559930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_6559930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559930 prefixEnd_6559930 := by exact prefixLift 6559930
  have htrace : WordTrace (prefixWord ++ tailWord_6559930) baseStart_6559930 baseEnd_6559930 := by
    simpa [prefixWord, tailWord_6559930, baseEnd_6559930] using wordTrace_append hprefix tailTrace_6559930
  have hstable : (prefixWord ++ tailWord_6559930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559930).length < 2 ^ (prefixWord ++ tailWord_6559930).sum := by decide
  have hdescent : baseEnd_6559930 < baseStart_6559930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559933 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_6559933 : Nat := 118140960795 + 6559933 * 2 ^ 59
def prefixEnd_6559933 : Nat := 4983230072969 + 3 ^ 40 * 6559933 * 2
def baseEnd_6559933 : Nat := 3368398690290587965668923

theorem tailTrace_6559933 : CollatzResearch.WordTrace tailWord_6559933 prefixEnd_6559933 3368398690290587965668923 := by
  unfold tailWord_6559933
  simp only [CollatzResearch.WordTrace]
  refine ⟨239260412543490563206100453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159506941695660375470733635 239260412543490563206100453)
  ·
    refine ⟨44861327351904480601143835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239260412543490563206100453 44861327351904480601143835)
    ·
      refine ⟨67291991027856720901715753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44861327351904480601143835 67291991027856720901715753)
      ·
        refine ⟨50468993270892540676286815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67291991027856720901715753 50468993270892540676286815)
        ·
          refine ⟨75703489906338811014430223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50468993270892540676286815 75703489906338811014430223)
          ·
            refine ⟨113555234859508216521645335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75703489906338811014430223 113555234859508216521645335)
            ·
              refine ⟨170332852289262324782468003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113555234859508216521645335 170332852289262324782468003)
              ·
                refine ⟨255499278433893487173702005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170332852289262324782468003 255499278433893487173702005)
                ·
                  refine ⟨23953057353177514422534563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255499278433893487173702005 23953057353177514422534563)
                  ·
                    refine ⟨35929586029766271633801845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23953057353177514422534563 35929586029766271633801845)
                    ·
                      refine ⟨3368398690290587965668923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35929586029766271633801845 3368398690290587965668923)
                      ·
                        rfl

theorem cell23_6559933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_6559933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559933 prefixEnd_6559933 := by exact prefixLift 6559933
  have htrace : WordTrace (prefixWord ++ tailWord_6559933) baseStart_6559933 baseEnd_6559933 := by
    simpa [prefixWord, tailWord_6559933, baseEnd_6559933] using wordTrace_append hprefix tailTrace_6559933
  have hstable : (prefixWord ++ tailWord_6559933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559933).length < 2 ^ (prefixWord ++ tailWord_6559933).sum := by decide
  have hdescent : baseEnd_6559933 < baseStart_6559933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559950 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6559950 : Nat := 118140960795 + 6559950 * 2 ^ 59
def prefixEnd_6559950 : Nat := 4983230072969 + 3 ^ 40 * 6559950 * 2
def baseEnd_6559950 : Nat := 3368407419461714399156345

theorem tailTrace_6559950 : CollatzResearch.WordTrace tailWord_6559950 prefixEnd_6559950 3368407419461714399156345 := by
  unfold tailWord_6559950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907629073053621888683663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159507355056285983406312869 29907629073053621888683663)
  ·
    refine ⟨44861443609580432833025495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29907629073053621888683663 44861443609580432833025495)
    ·
      refine ⟨67292165414370649249538243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44861443609580432833025495 67292165414370649249538243)
      ·
        refine ⟨100938248121555973874307365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67292165414370649249538243 100938248121555973874307365)
        ·
          refine ⟨18925921522791745101432631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100938248121555973874307365 18925921522791745101432631)
          ·
            refine ⟨28388882284187617652148947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925921522791745101432631 28388882284187617652148947)
            ·
              refine ⟨42583323426281426478223421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28388882284187617652148947 42583323426281426478223421)
              ·
                refine ⟨15968746284855534929333783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42583323426281426478223421 15968746284855534929333783)
                ·
                  refine ⟨23953119427283302394000675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15968746284855534929333783 23953119427283302394000675)
                  ·
                    refine ⟨35929679140924953591001013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23953119427283302394000675 35929679140924953591001013)
                    ·
                      refine ⟨3368407419461714399156345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35929679140924953591001013 3368407419461714399156345)
                      ·
                        rfl

theorem cell23_6559950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6559950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559950 prefixEnd_6559950 := by exact prefixLift 6559950
  have htrace : WordTrace (prefixWord ++ tailWord_6559950) baseStart_6559950 baseEnd_6559950 := by
    simpa [prefixWord, tailWord_6559950, baseEnd_6559950] using wordTrace_append hprefix tailTrace_6559950
  have hstable : (prefixWord ++ tailWord_6559950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559950).length < 2 ^ (prefixWord ++ tailWord_6559950).sum := by decide
  have hdescent : baseEnd_6559950 < baseStart_6559950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559980 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_6559980 : Nat := 118140960795 + 6559980 * 2 ^ 59
def prefixEnd_6559980 : Nat := 4983230072969 + 3 ^ 40 * 6559980 * 2
def baseEnd_6559980 : Nat := 3368422823881349281781207

theorem tailTrace_6559980 : CollatzResearch.WordTrace tailWord_6559980 prefixEnd_6559980 3368422823881349281781207 := by
  unfold tailWord_6559980
  simp only [CollatzResearch.WordTrace]
  refine ⟨119631063387160145116530697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159508084516213526822040929 119631063387160145116530697)
  ·
    refine ⟨89723297540370108837398023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119631063387160145116530697 89723297540370108837398023)
    ·
      refine ⟨134584946310555163256097035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89723297540370108837398023 134584946310555163256097035)
      ·
        refine ⟨201877419465832744884145553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134584946310555163256097035 201877419465832744884145553)
        ·
          refine ⟨151408064599374558663109165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201877419465832744884145553 151408064599374558663109165)
          ·
            refine ⟨56778024224765459498665937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151408064599374558663109165 56778024224765459498665937)
            ·
              refine ⟨42583518168574094623999453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56778024224765459498665937 42583518168574094623999453)
              ·
                refine ⟨15968819313215285483999795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42583518168574094623999453 15968819313215285483999795)
                ·
                  refine ⟨23953228969822928225999693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15968819313215285483999795 23953228969822928225999693)
                  ·
                    refine ⟨8982460863683598084749885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23953228969822928225999693 8982460863683598084749885)
                    ·
                      refine ⟨3368422823881349281781207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8982460863683598084749885 3368422823881349281781207)
                      ·
                        rfl

theorem cell23_6559980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_6559980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559980 prefixEnd_6559980 := by exact prefixLift 6559980
  have htrace : WordTrace (prefixWord ++ tailWord_6559980) baseStart_6559980 baseEnd_6559980 := by
    simpa [prefixWord, tailWord_6559980, baseEnd_6559980] using wordTrace_append hprefix tailTrace_6559980
  have hstable : (prefixWord ++ tailWord_6559980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559980).length < 2 ^ (prefixWord ++ tailWord_6559980).sum := by decide
  have hdescent : baseEnd_6559980 < baseStart_6559980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559981 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6559981 : Nat := 118140960795 + 6559981 * 2 ^ 59
def prefixEnd_6559981 : Nat := 4983230072969 + 3 ^ 40 * 6559981 * 2
def baseEnd_6559981 : Nat := 3368423337362003777868703

theorem tailTrace_6559981 : CollatzResearch.WordTrace tailWord_6559981 prefixEnd_6559981 3368423337362003777868703 := by
  unfold tailWord_6559981
  simp only [CollatzResearch.WordTrace]
  refine ⟨239262163247316667403847797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159508108831544444935898531 239262163247316667403847797)
  ·
    refine ⟨22430827804435937569110731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239262163247316667403847797 22430827804435937569110731)
    ·
      refine ⟨33646241706653906353666097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22430827804435937569110731 33646241706653906353666097)
      ·
        refine ⟨25234681279990429765249573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33646241706653906353666097 25234681279990429765249573)
        ·
          refine ⟨4731502739998205580984295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25234681279990429765249573 4731502739998205580984295)
          ·
            refine ⟨7097254109997308371476443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731502739998205580984295 7097254109997308371476443)
            ·
              refine ⟨10645881164995962557214665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097254109997308371476443 10645881164995962557214665)
              ·
                refine ⟨7984410873746971917910999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10645881164995962557214665 7984410873746971917910999)
                ·
                  refine ⟨11976616310620457876866499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7984410873746971917910999 11976616310620457876866499)
                  ·
                    refine ⟨17964924465930686815299749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11976616310620457876866499 17964924465930686815299749)
                    ·
                      refine ⟨3368423337362003777868703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17964924465930686815299749 3368423337362003777868703)
                      ·
                        rfl

theorem cell23_6559981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6559981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559981 prefixEnd_6559981 := by exact prefixLift 6559981
  have htrace : WordTrace (prefixWord ++ tailWord_6559981) baseStart_6559981 baseEnd_6559981 := by
    simpa [prefixWord, tailWord_6559981, baseEnd_6559981] using wordTrace_append hprefix tailTrace_6559981
  have hstable : (prefixWord ++ tailWord_6559981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559981).length < 2 ^ (prefixWord ++ tailWord_6559981).sum := by decide
  have hdescent : baseEnd_6559981 < baseStart_6559981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6559993 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6559993 : Nat := 118140960795 + 6559993 * 2 ^ 59
def prefixEnd_6559993 : Nat := 4983230072969 + 3 ^ 40 * 6559993 * 2
def baseEnd_6559993 : Nat := 3368429499129857730918647

theorem tailTrace_6559993 : CollatzResearch.WordTrace tailWord_6559993 prefixEnd_6559993 3368429499129857730918647 := by
  unfold tailWord_6559993
  simp only [CollatzResearch.WordTrace]
  refine ⟨239262600923273193453284633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159508400615515462302189755 239262600923273193453284633)
  ·
    refine ⟨179446950692454895089963475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239262600923273193453284633 179446950692454895089963475)
    ·
      refine ⟨269170426038682342634945213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179446950692454895089963475 269170426038682342634945213)
      ·
        refine ⟨100938909764505878488104455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269170426038682342634945213 100938909764505878488104455)
        ·
          refine ⟨151408364646758817732156683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100938909764505878488104455 151408364646758817732156683)
          ·
            refine ⟨227112546970138226598235025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151408364646758817732156683 227112546970138226598235025)
            ·
              refine ⟨170334410227603669948676269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227112546970138226598235025 170334410227603669948676269)
              ·
                refine ⟨63875403835351376230753601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170334410227603669948676269 63875403835351376230753601)
                ·
                  refine ⟨47906552876513532173065201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63875403835351376230753601 47906552876513532173065201)
                  ·
                    refine ⟨35929914657385149129798901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47906552876513532173065201 35929914657385149129798901)
                    ·
                      refine ⟨3368429499129857730918647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35929914657385149129798901 3368429499129857730918647)
                      ·
                        rfl

theorem cell23_6559993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6559993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6559993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6559993 prefixEnd_6559993 := by exact prefixLift 6559993
  have htrace : WordTrace (prefixWord ++ tailWord_6559993) baseStart_6559993 baseEnd_6559993 := by
    simpa [prefixWord, tailWord_6559993, baseEnd_6559993] using wordTrace_append hprefix tailTrace_6559993
  have hstable : (prefixWord ++ tailWord_6559993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6559993).length < 2 ^ (prefixWord ++ tailWord_6559993).sum := by decide
  have hdescent : baseEnd_6559993 < baseStart_6559993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6559993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560014 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6560014 : Nat := 118140960795 + 6560014 * 2 ^ 59
def prefixEnd_6560014 : Nat := 4983230072969 + 3 ^ 40 * 6560014 * 2
def baseEnd_6560014 : Nat := 3368440282223602148756051

theorem tailTrace_6560014 : CollatzResearch.WordTrace tailWord_6560014 prefixEnd_6560014 3368440282223602148756051 := by
  unfold tailWord_6560014
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907920857024639254974887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159508911237464742693199397 29907920857024639254974887)
  ·
    refine ⟨44861881285536958882462331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29907920857024639254974887 44861881285536958882462331)
    ·
      refine ⟨67292821928305438323693497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44861881285536958882462331 67292821928305438323693497)
      ·
        refine ⟨50469616446229078742770123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67292821928305438323693497 50469616446229078742770123)
        ·
          refine ⟨75704424669343618114155185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50469616446229078742770123 75704424669343618114155185)
          ·
            refine ⟨56778318502007713585616389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75704424669343618114155185 56778318502007713585616389)
            ·
              refine ⟨10645934719126446297303073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56778318502007713585616389 10645934719126446297303073)
              ·
                refine ⟨7984451039344834722977305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10645934719126446297303073 7984451039344834722977305)
                ·
                  refine ⟨5988338279508626042232979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7984451039344834722977305 5988338279508626042232979)
                  ·
                    refine ⟨8982507419262939063349469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5988338279508626042232979 8982507419262939063349469)
                    ·
                      refine ⟨3368440282223602148756051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8982507419262939063349469 3368440282223602148756051)
                      ·
                        rfl

theorem cell23_6560014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6560014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560014 prefixEnd_6560014 := by exact prefixLift 6560014
  have htrace : WordTrace (prefixWord ++ tailWord_6560014) baseStart_6560014 baseEnd_6560014 := by
    simpa [prefixWord, tailWord_6560014, baseEnd_6560014] using wordTrace_append hprefix tailTrace_6560014
  have hstable : (prefixWord ++ tailWord_6560014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560014).length < 2 ^ (prefixWord ++ tailWord_6560014).sum := by decide
  have hdescent : baseEnd_6560014 < baseStart_6560014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560161 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6560161 : Nat := 118140960795 + 6560161 * 2 ^ 59
def prefixEnd_6560161 : Nat := 4983230072969 + 3 ^ 40 * 6560161 * 2
def baseEnd_6560161 : Nat := 3368515763879813073617875

theorem tailTrace_6560161 : CollatzResearch.WordTrace tailWord_6560161 prefixEnd_6560161 3368515763879813073617875 := by
  unfold tailWord_6560161
  simp only [CollatzResearch.WordTrace]
  refine ⟨239268728386664558145400337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159512485591109705430266891 239268728386664558145400337)
  ·
    refine ⟨179451546289998418609050253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239268728386664558145400337 179451546289998418609050253)
    ·
      refine ⟨67294329858749406978393845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179451546289998418609050253 67294329858749406978393845)
      ·
        refine ⟨6308843424257756904224423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67294329858749406978393845 6308843424257756904224423)
        ·
          refine ⟨9463265136386635356336635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308843424257756904224423 9463265136386635356336635)
          ·
            refine ⟨14194897704579953034504953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463265136386635356336635 14194897704579953034504953)
            ·
              refine ⟨10646173278434964775878715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14194897704579953034504953 10646173278434964775878715)
              ·
                refine ⟨15969259917652447163818073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646173278434964775878715 15969259917652447163818073)
                ·
                  refine ⟨11976944938239335372863555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15969259917652447163818073 11976944938239335372863555)
                  ·
                    refine ⟨17965417407359003059295333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11976944938239335372863555 17965417407359003059295333)
                    ·
                      refine ⟨3368515763879813073617875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17965417407359003059295333 3368515763879813073617875)
                      ·
                        rfl

theorem cell23_6560161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6560161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560161 prefixEnd_6560161 := by exact prefixLift 6560161
  have htrace : WordTrace (prefixWord ++ tailWord_6560161) baseStart_6560161 baseEnd_6560161 := by
    simpa [prefixWord, tailWord_6560161, baseEnd_6560161] using wordTrace_append hprefix tailTrace_6560161
  have hstable : (prefixWord ++ tailWord_6560161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560161).length < 2 ^ (prefixWord ++ tailWord_6560161).sum := by decide
  have hdescent : baseEnd_6560161 < baseStart_6560161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560188 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_6560188 : Nat := 118140960795 + 6560188 * 2 ^ 59
def prefixEnd_6560188 : Nat := 4983230072969 + 3 ^ 40 * 6560188 * 2
def baseEnd_6560188 : Nat := 1122843209285828155993417

theorem tailTrace_6560188 : CollatzResearch.WordTrace tailWord_6560188 prefixEnd_6560188 1122843209285828155993417 := by
  unfold tailWord_6560188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119634856578783370878316609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159513142105044494504422145 119634856578783370878316609)
  ·
    refine ⟨89726142434087528158737457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119634856578783370878316609 89726142434087528158737457)
    ·
      refine ⟨67294606825565646119053093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89726142434087528158737457 67294606825565646119053093)
      ·
        refine ⟨12617738779793558647322455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67294606825565646119053093 12617738779793558647322455)
        ·
          refine ⟨18926608169690337970983683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12617738779793558647322455 18926608169690337970983683)
          ·
            refine ⟨28389912254535506956475525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18926608169690337970983683 28389912254535506956475525)
            ·
              refine ⟨5323108547725407554339161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28389912254535506956475525 5323108547725407554339161)
              ·
                refine ⟨3992331410794055665754371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323108547725407554339161 3992331410794055665754371)
                ·
                  refine ⟨5988497116191083498631557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992331410794055665754371 5988497116191083498631557)
                  ·
                    refine ⟨1122843209285828155993417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5988497116191083498631557 1122843209285828155993417)
                    ·
                      rfl

theorem cell23_6560188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_6560188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560188 prefixEnd_6560188 := by exact prefixLift 6560188
  have htrace : WordTrace (prefixWord ++ tailWord_6560188) baseStart_6560188 baseEnd_6560188 := by
    simpa [prefixWord, tailWord_6560188, baseEnd_6560188] using wordTrace_append hprefix tailTrace_6560188
  have hstable : (prefixWord ++ tailWord_6560188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560188).length < 2 ^ (prefixWord ++ tailWord_6560188).sum := by decide
  have hdescent : baseEnd_6560188 < baseStart_6560188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560214 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_6560214 : Nat := 118140960795 + 6560214 * 2 ^ 59
def prefixEnd_6560214 : Nat := 4983230072969 + 3 ^ 40 * 6560214 * 2
def baseEnd_6560214 : Nat := 1122847659451500455418377

theorem tailTrace_6560214 : CollatzResearch.WordTrace tailWord_6560214 prefixEnd_6560214 1122847659451500455418377 := by
  unfold tailWord_6560214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954416340967034262317481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159513774303648365464719797 14954416340967034262317481)
  ·
    refine ⟨11215812255725275696738111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14954416340967034262317481 11215812255725275696738111)
    ·
      refine ⟨16823718383587913545107167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215812255725275696738111 16823718383587913545107167)
      ·
        refine ⟨25235577575381870317660751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823718383587913545107167 25235577575381870317660751)
        ·
          refine ⟨37853366363072805476491127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25235577575381870317660751 37853366363072805476491127)
          ·
            refine ⟨56780049544609208214736691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37853366363072805476491127 56780049544609208214736691)
            ·
              refine ⟨85170074316913812322105037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56780049544609208214736691 85170074316913812322105037)
              ·
                refine ⟨31938777868842679620789389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85170074316913812322105037 31938777868842679620789389)
                ·
                  refine ⟨11977041700816004857796021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31938777868842679620789389 11977041700816004857796021)
                  ·
                    refine ⟨1122847659451500455418377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11977041700816004857796021 1122847659451500455418377)
                    ·
                      rfl

theorem cell23_6560214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_6560214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560214 prefixEnd_6560214 := by exact prefixLift 6560214
  have htrace : WordTrace (prefixWord ++ tailWord_6560214) baseStart_6560214 baseEnd_6560214 := by
    simpa [prefixWord, tailWord_6560214, baseEnd_6560214] using wordTrace_append hprefix tailTrace_6560214
  have hstable : (prefixWord ++ tailWord_6560214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560214).length < 2 ^ (prefixWord ++ tailWord_6560214).sum := by decide
  have hdescent : baseEnd_6560214 < baseStart_6560214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560217 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_6560217 : Nat := 118140960795 + 6560217 * 2 ^ 59
def prefixEnd_6560217 : Nat := 4983230072969 + 3 ^ 40 * 6560217 * 2
def baseEnd_6560217 : Nat := 3368544518796464854517617

theorem tailTrace_6560217 : CollatzResearch.WordTrace tailWord_6560217 prefixEnd_6560217 3368544518796464854517617 := by
  unfold tailWord_6560217
  simp only [CollatzResearch.WordTrace]
  refine ⟨239270770874461679709438905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159513847249641119806292603 239270770874461679709438905)
  ·
    refine ⟨179453078155846259782079179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239270770874461679709438905 179453078155846259782079179)
    ·
      refine ⟨269179617233769389673118769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179453078155846259782079179 269179617233769389673118769)
      ·
        refine ⟨201884712925327042254839077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269179617233769389673118769 201884712925327042254839077)
        ·
          refine ⟨37853383673498820422782327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201884712925327042254839077 37853383673498820422782327)
          ·
            refine ⟨56780075510248230634173491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37853383673498820422782327 56780075510248230634173491)
            ·
              refine ⟨85170113265372345951260237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56780075510248230634173491 85170113265372345951260237)
              ·
                refine ⟨31938792474514629731722589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85170113265372345951260237 31938792474514629731722589)
                ·
                  refine ⟨11977047177942986149395971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31938792474514629731722589 11977047177942986149395971)
                  ·
                    refine ⟨17965570766914479224093957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11977047177942986149395971 17965570766914479224093957)
                    ·
                      refine ⟨3368544518796464854517617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17965570766914479224093957 3368544518796464854517617)
                      ·
                        rfl

theorem cell23_6560217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_6560217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560217 prefixEnd_6560217 := by exact prefixLift 6560217
  have htrace : WordTrace (prefixWord ++ tailWord_6560217) baseStart_6560217 baseEnd_6560217 := by
    simpa [prefixWord, tailWord_6560217, baseEnd_6560217] using wordTrace_append hprefix tailTrace_6560217
  have hstable : (prefixWord ++ tailWord_6560217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560217).length < 2 ^ (prefixWord ++ tailWord_6560217).sum := by decide
  have hdescent : baseEnd_6560217 < baseStart_6560217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560240 : List Nat := [2, 1, 1, 1, 3, 3, 12]
def baseStart_6560240 : Nat := 118140960795 + 6560240 * 2 ^ 59
def prefixEnd_6560240 : Nat := 4983230072969 + 3 ^ 40 * 6560240 * 2
def baseEnd_6560240 : Nat := 41587115171006398327531

theorem tailTrace_6560240 : CollatzResearch.WordTrace tailWord_6560240 prefixEnd_6560240 41587115171006398327531 := by
  unfold tailWord_6560240
  simp only [CollatzResearch.WordTrace]
  refine ⟨119635804876689177318763087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159514406502252236425017449 119635804876689177318763087)
  ·
    refine ⟨179453707315033765978144631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119635804876689177318763087 179453707315033765978144631)
    ·
      refine ⟨269180560972550648967216947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179453707315033765978144631 269180560972550648967216947)
      ·
        refine ⟨403770841458825973450825421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269180560972550648967216947 403770841458825973450825421)
        ·
          refine ⟨151414065547059740044059533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403770841458825973450825421 151414065547059740044059533)
          ·
            refine ⟨56780274580147402516522325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151414065547059740044059533 56780274580147402516522325)
            ·
              refine ⟨41587115171006398327531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 56780274580147402516522325 41587115171006398327531)
              ·
                rfl

theorem cell23_6560240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 12].length) (baseStart_6560240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560240 prefixEnd_6560240 := by exact prefixLift 6560240
  have htrace : WordTrace (prefixWord ++ tailWord_6560240) baseStart_6560240 baseEnd_6560240 := by
    simpa [prefixWord, tailWord_6560240, baseEnd_6560240] using wordTrace_append hprefix tailTrace_6560240
  have hstable : (prefixWord ++ tailWord_6560240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560240).length < 2 ^ (prefixWord ++ tailWord_6560240).sum := by decide
  have hdescent : baseEnd_6560240 < baseStart_6560240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560285 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_6560285 : Nat := 118140960795 + 6560285 * 2 ^ 59
def prefixEnd_6560285 : Nat := 4983230072969 + 3 ^ 40 * 6560285 * 2
def baseEnd_6560285 : Nat := 3368579435480970588467305

theorem tailTrace_6560285 : CollatzResearch.WordTrace tailWord_6560285 prefixEnd_6560285 3368579435480970588467305 := by
  unfold tailWord_6560285
  simp only [CollatzResearch.WordTrace]
  refine ⟨239273251038215327322914309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159515500692143551548609539 239273251038215327322914309)
  ·
    refine ⟨44863734569665373873046433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239273251038215327322914309 44863734569665373873046433)
    ·
      refine ⟨33647800927249030404784825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44863734569665373873046433 33647800927249030404784825)
      ·
        refine ⟨25235850695436772803588619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33647800927249030404784825 25235850695436772803588619)
        ·
          refine ⟨37853776043155159205382929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25235850695436772803588619 37853776043155159205382929)
          ·
            refine ⟨28390332032366369404037197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37853776043155159205382929 28390332032366369404037197)
            ·
              refine ⟨10646374512137388526513949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28390332032366369404037197 10646374512137388526513949)
              ·
                refine ⟨3992390442051520697442731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10646374512137388526513949 3992390442051520697442731)
                ·
                  refine ⟨5988585663077281046164097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992390442051520697442731 5988585663077281046164097)
                  ·
                    refine ⟨4491439247307960784623073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988585663077281046164097 4491439247307960784623073)
                    ·
                      refine ⟨3368579435480970588467305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491439247307960784623073 3368579435480970588467305)
                      ·
                        rfl

theorem cell23_6560285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_6560285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560285 prefixEnd_6560285 := by exact prefixLift 6560285
  have htrace : WordTrace (prefixWord ++ tailWord_6560285) baseStart_6560285 baseEnd_6560285 := by
    simpa [prefixWord, tailWord_6560285, baseEnd_6560285] using wordTrace_append hprefix tailTrace_6560285
  have hstable : (prefixWord ++ tailWord_6560285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560285).length < 2 ^ (prefixWord ++ tailWord_6560285).sum := by decide
  have hdescent : baseEnd_6560285 < baseStart_6560285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560302 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6560302 : Nat := 118140960795 + 6560302 * 2 ^ 59
def prefixEnd_6560302 : Nat := 4983230072969 + 3 ^ 40 * 6560302 * 2
def baseEnd_6560302 : Nat := 3368588164652097021954727

theorem tailTrace_6560302 : CollatzResearch.WordTrace tailWord_6560302 prefixEnd_6560302 3368588164652097021954727 := by
  unfold tailWord_6560302
  simp only [CollatzResearch.WordTrace]
  refine ⟨29909233884894217403285395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159515914052769159484188773 29909233884894217403285395)
  ·
    refine ⟨44863850827341326104928093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29909233884894217403285395 44863850827341326104928093)
    ·
      refine ⟨16823944060252997289348035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44863850827341326104928093 16823944060252997289348035)
      ·
        refine ⟨25235916090379495934022053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823944060252997289348035 25235916090379495934022053)
        ·
          refine ⟨4731734266946155487629135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25235916090379495934022053 4731734266946155487629135)
          ·
            refine ⟨7097601400419233231443703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731734266946155487629135 7097601400419233231443703)
            ·
              refine ⟨10646402100628849847165555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097601400419233231443703 10646402100628849847165555)
              ·
                refine ⟨15969603150943274770748333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646402100628849847165555 15969603150943274770748333)
                ·
                  refine ⟨5988601181603728039030625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15969603150943274770748333 5988601181603728039030625)
                  ·
                    refine ⟨4491450886202796029272969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988601181603728039030625 4491450886202796029272969)
                    ·
                      refine ⟨3368588164652097021954727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491450886202796029272969 3368588164652097021954727)
                      ·
                        rfl

theorem cell23_6560302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6560302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560302 prefixEnd_6560302 := by exact prefixLift 6560302
  have htrace : WordTrace (prefixWord ++ tailWord_6560302) baseStart_6560302 baseEnd_6560302 := by
    simpa [prefixWord, tailWord_6560302, baseEnd_6560302] using wordTrace_append hprefix tailTrace_6560302
  have hstable : (prefixWord ++ tailWord_6560302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560302).length < 2 ^ (prefixWord ++ tailWord_6560302).sum := by decide
  have hdescent : baseEnd_6560302 < baseStart_6560302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560307 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_6560307 : Nat := 118140960795 + 6560307 * 2 ^ 59
def prefixEnd_6560307 : Nat := 4983230072969 + 3 ^ 40 * 6560307 * 2
def baseEnd_6560307 : Nat := 3368590732055369502392203

theorem tailTrace_6560307 : CollatzResearch.WordTrace tailWord_6560307 prefixEnd_6560307 3368590732055369502392203 := by
  unfold tailWord_6560307
  simp only [CollatzResearch.WordTrace]
  refine ⟨239274053444135625080215175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159516035629423750053476783 239274053444135625080215175)
  ·
    refine ⟨358911080166203437620322763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239274053444135625080215175 358911080166203437620322763)
    ·
      refine ⟨538366620249305156430484145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358911080166203437620322763 538366620249305156430484145)
      ·
        refine ⟨403774965186978867322863109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538366620249305156430484145 403774965186978867322863109)
        ·
          refine ⟨75707805972558537623036833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403774965186978867322863109 75707805972558537623036833)
          ·
            refine ⟨56780854479418903217277625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75707805972558537623036833 56780854479418903217277625)
            ·
              refine ⟨42585640859564177412958219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56780854479418903217277625 42585640859564177412958219)
              ·
                refine ⟨63878461289346266119437329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42585640859564177412958219 63878461289346266119437329)
                ·
                  refine ⟨47908845967009699589577997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63878461289346266119437329 47908845967009699589577997)
                  ·
                    refine ⟨17965817237628637346091749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47908845967009699589577997 17965817237628637346091749)
                    ·
                      refine ⟨3368590732055369502392203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17965817237628637346091749 3368590732055369502392203)
                      ·
                        rfl

theorem cell23_6560307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_6560307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560307 prefixEnd_6560307 := by exact prefixLift 6560307
  have htrace : WordTrace (prefixWord ++ tailWord_6560307) baseStart_6560307 baseEnd_6560307 := by
    simpa [prefixWord, tailWord_6560307, baseEnd_6560307] using wordTrace_append hprefix tailTrace_6560307
  have hstable : (prefixWord ++ tailWord_6560307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560307).length < 2 ^ (prefixWord ++ tailWord_6560307).sum := by decide
  have hdescent : baseEnd_6560307 < baseStart_6560307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560341 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_6560341 : Nat := 118140960795 + 6560341 * 2 ^ 59
def prefixEnd_6560341 : Nat := 4983230072969 + 3 ^ 40 * 6560341 * 2
def baseEnd_6560341 : Nat := 3368608190397622369367047

theorem tailTrace_6560341 : CollatzResearch.WordTrace tailWord_6560341 prefixEnd_6560341 3368608190397622369367047 := by
  unfold tailWord_6560341
  simp only [CollatzResearch.WordTrace]
  refine ⟨239275293526012448886952877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159516862350674965924635251 239275293526012448886952877)
  ·
    refine ⟨89728235072254668332607329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239275293526012448886952877 89728235072254668332607329)
    ·
      refine ⟨67296176304191001249455497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89728235072254668332607329 67296176304191001249455497)
      ·
        refine ⟨50472132228143250937091623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67296176304191001249455497 50472132228143250937091623)
        ·
          refine ⟨75708198342214876405637435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50472132228143250937091623 75708198342214876405637435)
          ·
            refine ⟨113562297513322314608456153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75708198342214876405637435 113562297513322314608456153)
            ·
              refine ⟨85171723134991735956342115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113562297513322314608456153 85171723134991735956342115)
              ·
                refine ⟨127757584702487603934513173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85171723134991735956342115 127757584702487603934513173)
                ·
                  refine ⟨5988636782929106434430305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127757584702487603934513173 5988636782929106434430305)
                  ·
                    refine ⟨4491477587196829825822729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988636782929106434430305 4491477587196829825822729)
                    ·
                      refine ⟨3368608190397622369367047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491477587196829825822729 3368608190397622369367047)
                      ·
                        rfl

theorem cell23_6560341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_6560341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560341 prefixEnd_6560341 := by exact prefixLift 6560341
  have htrace : WordTrace (prefixWord ++ tailWord_6560341) baseStart_6560341 baseEnd_6560341 := by
    simpa [prefixWord, tailWord_6560341, baseEnd_6560341] using wordTrace_append hprefix tailTrace_6560341
  have hstable : (prefixWord ++ tailWord_6560341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560341).length < 2 ^ (prefixWord ++ tailWord_6560341).sum := by decide
  have hdescent : baseEnd_6560341 < baseStart_6560341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560387 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_6560387 : Nat := 118140960795 + 6560387 * 2 ^ 59
def prefixEnd_6560387 : Nat := 4983230072969 + 3 ^ 40 * 6560387 * 2
def baseEnd_6560387 : Nat := 3368631810507729189391835

theorem tailTrace_6560387 : CollatzResearch.WordTrace tailWord_6560387 prefixEnd_6560387 3368631810507729189391835 := by
  unfold tailWord_6560387
  simp only [CollatzResearch.WordTrace]
  refine ⟨239276971283845798743127415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159517980855897199162084943 239276971283845798743127415)
  ·
    refine ⟨358915456925768698114691123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239276971283845798743127415 358915456925768698114691123)
    ·
      refine ⟨538373185388653047172036685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358915456925768698114691123 538373185388653047172036685)
      ·
        refine ⟨201889944520744892689513757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538373185388653047172036685 201889944520744892689513757)
        ·
          refine ⟨75708729195279334758567659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201889944520744892689513757 75708729195279334758567659)
          ·
            refine ⟨113563093792919002137851489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75708729195279334758567659 113563093792919002137851489)
            ·
              refine ⟨85172320344689251603388617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113563093792919002137851489 85172320344689251603388617)
              ·
                refine ⟨63879240258516938702541463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85172320344689251603388617 63879240258516938702541463)
                ·
                  refine ⟨95818860387775408053812195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63879240258516938702541463 95818860387775408053812195)
                  ·
                    refine ⟨143728290581663112080718293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95818860387775408053812195 143728290581663112080718293)
                    ·
                      refine ⟨3368631810507729189391835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143728290581663112080718293 3368631810507729189391835)
                      ·
                        rfl

theorem cell23_6560387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_6560387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560387 prefixEnd_6560387 := by exact prefixLift 6560387
  have htrace : WordTrace (prefixWord ++ tailWord_6560387) baseStart_6560387 baseEnd_6560387 := by
    simpa [prefixWord, tailWord_6560387, baseEnd_6560387] using wordTrace_append hprefix tailTrace_6560387
  have hstable : (prefixWord ++ tailWord_6560387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560387).length < 2 ^ (prefixWord ++ tailWord_6560387).sum := by decide
  have hdescent : baseEnd_6560387 < baseStart_6560387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560431 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 2, 4, 2]
def baseStart_6560431 : Nat := 118140960795 + 6560431 * 2 ^ 59
def prefixEnd_6560431 : Nat := 4983230072969 + 3 ^ 40 * 6560431 * 2
def baseEnd_6560431 : Nat := 3368654403656527017241633

theorem tailTrace_6560431 : CollatzResearch.WordTrace tailWord_6560431 prefixEnd_6560431 3368654403656527017241633 := by
  unfold tailWord_6560431
  simp only [CollatzResearch.WordTrace]
  refine ⟨239278576095686394257729147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159519050730457596171819431 239278576095686394257729147)
  ·
    refine ⟨358917864143529591386593721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239278576095686394257729147 358917864143529591386593721)
    ·
      refine ⟨269188398107647193539945291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358917864143529591386593721 269188398107647193539945291)
      ·
        refine ⟨403782597161470790309917937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269188398107647193539945291 403782597161470790309917937)
        ·
          refine ⟨302836947871103092732438453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403782597161470790309917937 302836947871103092732438453)
          ·
            refine ⟨28390963862915914943666105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302836947871103092732438453 28390963862915914943666105)
            ·
              refine ⟨21293222897186936207749579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28390963862915914943666105 21293222897186936207749579)
              ·
                refine ⟨31939834345780404311624369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21293222897186936207749579 31939834345780404311624369)
                ·
                  refine ⟨23954875759335303233718277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31939834345780404311624369 23954875759335303233718277)
                  ·
                    refine ⟨4491539204875369356322177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23954875759335303233718277 4491539204875369356322177)
                    ·
                      refine ⟨3368654403656527017241633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491539204875369356322177 3368654403656527017241633)
                      ·
                        rfl

theorem cell23_6560431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4, 2].length) (baseStart_6560431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560431 prefixEnd_6560431 := by exact prefixLift 6560431
  have htrace : WordTrace (prefixWord ++ tailWord_6560431) baseStart_6560431 baseEnd_6560431 := by
    simpa [prefixWord, tailWord_6560431, baseEnd_6560431] using wordTrace_append hprefix tailTrace_6560431
  have hstable : (prefixWord ++ tailWord_6560431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560431).length < 2 ^ (prefixWord ++ tailWord_6560431).sum := by decide
  have hdescent : baseEnd_6560431 < baseStart_6560431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560444 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6560444 : Nat := 118140960795 + 6560444 * 2 ^ 59
def prefixEnd_6560444 : Nat := 4983230072969 + 3 ^ 40 * 6560444 * 2
def baseEnd_6560444 : Nat := 3368661078905035466379073

theorem tailTrace_6560444 : CollatzResearch.WordTrace tailWord_6560444 prefixEnd_6560444 3368661078905035466379073 := by
  unfold tailWord_6560444
  simp only [CollatzResearch.WordTrace]
  refine ⟨119639525122319648738976193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159519366829759531651968257 119639525122319648738976193)
  ·
    refine ⟨89729643841739736554232145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119639525122319648738976193 89729643841739736554232145)
    ·
      refine ⟨67297232881304802415674109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89729643841739736554232145 67297232881304802415674109)
      ·
        refine ⟨25236462330489300905877791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67297232881304802415674109 25236462330489300905877791)
        ·
          refine ⟨37854693495733951358816687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25236462330489300905877791 37854693495733951358816687)
          ·
            refine ⟨56782040243600927038225031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37854693495733951358816687 56782040243600927038225031)
            ·
              refine ⟨85173060365401390557337547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56782040243600927038225031 85173060365401390557337547)
              ·
                refine ⟨127759590548102085836006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85173060365401390557337547 127759590548102085836006321)
                ·
                  refine ⟨95819692911076564377004741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127759590548102085836006321 95819692911076564377004741)
                  ·
                    refine ⟨17966192420826855820688389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95819692911076564377004741 17966192420826855820688389)
                    ·
                      refine ⟨3368661078905035466379073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17966192420826855820688389 3368661078905035466379073)
                      ·
                        rfl

theorem cell23_6560444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6560444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560444 prefixEnd_6560444 := by exact prefixLift 6560444
  have htrace : WordTrace (prefixWord ++ tailWord_6560444) baseStart_6560444 baseEnd_6560444 := by
    simpa [prefixWord, tailWord_6560444, baseEnd_6560444] using wordTrace_append hprefix tailTrace_6560444
  have hstable : (prefixWord ++ tailWord_6560444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560444).length < 2 ^ (prefixWord ++ tailWord_6560444).sum := by decide
  have hdescent : baseEnd_6560444 < baseStart_6560444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560491 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 6, 3, 2]
def baseStart_6560491 : Nat := 118140960795 + 6560491 * 2 ^ 59
def prefixEnd_6560491 : Nat := 4983230072969 + 3 ^ 40 * 6560491 * 2
def baseEnd_6560491 : Nat := 3368685212495796782491357

theorem tailTrace_6560491 : CollatzResearch.WordTrace tailWord_6560491 prefixEnd_6560491 3368685212495796782491357 := by
  unfold tailWord_6560491
  simp only [CollatzResearch.WordTrace]
  refine ⟨239280764475469024504913327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159520509650312683003275551 239280764475469024504913327)
  ·
    refine ⟨358921146713203536757369991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239280764475469024504913327 358921146713203536757369991)
    ·
      refine ⟨538381720069805305136054987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358921146713203536757369991 538381720069805305136054987)
      ·
        refine ⟨807572580104707957704082481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538381720069805305136054987 807572580104707957704082481)
        ·
          refine ⟨605679435078530968278061861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807572580104707957704082481 605679435078530968278061861)
          ·
            refine ⟨113564894077224556552136599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 605679435078530968278061861 113564894077224556552136599)
            ·
              refine ⟨170347341115836834828204899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113564894077224556552136599 170347341115836834828204899)
              ·
                refine ⟨255521011673755252242307349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170347341115836834828204899 255521011673755252242307349)
                ·
                  refine ⟨11977547422207277448858157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255521011673755252242307349 11977547422207277448858157)
                  ·
                    refine ⟨4491580283327729043321809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11977547422207277448858157 4491580283327729043321809)
                    ·
                      refine ⟨3368685212495796782491357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491580283327729043321809 3368685212495796782491357)
                      ·
                        rfl

theorem cell23_6560491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3, 2].length) (baseStart_6560491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560491 prefixEnd_6560491 := by exact prefixLift 6560491
  have htrace : WordTrace (prefixWord ++ tailWord_6560491) baseStart_6560491 baseEnd_6560491 := by
    simpa [prefixWord, tailWord_6560491, baseEnd_6560491] using wordTrace_append hprefix tailTrace_6560491
  have hstable : (prefixWord ++ tailWord_6560491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560491).length < 2 ^ (prefixWord ++ tailWord_6560491).sum := by decide
  have hdescent : baseEnd_6560491 < baseStart_6560491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560508 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_6560508 : Nat := 118140960795 + 6560508 * 2 ^ 59
def prefixEnd_6560508 : Nat := 4983230072969 + 3 ^ 40 * 6560508 * 2
def baseEnd_6560508 : Nat := 3368693941666923215978779

theorem tailTrace_6560508 : CollatzResearch.WordTrace tailWord_6560508 prefixEnd_6560508 3368693941666923215978779 := by
  unfold tailWord_6560508
  simp only [CollatzResearch.WordTrace]
  refine ⟨119640692258203718204141089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159520923010938290938854785 119640692258203718204141089)
  ·
    refine ⟨89730519193652788653105817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119640692258203718204141089 89730519193652788653105817)
    ·
      refine ⟨67297889395239591489829363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89730519193652788653105817 67297889395239591489829363)
      ·
        refine ⟨100946834092859387234744045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67297889395239591489829363 100946834092859387234744045)
        ·
          refine ⟨37855062784822270213029017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100946834092859387234744045 37855062784822270213029017)
          ·
            refine ⟨28391297088616702659771763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37855062784822270213029017 28391297088616702659771763)
            ·
              refine ⟨42586945632925053989657645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28391297088616702659771763 42586945632925053989657645)
              ·
                refine ⟨15970104612346895246121617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42586945632925053989657645 15970104612346895246121617)
                ·
                  refine ⟨11977578459260171434591213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15970104612346895246121617 11977578459260171434591213)
                  ·
                    refine ⟨4491591922222564287971705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11977578459260171434591213 4491591922222564287971705)
                    ·
                      refine ⟨3368693941666923215978779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491591922222564287971705 3368693941666923215978779)
                      ·
                        rfl

theorem cell23_6560508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_6560508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560508 prefixEnd_6560508 := by exact prefixLift 6560508
  have htrace : WordTrace (prefixWord ++ tailWord_6560508) baseStart_6560508 baseEnd_6560508 := by
    simpa [prefixWord, tailWord_6560508, baseEnd_6560508] using wordTrace_append hprefix tailTrace_6560508
  have hstable : (prefixWord ++ tailWord_6560508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560508).length < 2 ^ (prefixWord ++ tailWord_6560508).sum := by decide
  have hdescent : baseEnd_6560508 < baseStart_6560508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560521 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_6560521 : Nat := 118140960795 + 6560521 * 2 ^ 59
def prefixEnd_6560521 : Nat := 4983230072969 + 3 ^ 40 * 6560521 * 2
def baseEnd_6560521 : Nat := 3368700616915431665116219

theorem tailTrace_6560521 : CollatzResearch.WordTrace tailWord_6560521 prefixEnd_6560521 3368700616915431665116219 := by
  unfold tailWord_6560521
  simp only [CollatzResearch.WordTrace]
  refine ⟨239281858665360339628505417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159521239110240226419003611 239281858665360339628505417)
  ·
    refine ⟨179461393999020254721379063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239281858665360339628505417 179461393999020254721379063)
    ·
      refine ⟨269192090998530382082068595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179461393999020254721379063 269192090998530382082068595)
      ·
        refine ⟨403788136497795573123102893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269192090998530382082068595 403788136497795573123102893)
        ·
          refine ⟨151420551186673339921163585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403788136497795573123102893 151420551186673339921163585)
          ·
            refine ⟨113565413390005004940872689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151420551186673339921163585 113565413390005004940872689)
            ·
              refine ⟨85174060042503753705654517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113565413390005004940872689 85174060042503753705654517)
              ·
                refine ⟨7985068128984726909905111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85174060042503753705654517 7985068128984726909905111)
                ·
                  refine ⟨11977602193477090364857667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985068128984726909905111 11977602193477090364857667)
                  ·
                    refine ⟨17966403290215635547286501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11977602193477090364857667 17966403290215635547286501)
                    ·
                      refine ⟨3368700616915431665116219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17966403290215635547286501 3368700616915431665116219)
                      ·
                        rfl

theorem cell23_6560521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_6560521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560521 prefixEnd_6560521 := by exact prefixLift 6560521
  have htrace : WordTrace (prefixWord ++ tailWord_6560521) baseStart_6560521 baseEnd_6560521 := by
    simpa [prefixWord, tailWord_6560521, baseEnd_6560521] using wordTrace_append hprefix tailTrace_6560521
  have hstable : (prefixWord ++ tailWord_6560521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560521).length < 2 ^ (prefixWord ++ tailWord_6560521).sum := by decide
  have hdescent : baseEnd_6560521 < baseStart_6560521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560548 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_6560548 : Nat := 118140960795 + 6560548 * 2 ^ 59
def prefixEnd_6560548 : Nat := 4983230072969 + 3 ^ 40 * 6560548 * 2
def baseEnd_6560548 : Nat := 1122904826964367686492865

theorem tailTrace_6560548 : CollatzResearch.WordTrace tailWord_6560548 prefixEnd_6560548 1122904826964367686492865 := by
  unfold tailWord_6560548
  simp only [CollatzResearch.WordTrace]
  refine ⟨119641421718131261619869149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159521895624175015493158865 119641421718131261619869149)
  ·
    refine ⟨44865533144299223107450931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119641421718131261619869149 44865533144299223107450931)
    ·
      refine ⟨67298299716448834661176397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44865533144299223107450931 67298299716448834661176397)
      ·
        refine ⟨25236862393668312997941149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67298299716448834661176397 25236862393668312997941149)
        ·
          refine ⟨9463823397625617374227931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25236862393668312997941149 9463823397625617374227931)
          ·
            refine ⟨14195735096438426061341897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463823397625617374227931 14195735096438426061341897)
            ·
              refine ⟨10646801322328819546006423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14195735096438426061341897 10646801322328819546006423)
              ·
                refine ⟨15970201983493229319009635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646801322328819546006423 15970201983493229319009635)
                ·
                  refine ⟨23955302975239843978514453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15970201983493229319009635 23955302975239843978514453)
                  ·
                    refine ⟨1122904826964367686492865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23955302975239843978514453 1122904826964367686492865)
                    ·
                      rfl

theorem cell23_6560548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_6560548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560548 prefixEnd_6560548 := by exact prefixLift 6560548
  have htrace : WordTrace (prefixWord ++ tailWord_6560548) baseStart_6560548 baseEnd_6560548 := by
    simpa [prefixWord, tailWord_6560548, baseEnd_6560548] using wordTrace_append hprefix tailTrace_6560548
  have hstable : (prefixWord ++ tailWord_6560548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560548).length < 2 ^ (prefixWord ++ tailWord_6560548).sum := by decide
  have hdescent : baseEnd_6560548 < baseStart_6560548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560561 : List Nat := [1, 2, 2, 3, 2, 1, 5, 7]
def baseStart_6560561 : Nat := 118140960795 + 6560561 * 2 ^ 59
def prefixEnd_6560561 : Nat := 4983230072969 + 3 ^ 40 * 6560561 * 2
def baseEnd_6560561 : Nat := 124767450227467092911705

theorem tailTrace_6560561 : CollatzResearch.WordTrace tailWord_6560561 prefixEnd_6560561 124767450227467092911705 := by
  unfold tailWord_6560561
  simp only [CollatzResearch.WordTrace]
  refine ⟨239283317585215426459961537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159522211723476950973307691 239283317585215426459961537)
  ·
    refine ⟨179462488188911569844971153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239283317585215426459961537 179462488188911569844971153)
    ·
      refine ⟨134596866141683677383728365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179462488188911569844971153 134596866141683677383728365)
      ·
        refine ⟨50473824803131379018898137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134596866141683677383728365 50473824803131379018898137)
        ·
          refine ⟨37855368602348534264173603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50473824803131379018898137 37855368602348534264173603)
          ·
            refine ⟨56783052903522801396260405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37855368602348534264173603 56783052903522801396260405)
            ·
              refine ⟨5323411209705262630899413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56783052903522801396260405 5323411209705262630899413)
              ·
                refine ⟨124767450227467092911705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5323411209705262630899413 124767450227467092911705)
                ·
                  rfl

theorem cell23_6560561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 7].length) (baseStart_6560561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560561 prefixEnd_6560561 := by exact prefixLift 6560561
  have htrace : WordTrace (prefixWord ++ tailWord_6560561) baseStart_6560561 baseEnd_6560561 := by
    simpa [prefixWord, tailWord_6560561, baseEnd_6560561] using wordTrace_append hprefix tailTrace_6560561
  have hstable : (prefixWord ++ tailWord_6560561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560561).length < 2 ^ (prefixWord ++ tailWord_6560561).sum := by decide
  have hdescent : baseEnd_6560561 < baseStart_6560561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560575 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 1, 2, 3]
def baseStart_6560575 : Nat := 118140960795 + 6560575 * 2 ^ 59
def prefixEnd_6560575 : Nat := 4983230072969 + 3 ^ 40 * 6560575 * 2
def baseEnd_6560575 : Nat := 3368728344870774453840971

theorem tailTrace_6560575 : CollatzResearch.WordTrace tailWord_6560575 prefixEnd_6560575 3368728344870774453840971 := by
  unfold tailWord_6560575
  simp only [CollatzResearch.WordTrace]
  refine ⟨239283828207164706850971179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159522552138109804567314119 239283828207164706850971179)
  ·
    refine ⟨358925742310747060276456769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239283828207164706850971179 358925742310747060276456769)
    ·
      refine ⟨269194306733060295207342577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358925742310747060276456769 269194306733060295207342577)
      ·
        refine ⟨201895730049795221405506933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269194306733060295207342577 201895730049795221405506933)
        ·
          refine ⟨18927724692168302006766275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201895730049795221405506933 18927724692168302006766275)
          ·
            refine ⟨28391587038252453010149413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18927724692168302006766275 28391587038252453010149413)
            ·
              refine ⟨5323422569672334939403015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28391587038252453010149413 5323422569672334939403015)
              ·
                refine ⟨7985133854508502409104523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323422569672334939403015 7985133854508502409104523)
                ·
                  refine ⟨11977700781762753613656785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985133854508502409104523 11977700781762753613656785)
                  ·
                    refine ⟨8983275586322065210242589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11977700781762753613656785 8983275586322065210242589)
                    ·
                      refine ⟨3368728344870774453840971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8983275586322065210242589 3368728344870774453840971)
                      ·
                        rfl

theorem cell23_6560575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_6560575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560575 prefixEnd_6560575 := by exact prefixLift 6560575
  have htrace : WordTrace (prefixWord ++ tailWord_6560575) baseStart_6560575 baseEnd_6560575 := by
    simpa [prefixWord, tailWord_6560575, baseEnd_6560575] using wordTrace_append hprefix tailTrace_6560575
  have hstable : (prefixWord ++ tailWord_6560575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560575).length < 2 ^ (prefixWord ++ tailWord_6560575).sum := by decide
  have hdescent : baseEnd_6560575 < baseStart_6560575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560582 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_6560582 : Nat := 118140960795 + 6560582 * 2 ^ 59
def prefixEnd_6560582 : Nat := 4983230072969 + 3 ^ 40 * 6560582 * 2
def baseEnd_6560582 : Nat := 1122910646411785308817813

theorem tailTrace_6560582 : CollatzResearch.WordTrace tailWord_6560582 prefixEnd_6560582 1122910646411785308817813 := by
  unfold tailWord_6560582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477627609941854595202375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159522722345426231364317333 7477627609941854595202375)
  ·
    refine ⟨11216441414912781892803563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7477627609941854595202375 11216441414912781892803563)
    ·
      refine ⟨16824662122369172839205345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216441414912781892803563 16824662122369172839205345)
      ·
        refine ⟨12618496591776879629404009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16824662122369172839205345 12618496591776879629404009)
        ·
          refine ⟨9463872443832659722053007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12618496591776879629404009 9463872443832659722053007)
          ·
            refine ⟨14195808665748989583079511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463872443832659722053007 14195808665748989583079511)
            ·
              refine ⟨21293712998623484374619267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14195808665748989583079511 21293712998623484374619267)
              ·
                refine ⟨31940569497935226561928901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21293712998623484374619267 31940569497935226561928901)
                ·
                  refine ⟨5988856780862854980361669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31940569497935226561928901 5988856780862854980361669)
                  ·
                    refine ⟨1122910646411785308817813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5988856780862854980361669 1122910646411785308817813)
                    ·
                      rfl

theorem cell23_6560582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_6560582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560582 prefixEnd_6560582 := by exact prefixLift 6560582
  have htrace : WordTrace (prefixWord ++ tailWord_6560582) baseStart_6560582 baseEnd_6560582 := by
    simpa [prefixWord, tailWord_6560582, baseEnd_6560582] using wordTrace_append hprefix tailTrace_6560582
  have hstable : (prefixWord ++ tailWord_6560582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560582).length < 2 ^ (prefixWord ++ tailWord_6560582).sum := by decide
  have hdescent : baseEnd_6560582 < baseStart_6560582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560589 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6560589 : Nat := 118140960795 + 6560589 * 2 ^ 59
def prefixEnd_6560589 : Nat := 4983230072969 + 3 ^ 40 * 6560589 * 2
def baseEnd_6560589 : Nat := 3368735533599937399065907

theorem tailTrace_6560589 : CollatzResearch.WordTrace tailWord_6560589 prefixEnd_6560589 3368735533599937399065907 := by
  unfold tailWord_6560589
  simp only [CollatzResearch.WordTrace]
  refine ⟨239284338829113987241980821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159522892552742658161320547 239284338829113987241980821)
  ·
    refine ⟨11216453382614718151967851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239284338829113987241980821 11216453382614718151967851)
    ·
      refine ⟨16824680073922077227951777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216453382614718151967851 16824680073922077227951777)
      ·
        refine ⟨12618510055441557920963833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16824680073922077227951777 12618510055441557920963833)
        ·
          refine ⟨9463882541581168440722875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12618510055441557920963833 9463882541581168440722875)
          ·
            refine ⟨14195823812371752661084313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463882541581168440722875 14195823812371752661084313)
            ·
              refine ⟨10646867859278814495813235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14195823812371752661084313 10646867859278814495813235)
              ·
                refine ⟨15970301788918221743719853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646867859278814495813235 15970301788918221743719853)
                ·
                  refine ⟨5988863170844333153894945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15970301788918221743719853 5988863170844333153894945)
                  ·
                    refine ⟨4491647378133249865421209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988863170844333153894945 4491647378133249865421209)
                    ·
                      refine ⟨3368735533599937399065907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491647378133249865421209 3368735533599937399065907)
                      ·
                        rfl

theorem cell23_6560589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6560589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560589 prefixEnd_6560589 := by exact prefixLift 6560589
  have htrace : WordTrace (prefixWord ++ tailWord_6560589) baseStart_6560589 baseEnd_6560589 := by
    simpa [prefixWord, tailWord_6560589, baseEnd_6560589] using wordTrace_append hprefix tailTrace_6560589
  have hstable : (prefixWord ++ tailWord_6560589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560589).length < 2 ^ (prefixWord ++ tailWord_6560589).sum := by decide
  have hdescent : baseEnd_6560589 < baseStart_6560589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560615 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_6560615 : Nat := 118140960795 + 6560615 * 2 ^ 59
def prefixEnd_6560615 : Nat := 4983230072969 + 3 ^ 40 * 6560615 * 2
def baseEnd_6560615 : Nat := 3368748884096954297340787

theorem tailTrace_6560615 : CollatzResearch.WordTrace tailWord_6560615 prefixEnd_6560615 3368748884096954297340787 := by
  unfold tailWord_6560615
  simp only [CollatzResearch.WordTrace]
  refine ⟨239285287127019793682427299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159523524751346529121618199 239285287127019793682427299)
  ·
    refine ⟨358927930690529690523640949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239285287127019793682427299 358927930690529690523640949)
    ·
      refine ⟨33649493502237158486591339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 358927930690529690523640949 33649493502237158486591339)
      ·
        refine ⟨50474240253355737729887009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33649493502237158486591339 50474240253355737729887009)
        ·
          refine ⟨37855680190016803297415257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50474240253355737729887009 37855680190016803297415257)
          ·
            refine ⟨28391760142512602473061443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37855680190016803297415257 28391760142512602473061443)
            ·
              refine ⟨42587640213768903709592165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28391760142512602473061443 42587640213768903709592165)
              ·
                refine ⟨7985182540081669445548531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42587640213768903709592165 7985182540081669445548531)
                ·
                  refine ⟨11977773810122504168322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985182540081669445548531 11977773810122504168322797)
                  ·
                    refine ⟨4491665178795939063121049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11977773810122504168322797 4491665178795939063121049)
                    ·
                      refine ⟨3368748884096954297340787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491665178795939063121049 3368748884096954297340787)
                      ·
                        rfl

theorem cell23_6560615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_6560615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560615 prefixEnd_6560615 := by exact prefixLift 6560615
  have htrace : WordTrace (prefixWord ++ tailWord_6560615) baseStart_6560615 baseEnd_6560615 := by
    simpa [prefixWord, tailWord_6560615, baseEnd_6560615] using wordTrace_append hprefix tailTrace_6560615
  have hstable : (prefixWord ++ tailWord_6560615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560615).length < 2 ^ (prefixWord ++ tailWord_6560615).sum := by decide
  have hdescent : baseEnd_6560615 < baseStart_6560615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560645 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_6560645 : Nat := 118140960795 + 6560645 * 2 ^ 59
def prefixEnd_6560645 : Nat := 4983230072969 + 3 ^ 40 * 6560645 * 2
def baseEnd_6560645 : Nat := 3368764288516589179965649

theorem tailTrace_6560645 : CollatzResearch.WordTrace tailWord_6560645 prefixEnd_6560645 3368764288516589179965649 := by
  unfold tailWord_6560645
  simp only [CollatzResearch.WordTrace]
  refine ⟨239286381316911108806019389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159524254211274072537346259 239286381316911108806019389)
  ·
    refine ⟨89732392993841665802257271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239286381316911108806019389 89732392993841665802257271)
    ·
      refine ⟨134598589490762498703385907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89732392993841665802257271 134598589490762498703385907)
      ·
        refine ⟨201897884236143748055078861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134598589490762498703385907 201897884236143748055078861)
        ·
          refine ⟨75711706588553905520654573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201897884236143748055078861 75711706588553905520654573)
          ·
            refine ⟨28391889970707714570245465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75711706588553905520654573 28391889970707714570245465)
            ·
              refine ⟨21293917478030785927684099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28391889970707714570245465 21293917478030785927684099)
              ·
                refine ⟨31940876217046178891526149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21293917478030785927684099 31940876217046178891526149)
                ·
                  refine ⟨5988914290696158542161153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31940876217046178891526149 5988914290696158542161153)
                  ·
                    refine ⟨4491685718022118906620865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988914290696158542161153 4491685718022118906620865)
                    ·
                      refine ⟨3368764288516589179965649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491685718022118906620865 3368764288516589179965649)
                      ·
                        rfl

theorem cell23_6560645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_6560645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560645 prefixEnd_6560645 := by exact prefixLift 6560645
  have htrace : WordTrace (prefixWord ++ tailWord_6560645) baseStart_6560645 baseEnd_6560645 := by
    simpa [prefixWord, tailWord_6560645, baseEnd_6560645] using wordTrace_append hprefix tailTrace_6560645
  have hstable : (prefixWord ++ tailWord_6560645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560645).length < 2 ^ (prefixWord ++ tailWord_6560645).sum := by decide
  have hdescent : baseEnd_6560645 < baseStart_6560645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560651 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 7]
def baseStart_6560651 : Nat := 118140960795 + 6560651 * 2 ^ 59
def prefixEnd_6560651 : Nat := 4983230072969 + 3 ^ 40 * 6560651 * 2
def baseEnd_6560651 : Nat := 374307485488946239610069

theorem tailTrace_6560651 : CollatzResearch.WordTrace tailWord_6560651 prefixEnd_6560651 374307485488946239610069 := by
  unfold tailWord_6560651
  simp only [CollatzResearch.WordTrace]
  refine ⟨239286600154889371830737807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159524400103259581220491871 239286600154889371830737807)
  ·
    refine ⟨358929900232334057746106711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239286600154889371830737807 358929900232334057746106711)
    ·
      refine ⟨538394850348501086619160067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358929900232334057746106711 538394850348501086619160067)
      ·
        refine ⟨807592275522751629928740101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538394850348501086619160067 807592275522751629928740101)
        ·
          refine ⟨151423551660515930611638769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 807592275522751629928740101 151423551660515930611638769)
          ·
            refine ⟨113567663745386947958729077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151423551660515930611638769 113567663745386947958729077)
            ·
              refine ⟨10646968476130026371130851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113567663745386947958729077 10646968476130026371130851)
              ·
                refine ⟨15970452714195039556696277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646968476130026371130851 15970452714195039556696277)
                ·
                  refine ⟨374307485488946239610069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15970452714195039556696277 374307485488946239610069)
                  ·
                    rfl

theorem cell23_6560651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 7].length) (baseStart_6560651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560651 prefixEnd_6560651 := by exact prefixLift 6560651
  have htrace : WordTrace (prefixWord ++ tailWord_6560651) baseStart_6560651 baseEnd_6560651 := by
    simpa [prefixWord, tailWord_6560651, baseEnd_6560651] using wordTrace_append hprefix tailTrace_6560651
  have hstable : (prefixWord ++ tailWord_6560651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560651).length < 2 ^ (prefixWord ++ tailWord_6560651).sum := by decide
  have hdescent : baseEnd_6560651 < baseStart_6560651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560728 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_6560728 : Nat := 118140960795 + 6560728 * 2 ^ 59
def prefixEnd_6560728 : Nat := 4983230072969 + 3 ^ 40 * 6560728 * 2
def baseEnd_6560728 : Nat := 1122935635803637451742589

theorem tailTrace_6560728 : CollatzResearch.WordTrace tailWord_6560728 prefixEnd_6560728 1122935635803637451742589 := by
  unfold tailWord_6560728
  simp only [CollatzResearch.WordTrace]
  refine ⟨119644704287805206990645419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159526272383740275987527225 119644704287805206990645419)
  ·
    refine ⟨179467056431707810485968129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119644704287805206990645419 179467056431707810485968129)
    ·
      refine ⟨134600292323780857864476097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179467056431707810485968129 134600292323780857864476097)
      ·
        refine ⟨100950219242835643398357073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134600292323780857864476097 100950219242835643398357073)
        ·
          refine ⟨75712664432126732548767805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100950219242835643398357073 75712664432126732548767805)
          ·
            refine ⟨28392249162047524705787927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75712664432126732548767805 28392249162047524705787927)
            ·
              refine ⟨42588373743071287058681891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28392249162047524705787927 42588373743071287058681891)
              ·
                refine ⟨63882560614606930588022837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42588373743071287058681891 63882560614606930588022837)
                ·
                  refine ⟨5988990057619399742627141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63882560614606930588022837 5988990057619399742627141)
                  ·
                    refine ⟨1122935635803637451742589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5988990057619399742627141 1122935635803637451742589)
                    ·
                      rfl

theorem cell23_6560728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_6560728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560728 prefixEnd_6560728 := by exact prefixLift 6560728
  have htrace : WordTrace (prefixWord ++ tailWord_6560728) baseStart_6560728 baseEnd_6560728 := by
    simpa [prefixWord, tailWord_6560728, baseEnd_6560728] using wordTrace_append hprefix tailTrace_6560728
  have hstable : (prefixWord ++ tailWord_6560728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560728).length < 2 ^ (prefixWord ++ tailWord_6560728).sum := by decide
  have hdescent : baseEnd_6560728 < baseStart_6560728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560761 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6560761 : Nat := 118140960795 + 6560761 * 2 ^ 59
def prefixEnd_6560761 : Nat := 4983230072969 + 3 ^ 40 * 6560761 * 2
def baseEnd_6560761 : Nat := 3368823852272510726115115

theorem tailTrace_6560761 : CollatzResearch.WordTrace tailWord_6560761 prefixEnd_6560761 3368823852272510726115115 := by
  unfold tailWord_6560761
  simp only [CollatzResearch.WordTrace]
  refine ⟨239290612184490860617242137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159527074789660573744828091 239290612184490860617242137)
  ·
    refine ⟨179467959138368145462931603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239290612184490860617242137 179467959138368145462931603)
    ·
      refine ⟨269201938707552218194397405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179467959138368145462931603 269201938707552218194397405)
      ·
        refine ⟨100950727015332081822899027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269201938707552218194397405 100950727015332081822899027)
        ·
          refine ⟨151426090522998122734348541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100950727015332081822899027 151426090522998122734348541)
          ·
            refine ⟨56784783946124296025380703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151426090522998122734348541 56784783946124296025380703)
            ·
              refine ⟨85177175919186444038071055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56784783946124296025380703 85177175919186444038071055)
              ·
                refine ⟨127765763878779666057106583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85177175919186444038071055 127765763878779666057106583)
                ·
                  refine ⟨191648645818169499085659875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127765763878779666057106583 191648645818169499085659875)
                  ·
                    refine ⟨287472968727254248628489813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191648645818169499085659875 287472968727254248628489813)
                    ·
                      refine ⟨3368823852272510726115115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287472968727254248628489813 3368823852272510726115115)
                      ·
                        rfl

theorem cell23_6560761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6560761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560761 prefixEnd_6560761 := by exact prefixLift 6560761
  have htrace : WordTrace (prefixWord ++ tailWord_6560761) baseStart_6560761 baseEnd_6560761 := by
    simpa [prefixWord, tailWord_6560761, baseEnd_6560761] using wordTrace_append hprefix tailTrace_6560761
  have hstable : (prefixWord ++ tailWord_6560761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560761).length < 2 ^ (prefixWord ++ tailWord_6560761).sum := by decide
  have hdescent : baseEnd_6560761 < baseStart_6560761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560775 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 6]
def baseStart_6560775 : Nat := 118140960795 + 6560775 * 2 ^ 59
def prefixEnd_6560775 : Nat := 4983230072969 + 3 ^ 40 * 6560775 * 2
def baseEnd_6560775 : Nat := 374314560111297074593339

theorem tailTrace_6560775 : CollatzResearch.WordTrace tailWord_6560775 prefixEnd_6560775 374314560111297074593339 := by
  unfold tailWord_6560775
  simp only [CollatzResearch.WordTrace]
  refine ⟨239291122806440141008251779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159527415204293427338834519 239291122806440141008251779)
  ·
    refine ⟨358936684209660211512377669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239291122806440141008251779 358936684209660211512377669)
    ·
      refine ⟨67300628289311289658570813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358936684209660211512377669 67300628289311289658570813)
      ·
        refine ⟨25237735608491733621964055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67300628289311289658570813 25237735608491733621964055)
        ·
          refine ⟨37856603412737600432946083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25237735608491733621964055 37856603412737600432946083)
          ·
            refine ⟨56784905119106400649419125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37856603412737600432946083 56784905119106400649419125)
            ·
              refine ⟨5323584854916225060883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56784905119106400649419125 5323584854916225060883043)
              ·
                refine ⟨7985377282374337591324565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5323584854916225060883043 7985377282374337591324565)
                ·
                  refine ⟨374314560111297074593339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7985377282374337591324565 374314560111297074593339)
                  ·
                    rfl

theorem cell23_6560775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 6].length) (baseStart_6560775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560775 prefixEnd_6560775 := by exact prefixLift 6560775
  have htrace : WordTrace (prefixWord ++ tailWord_6560775) baseStart_6560775 baseEnd_6560775 := by
    simpa [prefixWord, tailWord_6560775, baseEnd_6560775] using wordTrace_append hprefix tailTrace_6560775
  have hstable : (prefixWord ++ tailWord_6560775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560775).length < 2 ^ (prefixWord ++ tailWord_6560775).sum := by decide
  have hdescent : baseEnd_6560775 < baseStart_6560775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560796 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6560796 : Nat := 118140960795 + 6560796 * 2 ^ 59
def prefixEnd_6560796 : Nat := 4983230072969 + 3 ^ 40 * 6560796 * 2
def baseEnd_6560796 : Nat := 1122947274698472696392485

theorem tailTrace_6560796 : CollatzResearch.WordTrace tailWord_6560796 prefixEnd_6560796 1122947274698472696392485 := by
  unfold tailWord_6560796
  simp only [CollatzResearch.WordTrace]
  refine ⟨119645944369682030797383121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159527925826242707729844161 119645944369682030797383121)
  ·
    refine ⟨89734458277261523098037341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119645944369682030797383121 89734458277261523098037341)
    ·
      refine ⟨33650421853973071161764003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89734458277261523098037341 33650421853973071161764003)
      ·
        refine ⟨50475632780959606742646005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33650421853973071161764003 50475632780959606742646005)
        ·
          refine ⟨4732090573214963132123063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50475632780959606742646005 4732090573214963132123063)
          ·
            refine ⟨7098135859822444698184595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732090573214963132123063 7098135859822444698184595)
            ·
              refine ⟨10647203789733667047276893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098135859822444698184595 10647203789733667047276893)
              ·
                refine ⟨3992701421150125142728835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10647203789733667047276893 3992701421150125142728835)
                ·
                  refine ⟨5989052131725187714093253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992701421150125142728835 5989052131725187714093253)
                  ·
                    refine ⟨1122947274698472696392485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5989052131725187714093253 1122947274698472696392485)
                    ·
                      rfl

theorem cell23_6560796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6560796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560796 prefixEnd_6560796 := by exact prefixLift 6560796
  have htrace : WordTrace (prefixWord ++ tailWord_6560796) baseStart_6560796 baseEnd_6560796 := by
    simpa [prefixWord, tailWord_6560796, baseEnd_6560796] using wordTrace_append hprefix tailTrace_6560796
  have hstable : (prefixWord ++ tailWord_6560796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560796).length < 2 ^ (prefixWord ++ tailWord_6560796).sum := by decide
  have hdescent : baseEnd_6560796 < baseStart_6560796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560835 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 2, 4]
def baseStart_6560835 : Nat := 118140960795 + 6560835 * 2 ^ 59
def prefixEnd_6560835 : Nat := 4983230072969 + 3 ^ 40 * 6560835 * 2
def baseEnd_6560835 : Nat := 1122953949946981145529925

theorem tailTrace_6560835 : CollatzResearch.WordTrace tailWord_6560835 prefixEnd_6560835 1122953949946981145529925 := by
  unfold tailWord_6560835
  simp only [CollatzResearch.WordTrace]
  refine ⟨239293311186222771255435959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159528874124148514170290639 239293311186222771255435959)
  ·
    refine ⟨358939966779334156883153939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239293311186222771255435959 358939966779334156883153939)
    ·
      refine ⟨538409950169001235324730909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358939966779334156883153939 538409950169001235324730909)
      ·
        refine ⟨201903731313375463246774091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538409950169001235324730909 201903731313375463246774091)
        ·
          refine ⟨302855596970063194870161137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201903731313375463246774091 302855596970063194870161137)
          ·
            refine ⟨227141697727547396152620853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302855596970063194870161137 227141697727547396152620853)
            ·
              refine ⟨21294534161957568389308205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227141697727547396152620853 21294534161957568389308205)
              ·
                refine ⟨7985450310734088145990577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21294534161957568389308205 7985450310734088145990577)
                ·
                  refine ⟨5989087733050566109492933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7985450310734088145990577 5989087733050566109492933)
                  ·
                    refine ⟨1122953949946981145529925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5989087733050566109492933 1122953949946981145529925)
                    ·
                      rfl

theorem cell23_6560835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 4].length) (baseStart_6560835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560835 prefixEnd_6560835 := by exact prefixLift 6560835
  have htrace : WordTrace (prefixWord ++ tailWord_6560835) baseStart_6560835 baseEnd_6560835 := by
    simpa [prefixWord, tailWord_6560835, baseEnd_6560835] using wordTrace_append hprefix tailTrace_6560835
  have hstable : (prefixWord ++ tailWord_6560835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560835).length < 2 ^ (prefixWord ++ tailWord_6560835).sum := by decide
  have hdescent : baseEnd_6560835 < baseStart_6560835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560842 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_6560842 : Nat := 118140960795 + 6560842 * 2 ^ 59
def prefixEnd_6560842 : Nat := 4983230072969 + 3 ^ 40 * 6560842 * 2
def baseEnd_6560842 : Nat := 3368865444205524909202243

theorem tailTrace_6560842 : CollatzResearch.WordTrace tailWord_6560842 prefixEnd_6560842 3368865444205524909202243 := by
  unfold tailWord_6560842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59823391624299352862735195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159529044331464940967293853 59823391624299352862735195)
  ·
    refine ⟨89735087436449029294102793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59823391624299352862735195 89735087436449029294102793)
    ·
      refine ⟨67301315577336771970577095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89735087436449029294102793 67301315577336771970577095)
      ·
        refine ⟨100951973366005157955865643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67301315577336771970577095 100951973366005157955865643)
        ·
          refine ⟨151427960049007736933798465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100951973366005157955865643 151427960049007736933798465)
          ·
            refine ⟨113570970036755802700348849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151427960049007736933798465 113570970036755802700348849)
            ·
              refine ⟨85178227527566852025261637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113570970036755802700348849 85178227527566852025261637)
              ·
                refine ⟨15970917661418784754736557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85178227527566852025261637 15970917661418784754736557)
                ·
                  refine ⟨5989094123032044283026209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15970917661418784754736557 5989094123032044283026209)
                  ·
                    refine ⟨4491820592274033212269657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989094123032044283026209 4491820592274033212269657)
                    ·
                      refine ⟨3368865444205524909202243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491820592274033212269657 3368865444205524909202243)
                      ·
                        rfl

theorem cell23_6560842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_6560842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560842 prefixEnd_6560842 := by exact prefixLift 6560842
  have htrace : WordTrace (prefixWord ++ tailWord_6560842) baseStart_6560842 baseEnd_6560842 := by
    simpa [prefixWord, tailWord_6560842, baseEnd_6560842] using wordTrace_append hprefix tailTrace_6560842
  have hstable : (prefixWord ++ tailWord_6560842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560842).length < 2 ^ (prefixWord ++ tailWord_6560842).sum := by decide
  have hdescent : baseEnd_6560842 < baseStart_6560842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560892 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_6560892 : Nat := 118140960795 + 6560892 * 2 ^ 59
def prefixEnd_6560892 : Nat := 4983230072969 + 3 ^ 40 * 6560892 * 2
def baseEnd_6560892 : Nat := 3368891118238249713577013

theorem tailTrace_6560892 : CollatzResearch.WordTrace tailWord_6560892 prefixEnd_6560892 3368891118238249713577013 := by
  unfold tailWord_6560892
  simp only [CollatzResearch.WordTrace]
  refine ⟨119647695073508134995130465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159530260098010846660173953 119647695073508134995130465)
  ·
    refine ⟨89735771305131101246347849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119647695073508134995130465 89735771305131101246347849)
    ·
      refine ⟨67301828478848325934760887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89735771305131101246347849 67301828478848325934760887)
      ·
        refine ⟨100952742718272488902141331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67301828478848325934760887 100952742718272488902141331)
        ·
          refine ⟨151429114077408733353211997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100952742718272488902141331 151429114077408733353211997)
          ·
            refine ⟨56785917779028275007454499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151429114077408733353211997 56785917779028275007454499)
            ·
              refine ⟨85178876668542412511181749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56785917779028275007454499 85178876668542412511181749)
              ·
                refine ⟨7985519687675851172923289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85178876668542412511181749 7985519687675851172923289)
                ·
                  refine ⟨5989139765756888379692467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7985519687675851172923289 5989139765756888379692467)
                  ·
                    refine ⟨8983709648635332569538701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989139765756888379692467 8983709648635332569538701)
                    ·
                      refine ⟨3368891118238249713577013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8983709648635332569538701 3368891118238249713577013)
                      ·
                        rfl

theorem cell23_6560892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_6560892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560892 prefixEnd_6560892 := by exact prefixLift 6560892
  have htrace : WordTrace (prefixWord ++ tailWord_6560892) baseStart_6560892 baseEnd_6560892 := by
    simpa [prefixWord, tailWord_6560892, baseEnd_6560892] using wordTrace_append hprefix tailTrace_6560892
  have hstable : (prefixWord ++ tailWord_6560892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560892).length < 2 ^ (prefixWord ++ tailWord_6560892).sum := by decide
  have hdescent : baseEnd_6560892 < baseStart_6560892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560919 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_6560919 : Nat := 118140960795 + 6560919 * 2 ^ 59
def prefixEnd_6560919 : Nat := 4983230072969 + 3 ^ 40 * 6560919 * 2
def baseEnd_6560919 : Nat := 3368904982215921107939389

theorem tailTrace_6560919 : CollatzResearch.WordTrace tailWord_6560919 prefixEnd_6560919 3368904982215921107939389 := by
  unfold tailWord_6560919
  simp only [CollatzResearch.WordTrace]
  refine ⟨239296374917918453601493811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159530916611945635734329207 239296374917918453601493811)
  ·
    refine ⟨358944562376877680402240717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239296374917918453601493811 358944562376877680402240717)
    ·
      refine ⟨134604210891329130150840269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358944562376877680402240717 134604210891329130150840269)
      ·
        refine ⟨50476579084248423806565101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134604210891329130150840269 50476579084248423806565101)
        ·
          refine ⟨18928717156593158927461913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50476579084248423806565101 18928717156593158927461913)
          ·
            refine ⟨14196537867444869195596435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18928717156593158927461913 14196537867444869195596435)
            ·
              refine ⟨21294806801167303793394653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14196537867444869195596435 21294806801167303793394653)
              ·
                refine ⟨7985552550437738922522995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21294806801167303793394653 7985552550437738922522995)
                ·
                  refine ⟨11978328825656608383784493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985552550437738922522995 11978328825656608383784493)
                  ·
                    refine ⟨4491873309621228143919185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11978328825656608383784493 4491873309621228143919185)
                    ·
                      refine ⟨3368904982215921107939389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491873309621228143919185 3368904982215921107939389)
                      ·
                        rfl

theorem cell23_6560919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_6560919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560919 prefixEnd_6560919 := by exact prefixLift 6560919
  have htrace : WordTrace (prefixWord ++ tailWord_6560919) baseStart_6560919 baseEnd_6560919 := by
    simpa [prefixWord, tailWord_6560919, baseEnd_6560919] using wordTrace_append hprefix tailTrace_6560919
  have hstable : (prefixWord ++ tailWord_6560919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560919).length < 2 ^ (prefixWord ++ tailWord_6560919).sum := by decide
  have hdescent : baseEnd_6560919 < baseStart_6560919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560926 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6560926 : Nat := 118140960795 + 6560926 * 2 ^ 59
def prefixEnd_6560926 : Nat := 4983230072969 + 3 ^ 40 * 6560926 * 2
def baseEnd_6560926 : Nat := 3368908576580502580551857

theorem tailTrace_6560926 : CollatzResearch.WordTrace tailWord_6560926 prefixEnd_6560926 3368908576580502580551857 := by
  unfold tailWord_6560926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29912078778611636724624829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159531086819262062531332421 29912078778611636724624829)
  ·
    refine ⟨11217029541979363771734311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29912078778611636724624829 11217029541979363771734311)
    ·
      refine ⟨16825544312969045657601467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11217029541979363771734311 16825544312969045657601467)
      ·
        refine ⟨25238316469453568486402201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16825544312969045657601467 25238316469453568486402201)
        ·
          refine ⟨18928737352090176364801651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25238316469453568486402201 18928737352090176364801651)
          ·
            refine ⟨28393106028135264547202477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18928737352090176364801651 28393106028135264547202477)
            ·
              refine ⟨10647414760550724205200929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28393106028135264547202477 10647414760550724205200929)
              ·
                refine ⟨7985561070413043153900697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10647414760550724205200929 7985561070413043153900697)
                ·
                  refine ⟨5989170802809782365425523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7985561070413043153900697 5989170802809782365425523)
                  ·
                    refine ⟨8983756204214673548138285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989170802809782365425523 8983756204214673548138285)
                    ·
                      refine ⟨3368908576580502580551857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8983756204214673548138285 3368908576580502580551857)
                      ·
                        rfl

theorem cell23_6560926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6560926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560926 prefixEnd_6560926 := by exact prefixLift 6560926
  have htrace : WordTrace (prefixWord ++ tailWord_6560926) baseStart_6560926 baseEnd_6560926 := by
    simpa [prefixWord, tailWord_6560926, baseEnd_6560926] using wordTrace_append hprefix tailTrace_6560926
  have hstable : (prefixWord ++ tailWord_6560926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560926).length < 2 ^ (prefixWord ++ tailWord_6560926).sum := by decide
  have hdescent : baseEnd_6560926 < baseStart_6560926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6560989 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 7]
def baseStart_6560989 : Nat := 118140960795 + 6560989 * 2 ^ 59
def prefixEnd_6560989 : Nat := 4983230072969 + 3 ^ 40 * 6560989 * 2
def baseEnd_6560989 : Nat := 374326769540192870451563

theorem tailTrace_6560989 : CollatzResearch.WordTrace tailWord_6560989 prefixEnd_6560989 374326769540192870451563 := by
  unfold tailWord_6560989
  simp only [CollatzResearch.WordTrace]
  refine ⟨239298928027664855556542021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159532618685109903704361347 239298928027664855556542021)
  ·
    refine ⟨44868549005187160416851629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239298928027664855556542021 44868549005187160416851629)
    ·
      refine ⟨16825705876945185156319361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44868549005187160416851629 16825705876945185156319361)
      ·
        refine ⟨12619279407708888867239521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16825705876945185156319361 12619279407708888867239521)
        ·
          refine ⟨9464459555781666650429641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12619279407708888867239521 9464459555781666650429641)
          ·
            refine ⟨7098344666836249987822231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9464459555781666650429641 7098344666836249987822231)
            ·
              refine ⟨10647517000254374981733347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098344666836249987822231 10647517000254374981733347)
              ·
                refine ⟨15971275500381562472600021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10647517000254374981733347 15971275500381562472600021)
                ·
                  refine ⟨374326769540192870451563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15971275500381562472600021 374326769540192870451563)
                  ·
                    rfl

theorem cell23_6560989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_6560989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6560989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6560989 prefixEnd_6560989 := by exact prefixLift 6560989
  have htrace : WordTrace (prefixWord ++ tailWord_6560989) baseStart_6560989 baseEnd_6560989 := by
    simpa [prefixWord, tailWord_6560989, baseEnd_6560989] using wordTrace_append hprefix tailTrace_6560989
  have hstable : (prefixWord ++ tailWord_6560989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6560989).length < 2 ^ (prefixWord ++ tailWord_6560989).sum := by decide
  have hdescent : baseEnd_6560989 < baseStart_6560989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6560989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561129 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 5, 2, 2]
def baseStart_6561129 : Nat := 118140960795 + 6561129 * 2 ^ 59
def prefixEnd_6561129 : Nat := 4983230072969 + 3 ^ 40 * 6561129 * 2
def baseEnd_6561129 : Nat := 3369012813153365286313423

theorem tailTrace_6561129 : CollatzResearch.WordTrace tailWord_6561129 prefixEnd_6561129 3369012813153365286313423 := by
  unfold tailWord_6561129
  simp only [CollatzResearch.WordTrace]
  refine ⟨239304034247157659466638441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159536022831438439644425627 239304034247157659466638441)
  ·
    refine ⟨179478025685368244599978831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239304034247157659466638441 179478025685368244599978831)
    ·
      refine ⟨269217038528052366899968247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179478025685368244599978831 269217038528052366899968247)
      ·
        refine ⟨403825557792078550349952371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269217038528052366899968247 403825557792078550349952371)
        ·
          refine ⟨605738336688117825524928557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403825557792078550349952371 605738336688117825524928557)
          ·
            refine ⟨227151876258044184571848209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605738336688117825524928557 227151876258044184571848209)
            ·
              refine ⟨170363907193533138428886157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227151876258044184571848209 170363907193533138428886157)
              ·
                refine ⟨63886465197574926910832309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170363907193533138428886157 63886465197574926910832309)
                ·
                  refine ⟨5989356112272649397890529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63886465197574926910832309 5989356112272649397890529)
                  ·
                    refine ⟨4492017084204487048417897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989356112272649397890529 4492017084204487048417897)
                    ·
                      refine ⟨3369012813153365286313423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492017084204487048417897 3369012813153365286313423)
                      ·
                        rfl

theorem cell23_6561129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 2, 2].length) (baseStart_6561129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561129 prefixEnd_6561129 := by exact prefixLift 6561129
  have htrace : WordTrace (prefixWord ++ tailWord_6561129) baseStart_6561129 baseEnd_6561129 := by
    simpa [prefixWord, tailWord_6561129, baseEnd_6561129] using wordTrace_append hprefix tailTrace_6561129
  have hstable : (prefixWord ++ tailWord_6561129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561129).length < 2 ^ (prefixWord ++ tailWord_6561129).sum := by decide
  have hdescent : baseEnd_6561129 < baseStart_6561129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561135 : List Nat := [1, 1, 2, 1, 3, 1, 5, 9]
def baseStart_6561135 : Nat := 118140960795 + 6561135 * 2 ^ 59
def prefixEnd_6561135 : Nat := 4983230072969 + 3 ^ 40 * 6561135 * 2
def baseEnd_6561135 : Nat := 124778366445825639364385

theorem tailTrace_6561135 : CollatzResearch.WordTrace tailWord_6561135 prefixEnd_6561135 124778366445825639364385 := by
  unfold tailWord_6561135
  simp only [CollatzResearch.WordTrace]
  refine ⟨239304253085135922491356859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159536168723423948327571239 239304253085135922491356859)
  ·
    refine ⟨358956379627703883737035289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239304253085135922491356859 358956379627703883737035289)
    ·
      refine ⟨269217284720777912802776467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358956379627703883737035289 269217284720777912802776467)
      ·
        refine ⟨403825927081166869204164701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269217284720777912802776467 403825927081166869204164701)
        ·
          refine ⟨151434722655437575951561763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403825927081166869204164701 151434722655437575951561763)
          ·
            refine ⟨227152083983156363927342645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151434722655437575951561763 227152083983156363927342645)
            ·
              refine ⟨21295507873420909118188373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227152083983156363927342645 21295507873420909118188373)
              ·
                refine ⟨124778366445825639364385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21295507873420909118188373 124778366445825639364385)
                ·
                  rfl

theorem cell23_6561135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 9].length) (baseStart_6561135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561135 prefixEnd_6561135 := by exact prefixLift 6561135
  have htrace : WordTrace (prefixWord ++ tailWord_6561135) baseStart_6561135 baseEnd_6561135 := by
    simpa [prefixWord, tailWord_6561135, baseEnd_6561135] using wordTrace_append hprefix tailTrace_6561135
  have hstable : (prefixWord ++ tailWord_6561135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561135).length < 2 ^ (prefixWord ++ tailWord_6561135).sum := by decide
  have hdescent : baseEnd_6561135 < baseStart_6561135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561149 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_6561149 : Nat := 118140960795 + 6561149 * 2 ^ 59
def prefixEnd_6561149 : Nat := 4983230072969 + 3 ^ 40 * 6561149 * 2
def baseEnd_6561149 : Nat := 3369023082766455208063331

theorem tailTrace_6561149 : CollatzResearch.WordTrace tailWord_6561149 prefixEnd_6561149 3369023082766455208063331 := by
  unfold tailWord_6561149
  simp only [CollatzResearch.WordTrace]
  refine ⟨239304763707085202882366501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159536509138056801921577667 239304763707085202882366501)
  ·
    refine ⟨44869643195078475540443719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239304763707085202882366501 44869643195078475540443719)
    ·
      refine ⟨67304464792617713310665579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44869643195078475540443719 67304464792617713310665579)
      ·
        refine ⟨100956697188926569965998369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67304464792617713310665579 100956697188926569965998369)
        ·
          refine ⟨75717522891694927474498777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100956697188926569965998369 75717522891694927474498777)
          ·
            refine ⟨56788142168771195605874083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75717522891694927474498777 56788142168771195605874083)
            ·
              refine ⟨85182213253156793408811125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56788142168771195605874083 85182213253156793408811125)
              ·
                refine ⟨7985832492483449382076043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85182213253156793408811125 7985832492483449382076043)
                ·
                  refine ⟨11978748738725174073114065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985832492483449382076043 11978748738725174073114065)
                  ·
                    refine ⟨8984061554043880554835549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11978748738725174073114065 8984061554043880554835549)
                    ·
                      refine ⟨3369023082766455208063331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984061554043880554835549 3369023082766455208063331)
                      ·
                        rfl

theorem cell23_6561149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_6561149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561149 prefixEnd_6561149 := by exact prefixLift 6561149
  have htrace : WordTrace (prefixWord ++ tailWord_6561149) baseStart_6561149 baseEnd_6561149 := by
    simpa [prefixWord, tailWord_6561149, baseEnd_6561149] using wordTrace_append hprefix tailTrace_6561149
  have hstable : (prefixWord ++ tailWord_6561149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561149).length < 2 ^ (prefixWord ++ tailWord_6561149).sum := by decide
  have hdescent : baseEnd_6561149 < baseStart_6561149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561150 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6561150 : Nat := 118140960795 + 6561150 * 2 ^ 59
def prefixEnd_6561150 : Nat := 4983230072969 + 3 ^ 40 * 6561150 * 2
def baseEnd_6561150 : Nat := 3369023596247109704150827

theorem tailTrace_6561150 : CollatzResearch.WordTrace tailWord_6561150 prefixEnd_6561150 3369023596247109704150827 := by
  unfold tailWord_6561150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29913100022510197506644113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159536533453387720035435269 29913100022510197506644113)
  ·
    refine ⟨22434825016882648129983085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29913100022510197506644113 22434825016882648129983085)
    ·
      refine ⟨8413059381330993048743657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22434825016882648129983085 8413059381330993048743657)
      ·
        refine ⟨6309794535998244786557743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8413059381330993048743657 6309794535998244786557743)
        ·
          refine ⟨9464691803997367179836615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309794535998244786557743 9464691803997367179836615)
          ·
            refine ⟨14197037705996050769754923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9464691803997367179836615 14197037705996050769754923)
            ·
              refine ⟨21295556558994076154632385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197037705996050769754923 21295556558994076154632385)
              ·
                refine ⟨15971667419245557115974289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21295556558994076154632385 15971667419245557115974289)
                ·
                  refine ⟨11978750564434167836980717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15971667419245557115974289 11978750564434167836980717)
                  ·
                    refine ⟨4492031461662812938867769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11978750564434167836980717 4492031461662812938867769)
                    ·
                      refine ⟨3369023596247109704150827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492031461662812938867769 3369023596247109704150827)
                      ·
                        rfl

theorem cell23_6561150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6561150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561150 prefixEnd_6561150 := by exact prefixLift 6561150
  have htrace : WordTrace (prefixWord ++ tailWord_6561150) baseStart_6561150 baseEnd_6561150 := by
    simpa [prefixWord, tailWord_6561150, baseEnd_6561150] using wordTrace_append hprefix tailTrace_6561150
  have hstable : (prefixWord ++ tailWord_6561150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561150).length < 2 ^ (prefixWord ++ tailWord_6561150).sum := by decide
  have hdescent : baseEnd_6561150 < baseStart_6561150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561180 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6561180 : Nat := 118140960795 + 6561180 * 2 ^ 59
def prefixEnd_6561180 : Nat := 4983230072969 + 3 ^ 40 * 6561180 * 2
def baseEnd_6561180 : Nat := 3369039000666744586775689

theorem tailTrace_6561180 : CollatzResearch.WordTrace tailWord_6561180 prefixEnd_6561180 3369039000666744586775689 := by
  unfold tailWord_6561180
  simp only [CollatzResearch.WordTrace]
  refine ⟨119652947184986447588372497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159537262913315263451163329 119652947184986447588372497)
  ·
    refine ⟨89739710388739835691279373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119652947184986447588372497 89739710388739835691279373)
    ·
      refine ⟨33652391395777438384229765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89739710388739835691279373 33652391395777438384229765)
      ·
        refine ⟨6309823386708269697043081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33652391395777438384229765 6309823386708269697043081)
        ·
          refine ⟨4732367540031202272782311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6309823386708269697043081 4732367540031202272782311)
          ·
            refine ⟨7098551310046803409173467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732367540031202272782311 7098551310046803409173467)
            ·
              refine ⟨10647826965070205113760201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098551310046803409173467 10647826965070205113760201)
              ·
                refine ⟨7985870223802653835320151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10647826965070205113760201 7985870223802653835320151)
                ·
                  refine ⟨11978805335703980752980227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985870223802653835320151 11978805335703980752980227)
                  ·
                    refine ⟨17968208003555971129470341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11978805335703980752980227 17968208003555971129470341)
                    ·
                      refine ⟨3369039000666744586775689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17968208003555971129470341 3369039000666744586775689)
                      ·
                        rfl

theorem cell23_6561180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6561180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561180 prefixEnd_6561180 := by exact prefixLift 6561180
  have htrace : WordTrace (prefixWord ++ tailWord_6561180) baseStart_6561180 baseEnd_6561180 := by
    simpa [prefixWord, tailWord_6561180, baseEnd_6561180] using wordTrace_append hprefix tailTrace_6561180
  have hstable : (prefixWord ++ tailWord_6561180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561180).length < 2 ^ (prefixWord ++ tailWord_6561180).sum := by decide
  have hdescent : baseEnd_6561180 < baseStart_6561180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561232 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_6561232 : Nat := 118140960795 + 6561232 * 2 ^ 59
def prefixEnd_6561232 : Nat := 4983230072969 + 3 ^ 40 * 6561232 * 2
def baseEnd_6561232 : Nat := 3369065701660778383325449

theorem tailTrace_6561232 : CollatzResearch.WordTrace tailWord_6561232 prefixEnd_6561232 3369065701660778383325449 := by
  unfold tailWord_6561232
  simp only [CollatzResearch.WordTrace]
  refine ⟨119653895482892254028818975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159538527310523005371758633 119653895482892254028818975)
  ·
    refine ⟨179480843224338381043228463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119653895482892254028818975 179480843224338381043228463)
    ·
      refine ⟨269221264836507571564842695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179480843224338381043228463 269221264836507571564842695)
      ·
        refine ⟨403831897254761357347264043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269221264836507571564842695 403831897254761357347264043)
        ·
          refine ⟨605747845882142036020896065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403831897254761357347264043 605747845882142036020896065)
          ·
            refine ⟨454310884411606527015672049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605747845882142036020896065 454310884411606527015672049)
            ·
              refine ⟨340733163308704895261754037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454310884411606527015672049 340733163308704895261754037)
              ·
                refine ⟨31943734060191083930789441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 340733163308704895261754037 31943734060191083930789441)
                ·
                  refine ⟨23957800545143312948092081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31943734060191083930789441 23957800545143312948092081)
                  ·
                    refine ⟨17968350408857484711069061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23957800545143312948092081 17968350408857484711069061)
                    ·
                      refine ⟨3369065701660778383325449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17968350408857484711069061 3369065701660778383325449)
                      ·
                        rfl

theorem cell23_6561232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_6561232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561232 prefixEnd_6561232 := by exact prefixLift 6561232
  have htrace : WordTrace (prefixWord ++ tailWord_6561232) baseStart_6561232 baseEnd_6561232 := by
    simpa [prefixWord, tailWord_6561232, baseEnd_6561232] using wordTrace_append hprefix tailTrace_6561232
  have hstable : (prefixWord ++ tailWord_6561232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561232).length < 2 ^ (prefixWord ++ tailWord_6561232).sum := by decide
  have hdescent : baseEnd_6561232 < baseStart_6561232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561242 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_6561242 : Nat := 118140960795 + 6561242 * 2 ^ 59
def prefixEnd_6561242 : Nat := 4983230072969 + 3 ^ 40 * 6561242 * 2
def baseEnd_6561242 : Nat := 374341204051924816022267

theorem tailTrace_6561242 : CollatzResearch.WordTrace tailWord_6561242 prefixEnd_6561242 374341204051924816022267 := by
  unfold tailWord_6561242
  simp only [CollatzResearch.WordTrace]
  refine ⟨59827038923937069941375495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159538770463832186510334653 59827038923937069941375495)
  ·
    refine ⟨89740558385905604912063243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59827038923937069941375495 89740558385905604912063243)
    ·
      refine ⟨134610837578858407368094865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89740558385905604912063243 134610837578858407368094865)
      ·
        refine ⟨100958128184143805526071149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134610837578858407368094865 100958128184143805526071149)
        ·
          refine ⟨37859298069053927072276681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100958128184143805526071149 37859298069053927072276681)
          ·
            refine ⟨28394473551790445304207511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37859298069053927072276681 28394473551790445304207511)
            ·
              refine ⟨42591710327685667956311267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28394473551790445304207511 42591710327685667956311267)
              ·
                refine ⟨63887565491528501934466901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42591710327685667956311267 63887565491528501934466901)
                ·
                  refine ⟨374341204051924816022267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63887565491528501934466901 374341204051924816022267)
                  ·
                    rfl

theorem cell23_6561242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_6561242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561242 prefixEnd_6561242 := by exact prefixLift 6561242
  have htrace : WordTrace (prefixWord ++ tailWord_6561242) baseStart_6561242 baseEnd_6561242 := by
    simpa [prefixWord, tailWord_6561242, baseEnd_6561242] using wordTrace_append hprefix tailTrace_6561242
  have hstable : (prefixWord ++ tailWord_6561242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561242).length < 2 ^ (prefixWord ++ tailWord_6561242).sum := by decide
  have hdescent : baseEnd_6561242 < baseStart_6561242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561270 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6561270 : Nat := 118140960795 + 6561270 * 2 ^ 59
def prefixEnd_6561270 : Nat := 4983230072969 + 3 ^ 40 * 6561270 * 2
def baseEnd_6561270 : Nat := 3369085213925649234650275

theorem tailTrace_6561270 : CollatzResearch.WordTrace tailWord_6561270 prefixEnd_6561270 3369085213925649234650275 := by
  unfold tailWord_6561270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14956823558727927534220079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159539451293097893698347509 14956823558727927534220079)
  ·
    refine ⟨22435235338091891301330119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14956823558727927534220079 22435235338091891301330119)
    ·
      refine ⟨33652853007137836951995179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22435235338091891301330119 33652853007137836951995179)
      ·
        refine ⟨50479279510706755427992769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33652853007137836951995179 50479279510706755427992769)
        ·
          refine ⟨37859459633030066570994577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50479279510706755427992769 37859459633030066570994577)
          ·
            refine ⟨28394594724772549928245933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37859459633030066570994577 28394594724772549928245933)
            ·
              refine ⟨10647973021789706223092225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28394594724772549928245933 10647973021789706223092225)
              ·
                refine ⟨7985979766342279667319169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10647973021789706223092225 7985979766342279667319169)
                ·
                  refine ⟨5989484824756709750489377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7985979766342279667319169 5989484824756709750489377)
                  ·
                    refine ⟨4492113618567532312867033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989484824756709750489377 4492113618567532312867033)
                    ·
                      refine ⟨3369085213925649234650275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492113618567532312867033 3369085213925649234650275)
                      ·
                        rfl

theorem cell23_6561270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6561270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561270 prefixEnd_6561270 := by exact prefixLift 6561270
  have htrace : WordTrace (prefixWord ++ tailWord_6561270) baseStart_6561270 baseEnd_6561270 := by
    simpa [prefixWord, tailWord_6561270, baseEnd_6561270] using wordTrace_append hprefix tailTrace_6561270
  have hstable : (prefixWord ++ tailWord_6561270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561270).length < 2 ^ (prefixWord ++ tailWord_6561270).sum := by decide
  have hdescent : baseEnd_6561270 < baseStart_6561270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561279 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 5, 2]
def baseStart_6561279 : Nat := 118140960795 + 6561279 * 2 ^ 59
def prefixEnd_6561279 : Nat := 4983230072969 + 3 ^ 40 * 6561279 * 2
def baseEnd_6561279 : Nat := 3369089835251539699437733

theorem tailTrace_6561279 : CollatzResearch.WordTrace tailWord_6561279 prefixEnd_6561279 3369089835251539699437733 := by
  unfold tailWord_6561279
  simp only [CollatzResearch.WordTrace]
  refine ⟨239309505196614235084598891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159539670131076156723065927 239309505196614235084598891)
  ·
    refine ⟨358964257794921352626898337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239309505196614235084598891 358964257794921352626898337)
    ·
      refine ⟨269223193346191014470173753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358964257794921352626898337 269223193346191014470173753)
      ·
        refine ⟨201917395009643260852630315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269223193346191014470173753 201917395009643260852630315)
        ·
          refine ⟨302876092514464891278945473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201917395009643260852630315 302876092514464891278945473)
          ·
            refine ⟨227157069385848668459209105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302876092514464891278945473 227157069385848668459209105)
            ·
              refine ⟨170367802039386501344406829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227157069385848668459209105 170367802039386501344406829)
              ·
                refine ⟨63887925764769938004152561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170367802039386501344406829 63887925764769938004152561)
                ·
                  refine ⟨47915944323577453503114421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63887925764769938004152561 47915944323577453503114421)
                  ·
                    refine ⟨4492119780335386265916977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47915944323577453503114421 4492119780335386265916977)
                    ·
                      refine ⟨3369089835251539699437733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492119780335386265916977 3369089835251539699437733)
                      ·
                        rfl

theorem cell23_6561279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_6561279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561279 prefixEnd_6561279 := by exact prefixLift 6561279
  have htrace : WordTrace (prefixWord ++ tailWord_6561279) baseStart_6561279 baseEnd_6561279 := by
    simpa [prefixWord, tailWord_6561279, baseEnd_6561279] using wordTrace_append hprefix tailTrace_6561279
  have hstable : (prefixWord ++ tailWord_6561279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561279).length < 2 ^ (prefixWord ++ tailWord_6561279).sum := by decide
  have hdescent : baseEnd_6561279 < baseStart_6561279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561309 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6561309 : Nat := 118140960795 + 6561309 * 2 ^ 59
def prefixEnd_6561309 : Nat := 4983230072969 + 3 ^ 40 * 6561309 * 2
def baseEnd_6561309 : Nat := 3369105239671174582062595

theorem tailTrace_6561309 : CollatzResearch.WordTrace tailWord_6561309 prefixEnd_6561309 3369105239671174582062595 := by
  unfold tailWord_6561309
  simp only [CollatzResearch.WordTrace]
  refine ⟨239310599386505550208190981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159540399591003700138793987 239310599386505550208190981)
  ·
    refine ⟨44870737384969790664035809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239310599386505550208190981 44870737384969790664035809)
    ·
      refine ⟨33653053038727342998026857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44870737384969790664035809 33653053038727342998026857)
      ·
        refine ⟨25239789779045507248520143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33653053038727342998026857 25239789779045507248520143)
        ·
          refine ⟨37859684668568260872780215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25239789779045507248520143 37859684668568260872780215)
          ·
            refine ⟨56789527002852391309170323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37859684668568260872780215 56789527002852391309170323)
            ·
              refine ⟨85184290504278586963755485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56789527002852391309170323 85184290504278586963755485)
              ·
                refine ⟨31944108939104470111408307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85184290504278586963755485 31944108939104470111408307)
                ·
                  refine ⟨47916163408656705167112461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31944108939104470111408307 47916163408656705167112461)
                  ·
                    refine ⟨17968561278246264437667173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47916163408656705167112461 17968561278246264437667173)
                    ·
                      refine ⟨3369105239671174582062595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17968561278246264437667173 3369105239671174582062595)
                      ·
                        rfl

theorem cell23_6561309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6561309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561309 prefixEnd_6561309 := by exact prefixLift 6561309
  have htrace : WordTrace (prefixWord ++ tailWord_6561309) baseStart_6561309 baseEnd_6561309 := by
    simpa [prefixWord, tailWord_6561309, baseEnd_6561309] using wordTrace_append hprefix tailTrace_6561309
  have hstable : (prefixWord ++ tailWord_6561309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561309).length < 2 ^ (prefixWord ++ tailWord_6561309).sum := by decide
  have hdescent : baseEnd_6561309 < baseStart_6561309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561326 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6561326 : Nat := 118140960795 + 6561326 * 2 ^ 59
def prefixEnd_6561326 : Nat := 4983230072969 + 3 ^ 40 * 6561326 * 2
def baseEnd_6561326 : Nat := 3369113968842301015550017

theorem tailTrace_6561326 : CollatzResearch.WordTrace tailWord_6561326 prefixEnd_6561326 3369113968842301015550017 := by
  unfold tailWord_6561326
  simp only [CollatzResearch.WordTrace]
  refine ⟨29913902428430495263944979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159540812951629308074373221 29913902428430495263944979)
  ·
    refine ⟨44870853642645742895917469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29913902428430495263944979 44870853642645742895917469)
    ·
      refine ⟨16826570115992153585969051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44870853642645742895917469 16826570115992153585969051)
      ·
        refine ⟨25239855173988230378953577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16826570115992153585969051 25239855173988230378953577)
        ·
          refine ⟨18929891380491172784215183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25239855173988230378953577 18929891380491172784215183)
          ·
            refine ⟨28394837070736759176322775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18929891380491172784215183 28394837070736759176322775)
            ·
              refine ⟨42592255606105138764484163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28394837070736759176322775 42592255606105138764484163)
              ·
                refine ⟨63888383409157708146726245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42592255606105138764484163 63888383409157708146726245)
                ·
                  refine ⟨11979071889217070277511171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63888383409157708146726245 11979071889217070277511171)
                  ·
                    refine ⟨17968607833825605416266757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11979071889217070277511171 17968607833825605416266757)
                    ·
                      refine ⟨3369113968842301015550017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17968607833825605416266757 3369113968842301015550017)
                      ·
                        rfl

theorem cell23_6561326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6561326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561326 prefixEnd_6561326 := by exact prefixLift 6561326
  have htrace : WordTrace (prefixWord ++ tailWord_6561326) baseStart_6561326 baseEnd_6561326 := by
    simpa [prefixWord, tailWord_6561326, baseEnd_6561326] using wordTrace_append hprefix tailTrace_6561326
  have hstable : (prefixWord ++ tailWord_6561326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561326).length < 2 ^ (prefixWord ++ tailWord_6561326).sum := by decide
  have hdescent : baseEnd_6561326 < baseStart_6561326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561336 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_6561336 : Nat := 118140960795 + 6561336 * 2 ^ 59
def prefixEnd_6561336 : Nat := 4983230072969 + 3 ^ 40 * 6561336 * 2
def baseEnd_6561336 : Nat := 1123039701216281992141657

theorem tailTrace_6561336 : CollatzResearch.WordTrace tailWord_6561336 prefixEnd_6561336 1123039701216281992141657 := by
  unfold tailWord_6561336
  simp only [CollatzResearch.WordTrace]
  refine ⟨119655792078703866909711931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159541056104938489212949241 119655792078703866909711931)
  ·
    refine ⟨179483688118055800364567897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119655792078703866909711931 179483688118055800364567897)
    ·
      refine ⟨134612766088541850273425923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179483688118055800364567897 134612766088541850273425923)
      ·
        refine ⟨201919149132812775410138885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134612766088541850273425923 201919149132812775410138885)
        ·
          refine ⟨37859840462402395389401041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201919149132812775410138885 37859840462402395389401041)
          ·
            refine ⟨28394880346801796542050781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37859840462402395389401041 28394880346801796542050781)
            ·
              refine ⟨10648080130050673703269043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28394880346801796542050781 10648080130050673703269043)
              ·
                refine ⟨15972120195076010554903565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648080130050673703269043 15972120195076010554903565)
                ·
                  refine ⟨5989545073153503958088837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15972120195076010554903565 5989545073153503958088837)
                  ·
                    refine ⟨1123039701216281992141657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5989545073153503958088837 1123039701216281992141657)
                    ·
                      rfl

theorem cell23_6561336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_6561336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561336 prefixEnd_6561336 := by exact prefixLift 6561336
  have htrace : WordTrace (prefixWord ++ tailWord_6561336) baseStart_6561336 baseEnd_6561336 := by
    simpa [prefixWord, tailWord_6561336, baseEnd_6561336] using wordTrace_append hprefix tailTrace_6561336
  have hstable : (prefixWord ++ tailWord_6561336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561336).length < 2 ^ (prefixWord ++ tailWord_6561336).sum := by decide
  have hdescent : baseEnd_6561336 < baseStart_6561336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561349 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 6]
def baseStart_6561349 : Nat := 118140960795 + 6561349 * 2 ^ 59
def prefixEnd_6561349 : Nat := 4983230072969 + 3 ^ 40 * 6561349 * 2
def baseEnd_6561349 : Nat := 374347308766372713951379

theorem tailTrace_6561349 : CollatzResearch.WordTrace tailWord_6561349 prefixEnd_6561349 374347308766372713951379 := by
  unfold tailWord_6561349
  simp only [CollatzResearch.WordTrace]
  refine ⟨239312058306360637039647101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159541372204240424693098067 239312058306360637039647101)
  ·
    refine ⟨89742021864885238889867663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239312058306360637039647101 89742021864885238889867663)
    ·
      refine ⟨134613032797327858334801495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89742021864885238889867663 134613032797327858334801495)
      ·
        refine ⟨201919549195991787502202243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134613032797327858334801495 201919549195991787502202243)
        ·
          refine ⟨302879323793987681253303365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201919549195991787502202243 302879323793987681253303365)
          ·
            refine ⟨56789873211372690234994381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302879323793987681253303365 56789873211372690234994381)
            ·
              refine ⟨21296202454264758838122893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56789873211372690234994381 21296202454264758838122893)
              ·
                refine ⟨7986075920349284564296085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21296202454264758838122893 7986075920349284564296085)
                ·
                  refine ⟨374347308766372713951379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7986075920349284564296085 374347308766372713951379)
                  ·
                    rfl

theorem cell23_6561349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_6561349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561349 prefixEnd_6561349 := by exact prefixLift 6561349
  have htrace : WordTrace (prefixWord ++ tailWord_6561349) baseStart_6561349 baseEnd_6561349 := by
    simpa [prefixWord, tailWord_6561349, baseEnd_6561349] using wordTrace_append hprefix tailTrace_6561349
  have hstable : (prefixWord ++ tailWord_6561349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561349).length < 2 ^ (prefixWord ++ tailWord_6561349).sum := by decide
  have hdescent : baseEnd_6561349 < baseStart_6561349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561463 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_6561463 : Nat := 118140960795 + 6561463 * 2 ^ 59
def prefixEnd_6561463 : Nat := 4983230072969 + 3 ^ 40 * 6561463 * 2
def baseEnd_6561463 : Nat := 3369184315691966979536887

theorem tailTrace_6561463 : CollatzResearch.WordTrace tailWord_6561463 prefixEnd_6561463 3369184315691966979536887 := by
  unfold tailWord_6561463
  simp only [CollatzResearch.WordTrace]
  refine ⟨239316216227947634509297043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159544144151965089672864695 239316216227947634509297043)
  ·
    refine ⟨358974324341921451763945565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239316216227947634509297043 358974324341921451763945565)
    ·
      refine ⟨134615371628220544411479587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358974324341921451763945565 134615371628220544411479587)
      ·
        refine ⟨201923057442330816617219381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134615371628220544411479587 201923057442330816617219381)
        ·
          refine ⟨18930286635218514057864317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201923057442330816617219381 18930286635218514057864317)
          ·
            refine ⟨7098857488206942771699119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18930286635218514057864317 7098857488206942771699119)
            ·
              refine ⟨10648286232310414157548679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098857488206942771699119 10648286232310414157548679)
              ·
                refine ⟨15972429348465621236323019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648286232310414157548679 15972429348465621236323019)
                ·
                  refine ⟨23958644022698431854484529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15972429348465621236323019 23958644022698431854484529)
                  ·
                    refine ⟨17968983017023823890863397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23958644022698431854484529 17968983017023823890863397)
                    ·
                      refine ⟨3369184315691966979536887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17968983017023823890863397 3369184315691966979536887)
                      ·
                        rfl

theorem cell23_6561463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_6561463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561463 prefixEnd_6561463 := by exact prefixLift 6561463
  have htrace : WordTrace (prefixWord ++ tailWord_6561463) baseStart_6561463 baseEnd_6561463 := by
    simpa [prefixWord, tailWord_6561463, baseEnd_6561463] using wordTrace_append hprefix tailTrace_6561463
  have hstable : (prefixWord ++ tailWord_6561463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561463).length < 2 ^ (prefixWord ++ tailWord_6561463).sum := by decide
  have hdescent : baseEnd_6561463 < baseStart_6561463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561470 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_6561470 : Nat := 118140960795 + 6561470 * 2 ^ 59
def prefixEnd_6561470 : Nat := 4983230072969 + 3 ^ 40 * 6561470 * 2
def baseEnd_6561470 : Nat := 3369187910056548452149355

theorem tailTrace_6561470 : CollatzResearch.WordTrace tailWord_6561470 prefixEnd_6561470 3369187910056548452149355 := by
  unfold tailWord_6561470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29914558942365284338100233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159544314359281516469867909 29914558942365284338100233)
  ·
    refine ⟨22435919206773963253575175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29914558942365284338100233 22435919206773963253575175)
    ·
      refine ⟨33653878810160944880362763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22435919206773963253575175 33653878810160944880362763)
      ·
        refine ⟨50480818215241417320544145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33653878810160944880362763 50480818215241417320544145)
        ·
          refine ⟨37860613661431062990408109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50480818215241417320544145 37860613661431062990408109)
          ·
            refine ⟨14197730123036648621403041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37860613661431062990408109 14197730123036648621403041)
            ·
              refine ⟨10648297592277486466052281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14197730123036648621403041 10648297592277486466052281)
              ·
                refine ⟨7986223194208114849539211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10648297592277486466052281 7986223194208114849539211)
                ·
                  refine ⟨11979334791312172274308817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7986223194208114849539211 11979334791312172274308817)
                  ·
                    refine ⟨8984501093484129205731613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11979334791312172274308817 8984501093484129205731613)
                    ·
                      refine ⟨3369187910056548452149355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984501093484129205731613 3369187910056548452149355)
                      ·
                        rfl

theorem cell23_6561470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_6561470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561470 prefixEnd_6561470 := by exact prefixLift 6561470
  have htrace : WordTrace (prefixWord ++ tailWord_6561470) baseStart_6561470 baseEnd_6561470 := by
    simpa [prefixWord, tailWord_6561470, baseEnd_6561470] using wordTrace_append hprefix tailTrace_6561470
  have hstable : (prefixWord ++ tailWord_6561470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561470).length < 2 ^ (prefixWord ++ tailWord_6561470).sum := by decide
  have hdescent : baseEnd_6561470 < baseStart_6561470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561479 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_6561479 : Nat := 118140960795 + 6561479 * 2 ^ 59
def prefixEnd_6561479 : Nat := 4983230072969 + 3 ^ 40 * 6561479 * 2
def baseEnd_6561479 : Nat := 3369192531382438916936813

theorem tailTrace_6561479 : CollatzResearch.WordTrace tailWord_6561479 prefixEnd_6561479 3369192531382438916936813 := by
  unfold tailWord_6561479
  simp only [CollatzResearch.WordTrace]
  refine ⟨239316799795889669241879491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159544533197259779494586327 239316799795889669241879491)
  ·
    refine ⟨358975199693834503862819237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239316799795889669241879491 358975199693834503862819237)
    ·
      refine ⟨67307849942593969474278607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358975199693834503862819237 67307849942593969474278607)
      ·
        refine ⟨100961774913890954211417911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67307849942593969474278607 100961774913890954211417911)
        ·
          refine ⟨151442662370836431317126867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100961774913890954211417911 151442662370836431317126867)
          ·
            refine ⟨227163993556254646975690301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151442662370836431317126867 227163993556254646975690301)
            ·
              refine ⟨85186497583595492615883863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227163993556254646975690301 85186497583595492615883863)
              ·
                refine ⟨127779746375393238923825795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85186497583595492615883863 127779746375393238923825795)
                ·
                  refine ⟨191669619563089858385738693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127779746375393238923825795 191669619563089858385738693)
                  ·
                    refine ⟨35938053668079348447326005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191669619563089858385738693 35938053668079348447326005)
                    ·
                      refine ⟨3369192531382438916936813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35938053668079348447326005 3369192531382438916936813)
                      ·
                        rfl

theorem cell23_6561479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_6561479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561479 prefixEnd_6561479 := by exact prefixLift 6561479
  have htrace : WordTrace (prefixWord ++ tailWord_6561479) baseStart_6561479 baseEnd_6561479 := by
    simpa [prefixWord, tailWord_6561479, baseEnd_6561479] using wordTrace_append hprefix tailTrace_6561479
  have hstable : (prefixWord ++ tailWord_6561479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561479).length < 2 ^ (prefixWord ++ tailWord_6561479).sum := by decide
  have hdescent : baseEnd_6561479 < baseStart_6561479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561501 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6561501 : Nat := 118140960795 + 6561501 * 2 ^ 59
def prefixEnd_6561501 : Nat := 4983230072969 + 3 ^ 40 * 6561501 * 2
def baseEnd_6561501 : Nat := 3369203827956837830861713

theorem tailTrace_6561501 : CollatzResearch.WordTrace tailWord_6561501 prefixEnd_6561501 3369203827956837830861713 := by
  unfold tailWord_6561501
  simp only [CollatzResearch.WordTrace]
  refine ⟨239317602201809966999180357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159545068134539977999453571 239317602201809966999180357)
  ·
    refine ⟨44872050412839368812346317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239317602201809966999180357 44872050412839368812346317)
    ·
      refine ⟨16827018904814763304629869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44872050412839368812346317 16827018904814763304629869)
      ·
        refine ⟨6310132089305536239236201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16827018904814763304629869 6310132089305536239236201)
        ·
          refine ⟨4732599066979152179427151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6310132089305536239236201 4732599066979152179427151)
          ·
            refine ⟨7098898600468728269140727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732599066979152179427151 7098898600468728269140727)
            ·
              refine ⟨10648347900703092403711091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098898600468728269140727 10648347900703092403711091)
              ·
                refine ⟨15972521851054638605566637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648347900703092403711091 15972521851054638605566637)
                ·
                  refine ⟨5989695694145489477087489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15972521851054638605566637 5989695694145489477087489)
                  ·
                    refine ⟨4492271770609117107815617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989695694145489477087489 4492271770609117107815617)
                    ·
                      refine ⟨3369203827956837830861713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492271770609117107815617 3369203827956837830861713)
                      ·
                        rfl

theorem cell23_6561501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6561501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561501 prefixEnd_6561501 := by exact prefixLift 6561501
  have htrace : WordTrace (prefixWord ++ tailWord_6561501) baseStart_6561501 baseEnd_6561501 := by
    simpa [prefixWord, tailWord_6561501, baseEnd_6561501] using wordTrace_append hprefix tailTrace_6561501
  have hstable : (prefixWord ++ tailWord_6561501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561501).length < 2 ^ (prefixWord ++ tailWord_6561501).sum := by decide
  have hdescent : baseEnd_6561501 < baseStart_6561501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561517 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6561517 : Nat := 118140960795 + 6561517 * 2 ^ 59
def prefixEnd_6561517 : Nat := 4983230072969 + 3 ^ 40 * 6561517 * 2
def baseEnd_6561517 : Nat := 3369212043647309768261639

theorem tailTrace_6561517 : CollatzResearch.WordTrace tailWord_6561517 prefixEnd_6561517 3369212043647309768261639 := by
  unfold tailWord_6561517
  simp only [CollatzResearch.WordTrace]
  refine ⟨239318185769752001731762805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159545457179834667821175203 239318185769752001731762805)
  ·
    refine ⟨22436079915914250162352763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239318185769752001731762805 22436079915914250162352763)
    ·
      refine ⟨33654119873871375243529145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22436079915914250162352763 33654119873871375243529145)
      ·
        refine ⟨25240589905403531432646859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33654119873871375243529145 25240589905403531432646859)
        ·
          refine ⟨37860884858105297148970289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240589905403531432646859 37860884858105297148970289)
          ·
            refine ⟨28395663643578972861727717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37860884858105297148970289 28395663643578972861727717)
            ·
              refine ⟨5324186933171057411573947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28395663643578972861727717 5324186933171057411573947)
              ·
                refine ⟨7986280399756586117360921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324186933171057411573947 7986280399756586117360921)
                ·
                  refine ⟨5989710299817439588020691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7986280399756586117360921 5989710299817439588020691)
                  ·
                    refine ⟨8984565449726159382031037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989710299817439588020691 8984565449726159382031037)
                    ·
                      refine ⟨3369212043647309768261639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984565449726159382031037 3369212043647309768261639)
                      ·
                        rfl

theorem cell23_6561517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6561517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561517 prefixEnd_6561517 := by exact prefixLift 6561517
  have htrace : WordTrace (prefixWord ++ tailWord_6561517) baseStart_6561517 baseEnd_6561517 := by
    simpa [prefixWord, tailWord_6561517, baseEnd_6561517] using wordTrace_append hprefix tailTrace_6561517
  have hstable : (prefixWord ++ tailWord_6561517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561517).length < 2 ^ (prefixWord ++ tailWord_6561517).sum := by decide
  have hdescent : baseEnd_6561517 < baseStart_6561517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561540 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6561540 : Nat := 118140960795 + 6561540 * 2 ^ 59
def prefixEnd_6561540 : Nat := 4983230072969 + 3 ^ 40 * 6561540 * 2
def baseEnd_6561540 : Nat := 3369223853702363178274033

theorem tailTrace_6561540 : CollatzResearch.WordTrace tailWord_6561540 prefixEnd_6561540 3369223853702363178274033 := by
  unfold tailWord_6561540
  simp only [CollatzResearch.WordTrace]
  refine ⟨119659512324334338329925037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159546016432445784439900049 119659512324334338329925037)
  ·
    refine ⟨44872317121625376873721889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119659512324334338329925037 44872317121625376873721889)
    ·
      refine ⟨33654237841219032655291417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44872317121625376873721889 33654237841219032655291417)
      ·
        refine ⟨25240678380914274491468563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33654237841219032655291417 25240678380914274491468563)
        ·
          refine ⟨37861017571371411737202845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240678380914274491468563 37861017571371411737202845)
          ·
            refine ⟨14197881589264279401451067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37861017571371411737202845 14197881589264279401451067)
            ·
              refine ⟨21296822383896419102176601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197881589264279401451067 21296822383896419102176601)
              ·
                refine ⟨15972616787922314326632451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21296822383896419102176601 15972616787922314326632451)
                ·
                  refine ⟨23958925181883471489948677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15972616787922314326632451 23958925181883471489948677)
                  ·
                    refine ⟨4492298471603150904365377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23958925181883471489948677 4492298471603150904365377)
                    ·
                      refine ⟨3369223853702363178274033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492298471603150904365377 3369223853702363178274033)
                      ·
                        rfl

theorem cell23_6561540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6561540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561540 prefixEnd_6561540 := by exact prefixLift 6561540
  have htrace : WordTrace (prefixWord ++ tailWord_6561540) baseStart_6561540 baseEnd_6561540 := by
    simpa [prefixWord, tailWord_6561540, baseEnd_6561540] using wordTrace_append hprefix tailTrace_6561540
  have hstable : (prefixWord ++ tailWord_6561540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561540).length < 2 ^ (prefixWord ++ tailWord_6561540).sum := by decide
  have hdescent : baseEnd_6561540 < baseStart_6561540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561557 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_6561557 : Nat := 118140960795 + 6561557 * 2 ^ 59
def prefixEnd_6561557 : Nat := 4983230072969 + 3 ^ 40 * 6561557 * 2
def baseEnd_6561557 : Nat := 3369232582873489611761455

theorem tailTrace_6561557 : CollatzResearch.WordTrace tailWord_6561557 prefixEnd_6561557 3369232582873489611761455 := by
  unfold tailWord_6561557
  simp only [CollatzResearch.WordTrace]
  refine ⟨239319644689607088563218925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159546429793071392375479283 239319644689607088563218925)
  ·
    refine ⟨89744866758602658211207097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239319644689607088563218925 89744866758602658211207097)
    ·
      refine ⟨67308650068951993658405323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89744866758602658211207097 67308650068951993658405323)
      ·
        refine ⟨100962975103427990487607985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67308650068951993658405323 100962975103427990487607985)
        ·
          refine ⟨75722231327570992865705989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100962975103427990487607985 75722231327570992865705989)
          ·
            refine ⟨14197918373919561162319873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75722231327570992865705989 14197918373919561162319873)
            ·
              refine ⟨10648438780439670871739905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14197918373919561162319873 10648438780439670871739905)
              ·
                refine ⟨7986329085329753153804929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10648438780439670871739905 7986329085329753153804929)
                ·
                  refine ⟨5989746813997314865353697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7986329085329753153804929 5989746813997314865353697)
                  ·
                    refine ⟨4492310110497986149015273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989746813997314865353697 4492310110497986149015273)
                    ·
                      refine ⟨3369232582873489611761455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492310110497986149015273 3369232582873489611761455)
                      ·
                        rfl

theorem cell23_6561557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_6561557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561557 prefixEnd_6561557 := by exact prefixLift 6561557
  have htrace : WordTrace (prefixWord ++ tailWord_6561557) baseStart_6561557 baseEnd_6561557 := by
    simpa [prefixWord, tailWord_6561557, baseEnd_6561557] using wordTrace_append hprefix tailTrace_6561557
  have hstable : (prefixWord ++ tailWord_6561557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561557).length < 2 ^ (prefixWord ++ tailWord_6561557).sum := by decide
  have hdescent : baseEnd_6561557 < baseStart_6561557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561573 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_6561573 : Nat := 118140960795 + 6561573 * 2 ^ 59
def prefixEnd_6561573 : Nat := 4983230072969 + 3 ^ 40 * 6561573 * 2
def baseEnd_6561573 : Nat := 3369240798563961549161381

theorem tailTrace_6561573 : CollatzResearch.WordTrace tailWord_6561573 prefixEnd_6561573 3369240798563961549161381 := by
  unfold tailWord_6561573
  simp only [CollatzResearch.WordTrace]
  refine ⟨239320228257549123295801373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159546818838366082197200915 239320228257549123295801373)
  ·
    refine ⟨89745085596580921235925515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239320228257549123295801373 89745085596580921235925515)
    ·
      refine ⟨134617628394871381853888273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89745085596580921235925515 134617628394871381853888273)
      ·
        refine ⟨100963221296153536390416205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134617628394871381853888273 100963221296153536390416205)
        ·
          refine ⟨37861207986057576146406077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100963221296153536390416205 37861207986057576146406077)
          ·
            refine ⟨14197952994771591054902279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37861207986057576146406077 14197952994771591054902279)
            ·
              refine ⟨21296929492157386582353419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197952994771591054902279 21296929492157386582353419)
              ·
                refine ⟨31945394238236079873530129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21296929492157386582353419 31945394238236079873530129)
                ·
                  refine ⟨23959045678677059905147597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31945394238236079873530129 23959045678677059905147597)
                  ·
                    refine ⟨8984642129503897464430349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23959045678677059905147597 8984642129503897464430349)
                    ·
                      refine ⟨3369240798563961549161381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984642129503897464430349 3369240798563961549161381)
                      ·
                        rfl

theorem cell23_6561573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_6561573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561573 prefixEnd_6561573 := by exact prefixLift 6561573
  have htrace : WordTrace (prefixWord ++ tailWord_6561573) baseStart_6561573 baseEnd_6561573 := by
    simpa [prefixWord, tailWord_6561573, baseEnd_6561573] using wordTrace_append hprefix tailTrace_6561573
  have hstable : (prefixWord ++ tailWord_6561573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561573).length < 2 ^ (prefixWord ++ tailWord_6561573).sum := by decide
  have hdescent : baseEnd_6561573 < baseStart_6561573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561626 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_6561626 : Nat := 118140960795 + 6561626 * 2 ^ 59
def prefixEnd_6561626 : Nat := 4983230072969 + 3 ^ 40 * 6561626 * 2
def baseEnd_6561626 : Nat := 3369268013038649841798637

theorem tailTrace_6561626 : CollatzResearch.WordTrace tailWord_6561626 prefixEnd_6561626 3369268013038649841798637 := by
  unfold tailWord_6561626
  simp only [CollatzResearch.WordTrace]
  refine ⟨59830540331589278336870183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159548107550904742231653821 59830540331589278336870183)
  ·
    refine ⟨89745810497383917505305275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59830540331589278336870183 89745810497383917505305275)
    ·
      refine ⟨134618715746075876257957913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89745810497383917505305275 134618715746075876257957913)
      ·
        refine ⟨100964036809556907193468435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134618715746075876257957913 100964036809556907193468435)
        ·
          refine ⟨151446055214335360790202653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100964036809556907193468435 151446055214335360790202653)
          ·
            refine ⟨56792270705375760296325995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151446055214335360790202653 56792270705375760296325995)
            ·
              refine ⟨85188406058063640444488993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56792270705375760296325995 85188406058063640444488993)
              ·
                refine ⟨63891304543547730333366745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85188406058063640444488993 63891304543547730333366745)
                ·
                  refine ⟨47918478407660797750025059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63891304543547730333366745 47918478407660797750025059)
                  ·
                    refine ⟨71877717611491196625037589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47918478407660797750025059 71877717611491196625037589)
                    ·
                      refine ⟨3369268013038649841798637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71877717611491196625037589 3369268013038649841798637)
                      ·
                        rfl

theorem cell23_6561626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_6561626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561626 prefixEnd_6561626 := by exact prefixLift 6561626
  have htrace : WordTrace (prefixWord ++ tailWord_6561626) baseStart_6561626 baseEnd_6561626 := by
    simpa [prefixWord, tailWord_6561626, baseEnd_6561626] using wordTrace_append hprefix tailTrace_6561626
  have hstable : (prefixWord ++ tailWord_6561626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561626).length < 2 ^ (prefixWord ++ tailWord_6561626).sum := by decide
  have hdescent : baseEnd_6561626 < baseStart_6561626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561674 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_6561674 : Nat := 118140960795 + 6561674 * 2 ^ 59
def prefixEnd_6561674 : Nat := 4983230072969 + 3 ^ 40 * 6561674 * 2
def baseEnd_6561674 : Nat := 1123097553370021884666139

theorem tailTrace_6561674 : CollatzResearch.WordTrace tailWord_6561674 prefixEnd_6561674 1123097553370021884666139 := by
  unfold tailWord_6561674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59830978007545804386307019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159549274686788811696818717 59830978007545804386307019)
  ·
    refine ⟨89746467011318706579460529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59830978007545804386307019 89746467011318706579460529)
    ·
      refine ⟨67309850258489029934595397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89746467011318706579460529 67309850258489029934595397)
      ·
        refine ⟨12620596923466693112736637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67309850258489029934595397 12620596923466693112736637)
        ·
          refine ⟨4732723846300009917276239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12620596923466693112736637 4732723846300009917276239)
          ·
            refine ⟨7099085769450014875914359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732723846300009917276239 7099085769450014875914359)
            ·
              refine ⟨10648628654175022313871539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099085769450014875914359 10648628654175022313871539)
              ·
                refine ⟨15972942981262533470807309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648628654175022313871539 15972942981262533470807309)
                ·
                  refine ⟨5989853617973450051552741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15972942981262533470807309 5989853617973450051552741)
                  ·
                    refine ⟨1123097553370021884666139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5989853617973450051552741 1123097553370021884666139)
                    ·
                      rfl

theorem cell23_6561674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_6561674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561674 prefixEnd_6561674 := by exact prefixLift 6561674
  have htrace : WordTrace (prefixWord ++ tailWord_6561674) baseStart_6561674 baseEnd_6561674 := by
    simpa [prefixWord, tailWord_6561674, baseEnd_6561674] using wordTrace_append hprefix tailTrace_6561674
  have hstable : (prefixWord ++ tailWord_6561674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561674).length < 2 ^ (prefixWord ++ tailWord_6561674).sum := by decide
  have hdescent : baseEnd_6561674 < baseStart_6561674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561676 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6561676 : Nat := 118140960795 + 6561676 * 2 ^ 59
def prefixEnd_6561676 : Nat := 4983230072969 + 3 ^ 40 * 6561676 * 2
def baseEnd_6561676 : Nat := 3369293687071374646173407

theorem tailTrace_6561676 : CollatzResearch.WordTrace tailWord_6561676 prefixEnd_6561676 3369293687071374646173407 := by
  unfold tailWord_6561676
  simp only [CollatzResearch.WordTrace]
  refine ⟨119661992488087985943400441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159549323317450647924533921 119661992488087985943400441)
  ·
    refine ⟨89746494366065989457550331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119661992488087985943400441 89746494366065989457550331)
    ·
      refine ⟨134619741549098984186325497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89746494366065989457550331 134619741549098984186325497)
      ·
        refine ⟨100964806161824238139744123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134619741549098984186325497 100964806161824238139744123)
        ·
          refine ⟨151447209242736357209616185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100964806161824238139744123 151447209242736357209616185)
          ·
            refine ⟨113585406932052267907212139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151447209242736357209616185 113585406932052267907212139)
            ·
              refine ⟨170378110398078401860818209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113585406932052267907212139 170378110398078401860818209)
              ·
                refine ⟨127783582798558801395613657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170378110398078401860818209 127783582798558801395613657)
                ·
                  refine ⟨95837687098919101046710243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127783582798558801395613657 95837687098919101046710243)
                  ·
                    refine ⟨143756530648378651570065365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95837687098919101046710243 143756530648378651570065365)
                    ·
                      refine ⟨3369293687071374646173407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143756530648378651570065365 3369293687071374646173407)
                      ·
                        rfl

theorem cell23_6561676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6561676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561676 prefixEnd_6561676 := by exact prefixLift 6561676
  have htrace : WordTrace (prefixWord ++ tailWord_6561676) baseStart_6561676 baseEnd_6561676 := by
    simpa [prefixWord, tailWord_6561676, baseEnd_6561676] using wordTrace_append hprefix tailTrace_6561676
  have hstable : (prefixWord ++ tailWord_6561676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561676).length < 2 ^ (prefixWord ++ tailWord_6561676).sum := by decide
  have hdescent : baseEnd_6561676 < baseStart_6561676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561700 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_6561700 : Nat := 118140960795 + 6561700 * 2 ^ 59
def prefixEnd_6561700 : Nat := 4983230072969 + 3 ^ 40 * 6561700 * 2
def baseEnd_6561700 : Nat := 1123102003535694184091099

theorem tailTrace_6561700 : CollatzResearch.WordTrace tailWord_6561700 prefixEnd_6561700 1123102003535694184091099 := by
  unfold tailWord_6561700
  simp only [CollatzResearch.WordTrace]
  refine ⟨119662430164044511992837277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159549906885392682657116369 119662430164044511992837277)
  ·
    refine ⟨44873411311516691997313979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119662430164044511992837277 44873411311516691997313979)
    ·
      refine ⟨67310116967275037995970969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44873411311516691997313979 67310116967275037995970969)
      ·
        refine ⟨50482587725456278496978227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67310116967275037995970969 50482587725456278496978227)
        ·
          refine ⟨75723881588184417745467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50482587725456278496978227 75723881588184417745467341)
          ·
            refine ⟨28396455595569156654550253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75723881588184417745467341 28396455595569156654550253)
            ·
              refine ⟨10648670848338433745456345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28396455595569156654550253 10648670848338433745456345)
              ·
                refine ⟨7986503136253825309092259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10648670848338433745456345 7986503136253825309092259)
                ·
                  refine ⟨11979754704380737963638389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7986503136253825309092259 11979754704380737963638389)
                  ·
                    refine ⟨1123102003535694184091099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11979754704380737963638389 1123102003535694184091099)
                    ·
                      rfl

theorem cell23_6561700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_6561700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561700 prefixEnd_6561700 := by exact prefixLift 6561700
  have htrace : WordTrace (prefixWord ++ tailWord_6561700) baseStart_6561700 baseEnd_6561700 := by
    simpa [prefixWord, tailWord_6561700, baseEnd_6561700] using wordTrace_append hprefix tailTrace_6561700
  have hstable : (prefixWord ++ tailWord_6561700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561700).length < 2 ^ (prefixWord ++ tailWord_6561700).sum := by decide
  have hdescent : baseEnd_6561700 < baseStart_6561700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561713 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_6561713 : Nat := 118140960795 + 6561713 * 2 ^ 59
def prefixEnd_6561713 : Nat := 4983230072969 + 3 ^ 40 * 6561713 * 2
def baseEnd_6561713 : Nat := 1123104228618530333803579

theorem tailTrace_6561713 : CollatzResearch.WordTrace tailWord_6561713 prefixEnd_6561713 1123104228618530333803579 := by
  unfold tailWord_6561713
  simp only [CollatzResearch.WordTrace]
  refine ⟨239325334477041927205897793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159550222984694618137265195 239325334477041927205897793)
  ·
    refine ⟨179494000857781445404423345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239325334477041927205897793 179494000857781445404423345)
    ·
      refine ⟨134620500643336084053317509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179494000857781445404423345 134620500643336084053317509)
      ·
        refine ⟨25241343870625515759997033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134620500643336084053317509 25241343870625515759997033)
        ·
          refine ⟨18931007902969136819997775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25241343870625515759997033 18931007902969136819997775)
          ·
            refine ⟨28396511854453705229996663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18931007902969136819997775 28396511854453705229996663)
            ·
              refine ⟨42594767781680557844994995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28396511854453705229996663 42594767781680557844994995)
              ·
                refine ⟨63892151672520836767492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42594767781680557844994995 63892151672520836767492493)
                ·
                  refine ⟨23959556877195313787809685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63892151672520836767492493 23959556877195313787809685)
                  ·
                    refine ⟨1123104228618530333803579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23959556877195313787809685 1123104228618530333803579)
                    ·
                      rfl

theorem cell23_6561713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_6561713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561713 prefixEnd_6561713 := by exact prefixLift 6561713
  have htrace : WordTrace (prefixWord ++ tailWord_6561713) baseStart_6561713 baseEnd_6561713 := by
    simpa [prefixWord, tailWord_6561713, baseEnd_6561713] using wordTrace_append hprefix tailTrace_6561713
  have hstable : (prefixWord ++ tailWord_6561713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561713).length < 2 ^ (prefixWord ++ tailWord_6561713).sum := by decide
  have hdescent : baseEnd_6561713 < baseStart_6561713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561717 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6561717 : Nat := 118140960795 + 6561717 * 2 ^ 59
def prefixEnd_6561717 : Nat := 4983230072969 + 3 ^ 40 * 6561717 * 2
def baseEnd_6561717 : Nat := 1123104913259402995253573

theorem tailTrace_6561717 : CollatzResearch.WordTrace tailWord_6561717 prefixEnd_6561717 1123104913259402995253573 := by
  unfold tailWord_6561717
  simp only [CollatzResearch.WordTrace]
  refine ⟨239325480369027435889043405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159550320246018290592695603 239325480369027435889043405)
  ·
    refine ⟨89747055138385288458391277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239325480369027435889043405 89747055138385288458391277)
    ·
      refine ⟨33655145676894483171896729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89747055138385288458391277 33655145676894483171896729)
      ·
        refine ⟨25241359257670862378922547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33655145676894483171896729 25241359257670862378922547)
        ·
          refine ⟨37862038886506293568383821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25241359257670862378922547 37862038886506293568383821)
          ·
            refine ⟨14198264582439860088143933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37862038886506293568383821 14198264582439860088143933)
            ·
              refine ⟨5324349218414947533053975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14198264582439860088143933 5324349218414947533053975)
              ·
                refine ⟨7986523827622421299580963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324349218414947533053975 7986523827622421299580963)
                ·
                  refine ⟨11979785741433631949371445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7986523827622421299580963 11979785741433631949371445)
                  ·
                    refine ⟨1123104913259402995253573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11979785741433631949371445 1123104913259402995253573)
                    ·
                      rfl

theorem cell23_6561717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6561717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561717 prefixEnd_6561717 := by exact prefixLift 6561717
  have htrace : WordTrace (prefixWord ++ tailWord_6561717) baseStart_6561717 baseEnd_6561717 := by
    simpa [prefixWord, tailWord_6561717, baseEnd_6561717] using wordTrace_append hprefix tailTrace_6561717
  have hstable : (prefixWord ++ tailWord_6561717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561717).length < 2 ^ (prefixWord ++ tailWord_6561717).sum := by decide
  have hdescent : baseEnd_6561717 < baseStart_6561717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561723 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3]
def baseStart_6561723 : Nat := 118140960795 + 6561723 * 2 ^ 59
def prefixEnd_6561723 : Nat := 4983230072969 + 3 ^ 40 * 6561723 * 2
def baseEnd_6561723 : Nat := 3369317820662135962285691

theorem tailTrace_6561723 : CollatzResearch.WordTrace tailWord_6561723 prefixEnd_6561723 3369317820662135962285691 := by
  unfold tailWord_6561723
  simp only [CollatzResearch.WordTrace]
  refine ⟨239325699207005698913761823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159550466138003799275841215 239325699207005698913761823)
  ·
    refine ⟨358988548810508548370642735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239325699207005698913761823 358988548810508548370642735)
    ·
      refine ⟨538482823215762822555964103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358988548810508548370642735 538482823215762822555964103)
      ·
        refine ⟨807724234823644233833946155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538482823215762822555964103 807724234823644233833946155)
        ·
          refine ⟨1211586352235466350750919233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807724234823644233833946155 1211586352235466350750919233)
          ·
            refine ⟨908689764176599763063189425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211586352235466350750919233 908689764176599763063189425)
            ·
              refine ⟨681517323132449822297392069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908689764176599763063189425 681517323132449822297392069)
              ·
                refine ⟨127784498087334341680761013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681517323132449822297392069 127784498087334341680761013)
                ·
                  refine ⟨11979796695687594532571345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127784498087334341680761013 11979796695687594532571345)
                  ·
                    refine ⟨8984847521765695899428509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11979796695687594532571345 8984847521765695899428509)
                    ·
                      refine ⟨3369317820662135962285691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984847521765695899428509 3369317820662135962285691)
                      ·
                        rfl

theorem cell23_6561723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3].length) (baseStart_6561723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561723 prefixEnd_6561723 := by exact prefixLift 6561723
  have htrace : WordTrace (prefixWord ++ tailWord_6561723) baseStart_6561723 baseEnd_6561723 := by
    simpa [prefixWord, tailWord_6561723, baseEnd_6561723] using wordTrace_append hprefix tailTrace_6561723
  have hstable : (prefixWord ++ tailWord_6561723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561723).length < 2 ^ (prefixWord ++ tailWord_6561723).sum := by decide
  have hdescent : baseEnd_6561723 < baseStart_6561723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561740 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6561740 : Nat := 118140960795 + 6561740 * 2 ^ 59
def prefixEnd_6561740 : Nat := 4983230072969 + 3 ^ 40 * 6561740 * 2
def baseEnd_6561740 : Nat := 3369326549833262395773113

theorem tailTrace_6561740 : CollatzResearch.WordTrace tailWord_6561740 prefixEnd_6561740 3369326549833262395773113 := by
  unfold tailWord_6561740
  simp only [CollatzResearch.WordTrace]
  refine ⟨119663159623972055408565337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159550879498629407211420449 119663159623972055408565337)
  ·
    refine ⟨89747369717979041556424003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119663159623972055408565337 89747369717979041556424003)
    ·
      refine ⟨134621054576968562334636005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89747369717979041556424003 134621054576968562334636005)
      ·
        refine ⟨25241447733181605437744251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134621054576968562334636005 25241447733181605437744251)
        ·
          refine ⟨37862171599772408156616377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25241447733181605437744251 37862171599772408156616377)
          ·
            refine ⟨28396628699829306117462283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37862171599772408156616377 28396628699829306117462283)
            ·
              refine ⟨42594943049743959176193425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28396628699829306117462283 42594943049743959176193425)
              ·
                refine ⟨31946207287307969382145069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42594943049743959176193425 31946207287307969382145069)
                ·
                  refine ⟨11979827732740488518304401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31946207287307969382145069 11979827732740488518304401)
                  ·
                    refine ⟨8984870799555366388728301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11979827732740488518304401 8984870799555366388728301)
                    ·
                      refine ⟨3369326549833262395773113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984870799555366388728301 3369326549833262395773113)
                      ·
                        rfl

theorem cell23_6561740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6561740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561740 prefixEnd_6561740 := by exact prefixLift 6561740
  have htrace : WordTrace (prefixWord ++ tailWord_6561740) baseStart_6561740 baseEnd_6561740 := by
    simpa [prefixWord, tailWord_6561740, baseEnd_6561740] using wordTrace_append hprefix tailTrace_6561740
  have hstable : (prefixWord ++ tailWord_6561740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561740).length < 2 ^ (prefixWord ++ tailWord_6561740).sum := by decide
  have hdescent : baseEnd_6561740 < baseStart_6561740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
