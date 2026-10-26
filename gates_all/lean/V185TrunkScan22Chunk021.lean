import V185TrunkScan22Chunk020

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_187296 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_187296 : Nat := 118140960795 + 187296 * 2 ^ 59
def prefixEnd_187296 : Nat := 4983230072969 + 3 ^ 40 * 187296 * 2
def baseEnd_187296 : Nat := 21371749481023208275255

theorem tailTrace_187296 : CollatzResearch.WordTrace tailWord_187296 prefixEnd_187296 21371749481023208275255 := by
  unfold tailWord_187296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415623164733027227622871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4554164219644036303497161 3415623164733027227622871)
  ·
    refine ⟨5123434747099540841434307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3415623164733027227622871 5123434747099540841434307)
    ·
      refine ⟨7685152120649311262151461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5123434747099540841434307 7685152120649311262151461)
      ·
        refine ⟨1440966022621745861653399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7685152120649311262151461 1440966022621745861653399)
        ·
          refine ⟨2161449033932618792480099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440966022621745861653399 2161449033932618792480099)
          ·
            refine ⟨3242173550898928188720149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161449033932618792480099 3242173550898928188720149)
            ·
              refine ⟨151976885198387258846257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3242173550898928188720149 151976885198387258846257)
              ·
                refine ⟨113982663898790444134693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151976885198387258846257 113982663898790444134693)
                ·
                  refine ⟨21371749481023208275255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113982663898790444134693 21371749481023208275255)
                  ·
                    rfl

theorem cell22_187296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_187296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187296 prefixEnd_187296 := by exact prefixLift 187296
  have htrace : WordTrace (prefixWord ++ tailWord_187296) baseStart_187296 baseEnd_187296 := by
    simpa [prefixWord, tailWord_187296, baseEnd_187296] using wordTrace_append hprefix tailTrace_187296
  have hstable : (prefixWord ++ tailWord_187296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187296).length < 2 ^ (prefixWord ++ tailWord_187296).sum := by decide
  have hdescent : baseEnd_187296 < baseStart_187296 := by decide
  rcases family_descends (prefixWord ++ tailWord_187296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187332 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_187332 : Nat := 118140960795 + 187332 * 2 ^ 59
def prefixEnd_187332 : Nat := 4983230072969 + 3 ^ 40 * 187332 * 2
def baseEnd_187332 : Nat := 64127571978777530925655

theorem tailTrace_187332 : CollatzResearch.WordTrace tailWord_187332 prefixEnd_187332 64127571978777530925655 := by
  unfold tailWord_187332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416279678667816301778125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4555039571557088402370833 3416279678667816301778125)
  ·
    refine ⟨1281104879500431113166797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3416279678667816301778125 1281104879500431113166797)
    ·
      refine ⟨480414329812661667437549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1281104879500431113166797 480414329812661667437549)
      ·
        refine ⟨180155373679748125289081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480414329812661667437549 180155373679748125289081)
        ·
          refine ⟨135116530259811093966811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180155373679748125289081 135116530259811093966811)
          ·
            refine ⟨202674795389716640950217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135116530259811093966811 202674795389716640950217)
            ·
              refine ⟨152006096542287480712663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202674795389716640950217 152006096542287480712663)
              ·
                refine ⟨228009144813431221068995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152006096542287480712663 228009144813431221068995)
                ·
                  refine ⟨342013717220146831603493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228009144813431221068995 342013717220146831603493)
                  ·
                    refine ⟨64127571978777530925655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342013717220146831603493 64127571978777530925655)
                    ·
                      rfl

theorem cell22_187332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_187332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187332 prefixEnd_187332 := by exact prefixLift 187332
  have htrace : WordTrace (prefixWord ++ tailWord_187332) baseStart_187332 baseEnd_187332 := by
    simpa [prefixWord, tailWord_187332, baseEnd_187332] using wordTrace_append hprefix tailTrace_187332
  have hstable : (prefixWord ++ tailWord_187332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187332).length < 2 ^ (prefixWord ++ tailWord_187332).sum := by decide
  have hdescent : baseEnd_187332 < baseStart_187332 := by decide
  rcases family_descends (prefixWord ++ tailWord_187332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187420 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_187420 : Nat := 118140960795 + 187420 * 2 ^ 59
def prefixEnd_187420 : Nat := 4983230072969 + 3 ^ 40 * 187420 * 2
def baseEnd_187420 : Nat := 21385898725724878241795

theorem tailTrace_187420 : CollatzResearch.WordTrace tailWord_187420 prefixEnd_187420 21385898725724878241795 := by
  unfold tailWord_187420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417884490508411816379857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4557179320677882421839809 3417884490508411816379857)
  ·
    refine ⟨2563413367881308862284893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3417884490508411816379857 2563413367881308862284893)
    ·
      refine ⟨961280012955490823356835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2563413367881308862284893 961280012955490823356835)
      ·
        refine ⟨1441920019433236235035253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961280012955490823356835 1441920019433236235035253)
        ·
          refine ⟨135180001821865897034555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1441920019433236235035253 135180001821865897034555)
          ·
            refine ⟨202770002732798845551833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135180001821865897034555 202770002732798845551833)
            ·
              refine ⟨152077502049599134163875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202770002732798845551833 152077502049599134163875)
              ·
                refine ⟨228116253074398701245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152077502049599134163875 228116253074398701245813)
                ·
                  refine ⟨21385898725724878241795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228116253074398701245813 21385898725724878241795)
                  ·
                    rfl

theorem cell22_187420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_187420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187420 prefixEnd_187420 := by exact prefixLift 187420
  have htrace : WordTrace (prefixWord ++ tailWord_187420) baseStart_187420 baseEnd_187420 := by
    simpa [prefixWord, tailWord_187420, baseEnd_187420] using wordTrace_append hprefix tailTrace_187420
  have hstable : (prefixWord ++ tailWord_187420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187420).length < 2 ^ (prefixWord ++ tailWord_187420).sum := by decide
  have hdescent : baseEnd_187420 < baseStart_187420 := by decide
  rcases family_descends (prefixWord ++ tailWord_187420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187429 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_187429 : Nat := 118140960795 + 187429 * 2 ^ 59
def prefixEnd_187429 : Nat := 4983230072969 + 3 ^ 40 * 187429 * 2
def baseEnd_187429 : Nat := 64160777061101611250357

theorem tailTrace_187429 : CollatzResearch.WordTrace tailWord_187429 prefixEnd_187429 64160777061101611250357 := by
  unfold tailWord_187429
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836097237984218169837341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4557398158656145446558227 6836097237984218169837341)
  ·
    refine ⟨2563536464244081813689003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6836097237984218169837341 2563536464244081813689003)
    ·
      refine ⟨3845304696366122720533505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563536464244081813689003 3845304696366122720533505)
      ·
        refine ⟨2883978522274592040400129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845304696366122720533505 2883978522274592040400129)
        ·
          refine ⟨2162983891705944030300097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2883978522274592040400129 2162983891705944030300097)
          ·
            refine ⟨1622237918779458022725073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2162983891705944030300097 1622237918779458022725073)
            ·
              refine ⟨1216678439084593517043805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622237918779458022725073 1216678439084593517043805)
              ·
                refine ⟨456254414656722568891427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216678439084593517043805 456254414656722568891427)
                ·
                  refine ⟨684381621985083853337141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456254414656722568891427 684381621985083853337141)
                  ·
                    refine ⟨64160777061101611250357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 684381621985083853337141 64160777061101611250357)
                    ·
                      rfl

theorem cell22_187429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_187429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187429 prefixEnd_187429 := by exact prefixLift 187429
  have htrace : WordTrace (prefixWord ++ tailWord_187429) baseStart_187429 baseEnd_187429 := by
    simpa [prefixWord, tailWord_187429, baseEnd_187429] using wordTrace_append hprefix tailTrace_187429
  have hstable : (prefixWord ++ tailWord_187429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187429).length < 2 ^ (prefixWord ++ tailWord_187429).sum := by decide
  have hdescent : baseEnd_187429 < baseStart_187429 := by decide
  rcases family_descends (prefixWord ++ tailWord_187429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187446 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_187446 : Nat := 118140960795 + 187446 * 2 ^ 59
def prefixEnd_187446 : Nat := 4983230072969 + 3 ^ 40 * 187446 * 2
def baseEnd_187446 : Nat := 64166596508519233575305

theorem tailTrace_187446 : CollatzResearch.WordTrace tailWord_187446 prefixEnd_187446 64166596508519233575305 := by
  unfold tailWord_187446
  simp only [CollatzResearch.WordTrace]
  refine ⟨427294829932664379575387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4557811519281753382137461 427294829932664379575387)
  ·
    refine ⟨640942244898996569363081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427294829932664379575387 640942244898996569363081)
    ·
      refine ⟨480706683674247427022311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 640942244898996569363081 480706683674247427022311)
      ·
        refine ⟨721060025511371140533467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480706683674247427022311 721060025511371140533467)
        ·
          refine ⟨1081590038267056710800201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721060025511371140533467 1081590038267056710800201)
          ·
            refine ⟨811192528700292533100151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081590038267056710800201 811192528700292533100151)
            ·
              refine ⟨1216788793050438799650227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811192528700292533100151 1216788793050438799650227)
              ·
                refine ⟨1825183189575658199475341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216788793050438799650227 1825183189575658199475341)
                ·
                  refine ⟨684443696090871824803253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1825183189575658199475341 684443696090871824803253)
                  ·
                    refine ⟨64166596508519233575305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 684443696090871824803253 64166596508519233575305)
                    ·
                      rfl

theorem cell22_187446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_187446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187446 prefixEnd_187446 := by exact prefixLift 187446
  have htrace : WordTrace (prefixWord ++ tailWord_187446) baseStart_187446 baseEnd_187446 := by
    simpa [prefixWord, tailWord_187446, baseEnd_187446] using wordTrace_append hprefix tailTrace_187446
  have hstable : (prefixWord ++ tailWord_187446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187446).length < 2 ^ (prefixWord ++ tailWord_187446).sum := by decide
  have hdescent : baseEnd_187446 < baseStart_187446 := by decide
  rcases family_descends (prefixWord ++ tailWord_187446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187463 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 2, 3]
def baseStart_187463 : Nat := 118140960795 + 187463 * 2 ^ 59
def prefixEnd_187463 : Nat := 4983230072969 + 3 ^ 40 * 187463 * 2
def baseEnd_187463 : Nat := 64172415955936855900253

theorem tailTrace_187463 : CollatzResearch.WordTrace tailWord_187463 prefixEnd_187463 64172415955936855900253 := by
  unfold tailWord_187463
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837337319861041976575043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4558224879907361317716695 6837337319861041976575043)
  ·
    refine ⟨10256005979791562964862565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6837337319861041976575043 10256005979791562964862565)
    ·
      refine ⟨1923001121210918055911731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10256005979791562964862565 1923001121210918055911731)
      ·
        refine ⟨2884501681816377083867597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923001121210918055911731 2884501681816377083867597)
        ·
          refine ⟨1081688130681141406450349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2884501681816377083867597 1081688130681141406450349)
          ·
            refine ⟨405633049005428027418881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1081688130681141406450349 405633049005428027418881)
            ·
              refine ⟨304224786754071020564161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405633049005428027418881 304224786754071020564161)
              ·
                refine ⟨228168590065553265423121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304224786754071020564161 228168590065553265423121)
                ·
                  refine ⟨171126442549164949067341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228168590065553265423121 171126442549164949067341)
                  ·
                    refine ⟨64172415955936855900253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171126442549164949067341 64172415955936855900253)
                    ·
                      rfl

theorem cell22_187463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_187463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187463 prefixEnd_187463 := by exact prefixLift 187463
  have htrace : WordTrace (prefixWord ++ tailWord_187463) baseStart_187463 baseEnd_187463 := by
    simpa [prefixWord, tailWord_187463, baseEnd_187463] using wordTrace_append hprefix tailTrace_187463
  have hstable : (prefixWord ++ tailWord_187463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187463).length < 2 ^ (prefixWord ++ tailWord_187463).sum := by decide
  have hdescent : baseEnd_187463 < baseStart_187463 := by decide
  rcases family_descends (prefixWord ++ tailWord_187463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187504 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_187504 : Nat := 118140960795 + 187504 * 2 ^ 59
def prefixEnd_187504 : Nat := 4983230072969 + 3 ^ 40 * 187504 * 2
def baseEnd_187504 : Nat := 21395483697942138541709

theorem tailTrace_187504 : CollatzResearch.WordTrace tailWord_187504 prefixEnd_187504 21395483697942138541709 := by
  unfold tailWord_187504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419416356356252989408783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4559221808475003985878377 3419416356356252989408783)
  ·
    refine ⟨5129124534534379484113175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3419416356356252989408783 5129124534534379484113175)
    ·
      refine ⟨7693686801801569226169763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5129124534534379484113175 7693686801801569226169763)
      ·
        refine ⟨11540530202702353839254645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693686801801569226169763 11540530202702353839254645)
        ·
          refine ⟨1081924706503345672430123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11540530202702353839254645 1081924706503345672430123)
          ·
            refine ⟨1622887059755018508645185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081924706503345672430123 1622887059755018508645185)
            ·
              refine ⟨1217165294816263881483889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622887059755018508645185 1217165294816263881483889)
              ·
                refine ⟨912873971112197911112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217165294816263881483889 912873971112197911112917)
                ·
                  refine ⟨21395483697942138541709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 912873971112197911112917 21395483697942138541709)
                  ·
                    rfl

theorem cell22_187504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_187504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187504 prefixEnd_187504 := by exact prefixLift 187504
  have htrace : WordTrace (prefixWord ++ tailWord_187504) baseStart_187504 baseEnd_187504 := by
    simpa [prefixWord, tailWord_187504, baseEnd_187504] using wordTrace_append hprefix tailTrace_187504
  have hstable : (prefixWord ++ tailWord_187504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187504).length < 2 ^ (prefixWord ++ tailWord_187504).sum := by decide
  have hdescent : baseEnd_187504 < baseStart_187504 := by decide
  rcases family_descends (prefixWord ++ tailWord_187504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187521 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 7]
def baseStart_187521 : Nat := 118140960795 + 187521 * 2 ^ 59
def prefixEnd_187521 : Nat := 4983230072969 + 3 ^ 40 * 187521 * 2
def baseEnd_187521 : Nat := 21397423513748012650025

theorem tailTrace_187521 : CollatzResearch.WordTrace tailWord_187521 prefixEnd_187521 21397423513748012650025 := by
  unfold tailWord_187521
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839452753650917882186417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4559635169100611921457611 6839452753650917882186417)
  ·
    refine ⟨5129589565238188411639813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6839452753650917882186417 5129589565238188411639813)
    ·
      refine ⟨961798043482160327182465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5129589565238188411639813 961798043482160327182465)
      ·
        refine ⟨721348532611620245386849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961798043482160327182465 721348532611620245386849)
        ·
          refine ⟨541011399458715184040137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721348532611620245386849 541011399458715184040137)
          ·
            refine ⟨405758549594036388030103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541011399458715184040137 405758549594036388030103)
            ·
              refine ⟨608637824391054582045155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405758549594036388030103 608637824391054582045155)
              ·
                refine ⟨912956736586581873067733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608637824391054582045155 912956736586581873067733)
                ·
                  refine ⟨21397423513748012650025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 912956736586581873067733 21397423513748012650025)
                  ·
                    rfl

theorem cell22_187521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_187521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187521 prefixEnd_187521 := by exact prefixLift 187521
  have htrace : WordTrace (prefixWord ++ tailWord_187521) baseStart_187521 baseEnd_187521 := by
    simpa [prefixWord, tailWord_187521, baseEnd_187521] using wordTrace_append hprefix tailTrace_187521
  have hstable : (prefixWord ++ tailWord_187521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187521).length < 2 ^ (prefixWord ++ tailWord_187521).sum := by decide
  have hdescent : baseEnd_187521 < baseStart_187521 := by decide
  rcases family_descends (prefixWord ++ tailWord_187521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187579 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_187579 : Nat := 118140960795 + 187579 * 2 ^ 59
def prefixEnd_187579 : Nat := 4983230072969 + 3 ^ 40 * 187579 * 2
def baseEnd_187579 : Nat := 64212125126551219999897

theorem tailTrace_187579 : CollatzResearch.WordTrace tailWord_187579 prefixEnd_187579 64212125126551219999897 := by
  unfold tailWord_187579
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841568187440793787797791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4561045458293862525198527 6841568187440793787797791)
  ·
    refine ⟨10262352281161190681696687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841568187440793787797791 10262352281161190681696687)
    ·
      refine ⟨15393528421741786022545031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262352281161190681696687 15393528421741786022545031)
      ·
        refine ⟨23090292632612679033817547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393528421741786022545031 23090292632612679033817547)
        ·
          refine ⟨34635438948919018550726321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23090292632612679033817547 34635438948919018550726321)
          ·
            refine ⟨25976579211689263913044741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34635438948919018550726321 25976579211689263913044741)
            ·
              refine ⟨4870608602191736983695889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25976579211689263913044741 4870608602191736983695889)
              ·
                refine ⟨3652956451643802737771917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870608602191736983695889 3652956451643802737771917)
                ·
                  refine ⟨1369858669366426026664469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3652956451643802737771917 1369858669366426026664469)
                  ·
                    refine ⟨64212125126551219999897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1369858669366426026664469 64212125126551219999897)
                    ·
                      rfl

theorem cell22_187579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_187579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187579 prefixEnd_187579 := by exact prefixLift 187579
  have htrace : WordTrace (prefixWord ++ tailWord_187579) baseStart_187579 baseEnd_187579 := by
    simpa [prefixWord, tailWord_187579, baseEnd_187579] using wordTrace_append hprefix tailTrace_187579
  have hstable : (prefixWord ++ tailWord_187579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187579).length < 2 ^ (prefixWord ++ tailWord_187579).sum := by decide
  have hdescent : baseEnd_187579 < baseStart_187579 := by decide
  rcases family_descends (prefixWord ++ tailWord_187579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187634 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_187634 : Nat := 118140960795 + 187634 * 2 ^ 59
def prefixEnd_187634 : Nat := 4983230072969 + 3 ^ 40 * 187634 * 2
def baseEnd_187634 : Nat := 21410317583516469958243

theorem tailTrace_187634 : CollatzResearch.WordTrace tailWord_187634 prefixEnd_187634 21410317583516469958243 := by
  unfold tailWord_187634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710893550560384545262489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4562382801494358787366637 1710893550560384545262489)
  ·
    refine ⟨1283170162920288408946867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1710893550560384545262489 1283170162920288408946867)
    ·
      refine ⟨1924755244380432613420301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283170162920288408946867 1924755244380432613420301)
      ·
        refine ⟨721783216642662230032613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1924755244380432613420301 721783216642662230032613)
        ·
          refine ⟨135334353120499168131115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 721783216642662230032613 135334353120499168131115)
          ·
            refine ⟨203001529680748752196673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135334353120499168131115 203001529680748752196673)
            ·
              refine ⟨152251147260561564147505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203001529680748752196673 152251147260561564147505)
              ·
                refine ⟨114188360445421173110629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152251147260561564147505 114188360445421173110629)
                ·
                  refine ⟨21410317583516469958243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114188360445421173110629 21410317583516469958243)
                  ·
                    rfl

theorem cell22_187634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_187634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187634 prefixEnd_187634 := by exact prefixLift 187634
  have htrace : WordTrace (prefixWord ++ tailWord_187634) baseStart_187634 baseEnd_187634 := by
    simpa [prefixWord, tailWord_187634, baseEnd_187634] using wordTrace_append hprefix tailTrace_187634
  have hstable : (prefixWord ++ tailWord_187634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187634).length < 2 ^ (prefixWord ++ tailWord_187634).sum := by decide
  have hdescent : baseEnd_187634 < baseStart_187634 := by decide
  rcases family_descends (prefixWord ++ tailWord_187634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187671 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_187671 : Nat := 118140960795 + 187671 * 2 ^ 59
def prefixEnd_187671 : Nat := 4983230072969 + 3 ^ 40 * 187671 * 2
def baseEnd_187671 : Nat := 64243618606693646699615

theorem tailTrace_187671 : CollatzResearch.WordTrace tailWord_187671 prefixEnd_187671 64243618606693646699615 := by
  unfold tailWord_187671
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844923703107493500146867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4563282468738329000097911 6844923703107493500146867)
  ·
    refine ⟨10267385554661240250220301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6844923703107493500146867 10267385554661240250220301)
    ·
      refine ⟨3850269582997965093832613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10267385554661240250220301 3850269582997965093832613)
      ·
        refine ⟨721925546812118455093615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3850269582997965093832613 721925546812118455093615)
        ·
          refine ⟨1082888320218177682640423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721925546812118455093615 1082888320218177682640423)
          ·
            refine ⟨1624332480327266523960635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082888320218177682640423 1624332480327266523960635)
            ·
              refine ⟨2436498720490899785940953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624332480327266523960635 2436498720490899785940953)
              ·
                refine ⟨1827374040368174839455715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436498720490899785940953 1827374040368174839455715)
                ·
                  refine ⟨2741061060552262259183573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827374040368174839455715 2741061060552262259183573)
                  ·
                    refine ⟨64243618606693646699615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2741061060552262259183573 64243618606693646699615)
                    ·
                      rfl

theorem cell22_187671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_187671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187671 prefixEnd_187671 := by exact prefixLift 187671
  have htrace : WordTrace (prefixWord ++ tailWord_187671) baseStart_187671 baseEnd_187671 := by
    simpa [prefixWord, tailWord_187671, baseEnd_187671] using wordTrace_append hprefix tailTrace_187671
  have hstable : (prefixWord ++ tailWord_187671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187671).length < 2 ^ (prefixWord ++ tailWord_187671).sum := by decide
  have hdescent : baseEnd_187671 < baseStart_187671 := by decide
  rcases family_descends (prefixWord ++ tailWord_187671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187677 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_187677 : Nat := 118140960795 + 187677 * 2 ^ 59
def prefixEnd_187677 : Nat := 4983230072969 + 3 ^ 40 * 187677 * 2
def baseEnd_187677 : Nat := 64245672529311631049597

theorem tailTrace_187677 : CollatzResearch.WordTrace tailWord_187677 prefixEnd_187677 64245672529311631049597 := by
  unfold tailWord_187677
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845142541085756524865285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4563428360723837683243523 6845142541085756524865285)
  ·
    refine ⟨1283464226453579348412241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6845142541085756524865285 1283464226453579348412241)
    ·
      refine ⟨962598169840184511309181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1283464226453579348412241 962598169840184511309181)
      ·
        refine ⟨360974313690069191740943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 962598169840184511309181 360974313690069191740943)
        ·
          refine ⟨541461470535103787611415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360974313690069191740943 541461470535103787611415)
          ·
            refine ⟨812192205802655681417123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541461470535103787611415 812192205802655681417123)
            ·
              refine ⟨1218288308703983522125685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812192205802655681417123 1218288308703983522125685)
              ·
                refine ⟨114214528940998455199283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1218288308703983522125685 114214528940998455199283)
                ·
                  refine ⟨171321793411497682798925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114214528940998455199283 171321793411497682798925)
                  ·
                    refine ⟨64245672529311631049597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171321793411497682798925 64245672529311631049597)
                    ·
                      rfl

theorem cell22_187677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_187677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187677 prefixEnd_187677 := by exact prefixLift 187677
  have htrace : WordTrace (prefixWord ++ tailWord_187677) baseStart_187677 baseEnd_187677 := by
    simpa [prefixWord, tailWord_187677, baseEnd_187677] using wordTrace_append hprefix tailTrace_187677
  have hstable : (prefixWord ++ tailWord_187677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187677).length < 2 ^ (prefixWord ++ tailWord_187677).sum := by decide
  have hdescent : baseEnd_187677 < baseStart_187677 := by decide
  rcases family_descends (prefixWord ++ tailWord_187677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187688 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_187688 : Nat := 118140960795 + 187688 * 2 ^ 59
def prefixEnd_187688 : Nat := 4983230072969 + 3 ^ 40 * 187688 * 2
def baseEnd_187688 : Nat := 64249438054111269024563

theorem tailTrace_187688 : CollatzResearch.WordTrace tailWord_187688 prefixEnd_187688 64249438054111269024563 := by
  unfold tailWord_187688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3422771872022952701757859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4563695829363936935677145 3422771872022952701757859)
  ·
    refine ⟨5134157808034429052636789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3422771872022952701757859 5134157808034429052636789)
    ·
      refine ⟨481327294503227723684699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5134157808034429052636789 481327294503227723684699)
      ·
        refine ⟨721990941754841585527049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481327294503227723684699 721990941754841585527049)
        ·
          refine ⟨541493206316131189145287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721990941754841585527049 541493206316131189145287)
          ·
            refine ⟨812239809474196783717931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541493206316131189145287 812239809474196783717931)
            ·
              refine ⟨1218359714211295175576897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812239809474196783717931 1218359714211295175576897)
              ·
                refine ⟨913769785658471381682673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218359714211295175576897 913769785658471381682673)
                ·
                  refine ⟨685327339243853536262005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913769785658471381682673 685327339243853536262005)
                  ·
                    refine ⟨64249438054111269024563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 685327339243853536262005 64249438054111269024563)
                    ·
                      rfl

theorem cell22_187688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_187688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187688 prefixEnd_187688 := by exact prefixLift 187688
  have htrace : WordTrace (prefixWord ++ tailWord_187688) baseStart_187688 baseEnd_187688 := by
    simpa [prefixWord, tailWord_187688, baseEnd_187688] using wordTrace_append hprefix tailTrace_187688
  have hstable : (prefixWord ++ tailWord_187688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187688).length < 2 ^ (prefixWord ++ tailWord_187688).sum := by decide
  have hdescent : baseEnd_187688 < baseStart_187688 := by decide
  rcases family_descends (prefixWord ++ tailWord_187688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187690 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_187690 : Nat := 118140960795 + 187690 * 2 ^ 59
def prefixEnd_187690 : Nat := 4983230072969 + 3 ^ 40 * 187690 * 2
def baseEnd_187690 : Nat := 21416707564994643491519

theorem tailTrace_187690 : CollatzResearch.WordTrace tailWord_187690 prefixEnd_187690 21416707564994643491519 := by
  unfold tailWord_187690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711404172509664936272131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4563744460025773163392349 1711404172509664936272131)
  ·
    refine ⟨2567106258764497404408197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711404172509664936272131 2567106258764497404408197)
    ·
      refine ⟨481332423518343263326537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2567106258764497404408197 481332423518343263326537)
      ·
        refine ⟨360999317638757447494903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481332423518343263326537 360999317638757447494903)
        ·
          refine ⟨541498976458136171242355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360999317638757447494903 541498976458136171242355)
          ·
            refine ⟨812248464687204256863533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541498976458136171242355 812248464687204256863533)
            ·
              refine ⟨304593174257701596323825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812248464687204256863533 304593174257701596323825)
              ·
                refine ⟨228444880693276197242869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304593174257701596323825 228444880693276197242869)
                ·
                  refine ⟨21416707564994643491519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228444880693276197242869 21416707564994643491519)
                  ·
                    rfl

theorem cell22_187690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_187690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187690 prefixEnd_187690 := by exact prefixLift 187690
  have htrace : WordTrace (prefixWord ++ tailWord_187690) baseStart_187690 baseEnd_187690 := by
    simpa [prefixWord, tailWord_187690, baseEnd_187690] using wordTrace_append hprefix tailTrace_187690
  have hstable : (prefixWord ++ tailWord_187690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187690).length < 2 ^ (prefixWord ++ tailWord_187690).sum := by decide
  have hdescent : baseEnd_187690 < baseStart_187690 := by decide
  rcases family_descends (prefixWord ++ tailWord_187690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187731 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_187731 : Nat := 118140960795 + 187731 * 2 ^ 59
def prefixEnd_187731 : Nat := 4983230072969 + 3 ^ 40 * 187731 * 2
def baseEnd_187731 : Nat := 64264157832873490199431

theorem tailTrace_187731 : CollatzResearch.WordTrace tailWord_187731 prefixEnd_187731 64264157832873490199431 := by
  unfold tailWord_187731
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847112082890123747331047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4564741388593415831554031 6847112082890123747331047)
  ·
    refine ⟨10270668124335185620996571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6847112082890123747331047 10270668124335185620996571)
    ·
      refine ⟨15406002186502778431494857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10270668124335185620996571 15406002186502778431494857)
      ·
        refine ⟨11554501639877083823621143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15406002186502778431494857 11554501639877083823621143)
        ·
          refine ⟨17331752459815625735431715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11554501639877083823621143 17331752459815625735431715)
          ·
            refine ⟨25997628689723438603147573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17331752459815625735431715 25997628689723438603147573)
            ·
              refine ⟨2437277689661572369045085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25997628689723438603147573 2437277689661572369045085)
              ·
                refine ⟨913979133623089638391907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2437277689661572369045085 913979133623089638391907)
                ·
                  refine ⟨1370968700434634457587861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913979133623089638391907 1370968700434634457587861)
                  ·
                    refine ⟨64264157832873490199431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1370968700434634457587861 64264157832873490199431)
                    ·
                      rfl

theorem cell22_187731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_187731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187731 prefixEnd_187731 := by exact prefixLift 187731
  have htrace : WordTrace (prefixWord ++ tailWord_187731) baseStart_187731 baseEnd_187731 := by
    simpa [prefixWord, tailWord_187731, baseEnd_187731] using wordTrace_append hprefix tailTrace_187731
  have hstable : (prefixWord ++ tailWord_187731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187731).length < 2 ^ (prefixWord ++ tailWord_187731).sum := by decide
  have hdescent : baseEnd_187731 < baseStart_187731 := by decide
  rcases family_descends (prefixWord ++ tailWord_187731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187735 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 4]
def baseStart_187735 : Nat := 118140960795 + 187735 * 2 ^ 59
def prefixEnd_187735 : Nat := 4983230072969 + 3 ^ 40 * 187735 * 2
def baseEnd_187735 : Nat := 21421842371539604366473

theorem tailTrace_187735 : CollatzResearch.WordTrace tailWord_187735 prefixEnd_187735 21421842371539604366473 := by
  unfold tailWord_187735
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847257974875632430476659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4564838649917088286984439 6847257974875632430476659)
  ·
    refine ⟨10270886962313448645714989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6847257974875632430476659 10270886962313448645714989)
    ·
      refine ⟨3851582610867543242143121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10270886962313448645714989 3851582610867543242143121)
      ·
        refine ⟨2888686958150657431607341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3851582610867543242143121 2888686958150657431607341)
        ·
          refine ⟨1083257609306496536852753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2888686958150657431607341 1083257609306496536852753)
          ·
            refine ⟨812443206979872402639565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083257609306496536852753 812443206979872402639565)
            ·
              refine ⟨304666202617452150989837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812443206979872402639565 304666202617452150989837)
              ·
                refine ⟨114249825981544556621189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304666202617452150989837 114249825981544556621189)
                ·
                  refine ⟨21421842371539604366473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114249825981544556621189 21421842371539604366473)
                  ·
                    rfl

theorem cell22_187735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 4].length) (baseStart_187735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187735 prefixEnd_187735 := by exact prefixLift 187735
  have htrace : WordTrace (prefixWord ++ tailWord_187735) baseStart_187735 baseEnd_187735 := by
    simpa [prefixWord, tailWord_187735, baseEnd_187735] using wordTrace_append hprefix tailTrace_187735
  have hstable : (prefixWord ++ tailWord_187735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187735).length < 2 ^ (prefixWord ++ tailWord_187735).sum := by decide
  have hdescent : baseEnd_187735 < baseStart_187735 := by decide
  rcases family_descends (prefixWord ++ tailWord_187735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187748 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_187748 : Nat := 118140960795 + 187748 * 2 ^ 59
def prefixEnd_187748 : Nat := 4983230072969 + 3 ^ 40 * 187748 * 2
def baseEnd_187748 : Nat := 64269977280291112524379

theorem tailTrace_187748 : CollatzResearch.WordTrace tailWord_187748 prefixEnd_187748 64269977280291112524379 := by
  unfold tailWord_187748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423866061914267825349949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4565154749219023767133265 3423866061914267825349949)
  ·
    refine ⟨1283949773217850434506231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3423866061914267825349949 1283949773217850434506231)
    ·
      refine ⟨1925924659826775651759347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283949773217850434506231 1925924659826775651759347)
      ·
        refine ⟨2888886989740163477639021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925924659826775651759347 2888886989740163477639021)
        ·
          refine ⟨1083332621152561304114633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2888886989740163477639021 1083332621152561304114633)
          ·
            refine ⟨812499465864420978085975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083332621152561304114633 812499465864420978085975)
            ·
              refine ⟨1218749198796631467128963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812499465864420978085975 1218749198796631467128963)
              ·
                refine ⟨1828123798194947200693445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218749198796631467128963 1828123798194947200693445)
                ·
                  refine ⟨342773212161552600130021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828123798194947200693445 342773212161552600130021)
                  ·
                    refine ⟨64269977280291112524379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342773212161552600130021 64269977280291112524379)
                    ·
                      rfl

theorem cell22_187748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_187748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187748 prefixEnd_187748 := by exact prefixLift 187748
  have htrace : WordTrace (prefixWord ++ tailWord_187748) baseStart_187748 baseEnd_187748 := by
    simpa [prefixWord, tailWord_187748, baseEnd_187748] using wordTrace_append hprefix tailTrace_187748
  have hstable : (prefixWord ++ tailWord_187748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187748).length < 2 ^ (prefixWord ++ tailWord_187748).sum := by decide
  have hdescent : baseEnd_187748 < baseStart_187748 := by decide
  rcases family_descends (prefixWord ++ tailWord_187748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187752 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_187752 : Nat := 118140960795 + 187752 * 2 ^ 59
def prefixEnd_187752 : Nat := 4983230072969 + 3 ^ 40 * 187752 * 2
def baseEnd_187752 : Nat := 21423782187345478474789

theorem tailTrace_187752 : CollatzResearch.WordTrace tailWord_187752 prefixEnd_187752 21423782187345478474789 := by
  unfold tailWord_187752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423939007907022166922755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4565252010542696222563673 3423939007907022166922755)
  ·
    refine ⟨5135908511860533250384133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423939007907022166922755 5135908511860533250384133)
    ·
      refine ⟨962982845973849984447025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5135908511860533250384133 962982845973849984447025)
      ·
        refine ⟨722237134480387488335269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962982845973849984447025 722237134480387488335269)
        ·
          refine ⟨135419462715072654062863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 722237134480387488335269 135419462715072654062863)
          ·
            refine ⟨203129194072608981094295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135419462715072654062863 203129194072608981094295)
            ·
              refine ⟨304693791108913471641443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203129194072608981094295 304693791108913471641443)
              ·
                refine ⟨457040686663370207462165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304693791108913471641443 457040686663370207462165)
                ·
                  refine ⟨21423782187345478474789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 457040686663370207462165 21423782187345478474789)
                  ·
                    rfl

theorem cell22_187752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_187752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187752 prefixEnd_187752 := by exact prefixLift 187752
  have htrace : WordTrace (prefixWord ++ tailWord_187752) baseStart_187752 baseEnd_187752 := by
    simpa [prefixWord, tailWord_187752, baseEnd_187752] using wordTrace_append hprefix tailTrace_187752
  have hstable : (prefixWord ++ tailWord_187752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187752).length < 2 ^ (prefixWord ++ tailWord_187752).sum := by decide
  have hdescent : baseEnd_187752 < baseStart_187752 := by decide
  rcases family_descends (prefixWord ++ tailWord_187752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187883 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_187883 : Nat := 118140960795 + 187883 * 2 ^ 59
def prefixEnd_187883 : Nat := 4983230072969 + 3 ^ 40 * 187883 * 2
def baseEnd_187883 : Nat := 64316190539195760398965

theorem tailTrace_187883 : CollatzResearch.WordTrace tailWord_187883 prefixEnd_187883 64316190539195760398965 := by
  unfold tailWord_187883
  simp only [CollatzResearch.WordTrace]
  refine ⟨6852655978339453706864303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4568437318892969137909535 6852655978339453706864303)
  ·
    refine ⟨10278983967509180560296455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6852655978339453706864303 10278983967509180560296455)
    ·
      refine ⟨15418475951263770840444683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10278983967509180560296455 15418475951263770840444683)
      ·
        refine ⟨23127713926895656260667025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15418475951263770840444683 23127713926895656260667025)
        ·
          refine ⟨17345785445171742195500269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23127713926895656260667025 17345785445171742195500269)
          ·
            refine ⟨6504669541939403323312601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17345785445171742195500269 6504669541939403323312601)
            ·
              refine ⟨4878502156454552492484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6504669541939403323312601 4878502156454552492484451)
              ·
                refine ⟨7317753234681828738726677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878502156454552492484451 7317753234681828738726677)
                ·
                  refine ⟨343019682875710722127813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7317753234681828738726677 343019682875710722127813)
                  ·
                    refine ⟨64316190539195760398965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343019682875710722127813 64316190539195760398965)
                    ·
                      rfl

theorem cell22_187883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_187883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187883 prefixEnd_187883 := by exact prefixLift 187883
  have htrace : WordTrace (prefixWord ++ tailWord_187883) baseStart_187883 baseEnd_187883 := by
    simpa [prefixWord, tailWord_187883, baseEnd_187883] using wordTrace_append hprefix tailTrace_187883
  have hstable : (prefixWord ++ tailWord_187883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187883).length < 2 ^ (prefixWord ++ tailWord_187883).sum := by decide
  have hdescent : baseEnd_187883 < baseStart_187883 := by decide
  rcases family_descends (prefixWord ++ tailWord_187883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187898 : List Nat := [3, 1, 1, 1, 1, 2, 5, 8]
def baseStart_187898 : Nat := 118140960795 + 187898 * 2 ^ 59
def prefixEnd_187898 : Nat := 4983230072969 + 3 ^ 40 * 187898 * 2
def baseEnd_187898 : Nat := 7146813927304524585991

theorem tailTrace_187898 : CollatzResearch.WordTrace tailWord_187898 prefixEnd_187898 7146813927304524585991 := by
  unfold tailWord_187898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713300768321277817165087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4568802048856740845773565 1713300768321277817165087)
  ·
    refine ⟨2569951152481916725747631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1713300768321277817165087 2569951152481916725747631)
    ·
      refine ⟨3854926728722875088621447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2569951152481916725747631 3854926728722875088621447)
      ·
        refine ⟨5782390093084312632932171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854926728722875088621447 5782390093084312632932171)
        ·
          refine ⟨8673585139626468949398257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782390093084312632932171 8673585139626468949398257)
          ·
            refine ⟨6505188854719851712048693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8673585139626468949398257 6505188854719851712048693)
            ·
              refine ⟨609861455129986098004565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6505188854719851712048693 609861455129986098004565)
              ·
                refine ⟨7146813927304524585991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 609861455129986098004565 7146813927304524585991)
                ·
                  rfl

theorem cell22_187898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_187898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187898 prefixEnd_187898 := by exact prefixLift 187898
  have htrace : WordTrace (prefixWord ++ tailWord_187898) baseStart_187898 baseEnd_187898 := by
    simpa [prefixWord, tailWord_187898, baseEnd_187898] using wordTrace_append hprefix tailTrace_187898
  have hstable : (prefixWord ++ tailWord_187898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187898).length < 2 ^ (prefixWord ++ tailWord_187898).sum := by decide
  have hdescent : baseEnd_187898 < baseStart_187898 := by decide
  rcases family_descends (prefixWord ++ tailWord_187898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187915 : List Nat := [1, 1, 1, 1, 8, 2, 8]
def baseStart_187915 : Nat := 118140960795 + 187915 * 2 ^ 59
def prefixEnd_187915 : Nat := 4983230072969 + 3 ^ 40 * 187915 * 2
def baseEnd_187915 : Nat := 2382486844191049762921

theorem tailTrace_187915 : CollatzResearch.WordTrace tailWord_187915 prefixEnd_187915 2382486844191049762921 := by
  unfold tailWord_187915
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853823114223523172029199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4569215409482348781352799 6853823114223523172029199)
  ·
    refine ⟨10280734671335284758043799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6853823114223523172029199 10280734671335284758043799)
    ·
      refine ⟨15421102007002927137065699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10280734671335284758043799 15421102007002927137065699)
      ·
        refine ⟨23131653010504390705598549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15421102007002927137065699 23131653010504390705598549)
        ·
          refine ⟨271074058716848328581233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 23131653010504390705598549 271074058716848328581233)
          ·
            refine ⟨203305544037636246435925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271074058716848328581233 203305544037636246435925)
            ·
              refine ⟨2382486844191049762921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 203305544037636246435925 2382486844191049762921)
              ·
                rfl

theorem cell22_187915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 8].length) (baseStart_187915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187915 prefixEnd_187915 := by exact prefixLift 187915
  have htrace : WordTrace (prefixWord ++ tailWord_187915) baseStart_187915 baseEnd_187915 := by
    simpa [prefixWord, tailWord_187915, baseEnd_187915] using wordTrace_append hprefix tailTrace_187915
  have hstable : (prefixWord ++ tailWord_187915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187915).length < 2 ^ (prefixWord ++ tailWord_187915).sum := by decide
  have hdescent : baseEnd_187915 < baseStart_187915 := by decide
  rcases family_descends (prefixWord ++ tailWord_187915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187936 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_187936 : Nat := 118140960795 + 187936 * 2 ^ 59
def prefixEnd_187936 : Nat := 4983230072969 + 3 ^ 40 * 187936 * 2
def baseEnd_187936 : Nat := 64334333522321288823803

theorem tailTrace_187936 : CollatzResearch.WordTrace tailWord_187936 prefixEnd_187936 64334333522321288823803 := by
  unfold tailWord_187936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427294523573721879271831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4569726031431629172362441 3427294523573721879271831)
  ·
    refine ⟨5140941785360582818907747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3427294523573721879271831 5140941785360582818907747)
    ·
      refine ⟨7711412678040874228361621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140941785360582818907747 7711412678040874228361621)
      ·
        refine ⟨361472469283165979454451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7711412678040874228361621 361472469283165979454451)
        ·
          refine ⟨542208703924748969181677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361472469283165979454451 542208703924748969181677)
          ·
            refine ⟨203328263971780863443129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 542208703924748969181677 203328263971780863443129)
            ·
              refine ⟨152496197978835647582347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203328263971780863443129 152496197978835647582347)
              ·
                refine ⟨228744296968253471373521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152496197978835647582347 228744296968253471373521)
                ·
                  refine ⟨171558222726190103530141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228744296968253471373521 171558222726190103530141)
                  ·
                    refine ⟨64334333522321288823803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171558222726190103530141 64334333522321288823803)
                    ·
                      rfl

theorem cell22_187936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_187936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_187936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_187936 prefixEnd_187936 := by exact prefixLift 187936
  have htrace : WordTrace (prefixWord ++ tailWord_187936) baseStart_187936 baseEnd_187936 := by
    simpa [prefixWord, tailWord_187936, baseEnd_187936] using wordTrace_append hprefix tailTrace_187936
  have hstable : (prefixWord ++ tailWord_187936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187936).length < 2 ^ (prefixWord ++ tailWord_187936).sum := by decide
  have hdescent : baseEnd_187936 < baseStart_187936 := by decide
  rcases family_descends (prefixWord ++ tailWord_187936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188005 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 8]
def baseStart_188005 : Nat := 118140960795 + 188005 * 2 ^ 59
def prefixEnd_188005 : Nat := 4983230072969 + 3 ^ 40 * 188005 * 2
def baseEnd_188005 : Nat := 21452651210809369616197

theorem tailTrace_188005 : CollatzResearch.WordTrace tailWord_188005 prefixEnd_188005 21452651210809369616197 := by
  unfold tailWord_188005
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857105683897468542805469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4571403789264979028536979 6857105683897468542805469)
  ·
    refine ⟨2571414631461550703552051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6857105683897468542805469 2571414631461550703552051)
    ·
      refine ⟨3857121947192326055328077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571414631461550703552051 3857121947192326055328077)
      ·
        refine ⟨1446420730197122270748029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3857121947192326055328077 1446420730197122270748029)
        ·
          refine ⟨542407773823920851530511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1446420730197122270748029 542407773823920851530511)
          ·
            refine ⟨813611660735881277295767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542407773823920851530511 813611660735881277295767)
            ·
              refine ⟨1220417491103821915943651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813611660735881277295767 1220417491103821915943651)
              ·
                refine ⟨1830626236655732873915477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220417491103821915943651 1830626236655732873915477)
                ·
                  refine ⟨21452651210809369616197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1830626236655732873915477 21452651210809369616197)
                  ·
                    rfl

theorem cell22_188005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_188005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188005 prefixEnd_188005 := by exact prefixLift 188005
  have htrace : WordTrace (prefixWord ++ tailWord_188005) baseStart_188005 baseEnd_188005 := by
    simpa [prefixWord, tailWord_188005, baseEnd_188005] using wordTrace_append hprefix tailTrace_188005
  have hstable : (prefixWord ++ tailWord_188005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188005).length < 2 ^ (prefixWord ++ tailWord_188005).sum := by decide
  have hdescent : baseEnd_188005 < baseStart_188005 := by decide
  rcases family_descends (prefixWord ++ tailWord_188005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188035 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_188035 : Nat := 118140960795 + 188035 * 2 ^ 59
def prefixEnd_188035 : Nat := 4983230072969 + 3 ^ 40 * 188035 * 2
def baseEnd_188035 : Nat := 64368223245518030598499

theorem tailTrace_188035 : CollatzResearch.WordTrace tailWord_188035 prefixEnd_188035 64368223245518030598499 := by
  unfold tailWord_188035
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858199873788783666397559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572133249192522444265039 6858199873788783666397559)
  ·
    refine ⟨10287299810683175499596339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6858199873788783666397559 10287299810683175499596339)
    ·
      refine ⟨15430949716024763249394509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10287299810683175499596339 15430949716024763249394509)
      ·
        refine ⟨5786606143509286218522941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15430949716024763249394509 5786606143509286218522941)
        ·
          refine ⟨2169977303815982331946103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5786606143509286218522941 2169977303815982331946103)
          ·
            refine ⟨3254965955723973497919155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169977303815982331946103 3254965955723973497919155)
            ·
              refine ⟨4882448933585960246878733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254965955723973497919155 4882448933585960246878733)
              ·
                refine ⟨1830918350094735092579525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4882448933585960246878733 1830918350094735092579525)
                ·
                  refine ⟨343297190642762829858661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830918350094735092579525 343297190642762829858661)
                  ·
                    refine ⟨64368223245518030598499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343297190642762829858661 64368223245518030598499)
                    ·
                      rfl

theorem cell22_188035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_188035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188035 prefixEnd_188035 := by exact prefixLift 188035
  have htrace : WordTrace (prefixWord ++ tailWord_188035) baseStart_188035 baseEnd_188035 := by
    simpa [prefixWord, tailWord_188035, baseEnd_188035] using wordTrace_append hprefix tailTrace_188035
  have hstable : (prefixWord ++ tailWord_188035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188035).length < 2 ^ (prefixWord ++ tailWord_188035).sum := by decide
  have hdescent : baseEnd_188035 < baseStart_188035 := by decide
  rcases family_descends (prefixWord ++ tailWord_188035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188037 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_188037 : Nat := 118140960795 + 188037 * 2 ^ 59
def prefixEnd_188037 : Nat := 4983230072969 + 3 ^ 40 * 188037 * 2
def baseEnd_188037 : Nat := 64368907886390692048493

theorem tailTrace_188037 : CollatzResearch.WordTrace tailWord_188037 prefixEnd_188037 64368907886390692048493 := by
  unfold tailWord_188037
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858272819781538007970365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572181879854358671980243 6858272819781538007970365)
  ·
    refine ⟨2571852307418076752988887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6858272819781538007970365 2571852307418076752988887)
    ·
      refine ⟨3857778461127115129483331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571852307418076752988887 3857778461127115129483331)
      ·
        refine ⟨5786667691690672694224997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857778461127115129483331 5786667691690672694224997)
        ·
          refine ⟨1085000192192001130167187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5786667691690672694224997 1085000192192001130167187)
          ·
            refine ⟨1627500288288001695250781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085000192192001130167187 1627500288288001695250781)
            ·
              refine ⟨610312608108000635719043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1627500288288001695250781 610312608108000635719043)
              ·
                refine ⟨915468912162000953578565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610312608108000635719043 915468912162000953578565)
                ·
                  refine ⟨171650421030375178795981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915468912162000953578565 171650421030375178795981)
                  ·
                    refine ⟨64368907886390692048493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171650421030375178795981 64368907886390692048493)
                    ·
                      rfl

theorem cell22_188037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_188037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188037 prefixEnd_188037 := by exact prefixLift 188037
  have htrace : WordTrace (prefixWord ++ tailWord_188037) baseStart_188037 baseEnd_188037 := by
    simpa [prefixWord, tailWord_188037, baseEnd_188037] using wordTrace_append hprefix tailTrace_188037
  have hstable : (prefixWord ++ tailWord_188037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188037).length < 2 ^ (prefixWord ++ tailWord_188037).sum := by decide
  have hdescent : baseEnd_188037 < baseStart_188037 := by decide
  rcases family_descends (prefixWord ++ tailWord_188037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188082 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_188082 : Nat := 118140960795 + 188082 * 2 ^ 59
def prefixEnd_188082 : Nat := 4983230072969 + 3 ^ 40 * 188082 * 2
def baseEnd_188082 : Nat := 64384312306025574673355

theorem tailTrace_188082 : CollatzResearch.WordTrace tailWord_188082 prefixEnd_188082 64384312306025574673355 := by
  unfold tailWord_188082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714978526154627673339625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4573276069745673795572333 1714978526154627673339625)
  ·
    refine ⟨1286233894615970755004719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1714978526154627673339625 1286233894615970755004719)
    ·
      refine ⟨1929350841923956132507079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286233894615970755004719 1929350841923956132507079)
      ·
        refine ⟨2894026262885934198760619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929350841923956132507079 2894026262885934198760619)
        ·
          refine ⟨4341039394328901298140929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894026262885934198760619 4341039394328901298140929)
          ·
            refine ⟨3255779545746675973605697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4341039394328901298140929 3255779545746675973605697)
            ·
              refine ⟨2441834659310006980204273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255779545746675973605697 2441834659310006980204273)
              ·
                refine ⟨1831375994482505235153205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441834659310006980204273 1831375994482505235153205)
                ·
                  refine ⟨171691499482734865795613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831375994482505235153205 171691499482734865795613)
                  ·
                    refine ⟨64384312306025574673355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171691499482734865795613 64384312306025574673355)
                    ·
                      rfl

theorem cell22_188082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_188082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188082 prefixEnd_188082 := by exact prefixLift 188082
  have htrace : WordTrace (prefixWord ++ tailWord_188082) baseStart_188082 baseEnd_188082 := by
    simpa [prefixWord, tailWord_188082, baseEnd_188082] using wordTrace_append hprefix tailTrace_188082
  have hstable : (prefixWord ++ tailWord_188082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188082).length < 2 ^ (prefixWord ++ tailWord_188082).sum := by decide
  have hdescent : baseEnd_188082 < baseStart_188082 := by decide
  rcases family_descends (prefixWord ++ tailWord_188082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188086 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_188086 : Nat := 118140960795 + 188086 * 2 ^ 59
def prefixEnd_188086 : Nat := 4983230072969 + 3 ^ 40 * 188086 * 2
def baseEnd_188086 : Nat := 64385681587770897573343

theorem tailTrace_188086 : CollatzResearch.WordTrace tailWord_188086 prefixEnd_188086 64385681587770897573343 := by
  unfold tailWord_188086
  simp only [CollatzResearch.WordTrace]
  refine ⟨428753749787751211031507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4573373331069346251002741 428753749787751211031507)
  ·
    refine ⟨643130624681626816547261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428753749787751211031507 643130624681626816547261)
    ·
      refine ⟨241173984255610056205223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 643130624681626816547261 241173984255610056205223)
      ·
        refine ⟨361760976383415084307835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241173984255610056205223 361760976383415084307835)
        ·
          refine ⟨542641464575122626461753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361760976383415084307835 542641464575122626461753)
          ·
            refine ⟨406981098431341969846315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542641464575122626461753 406981098431341969846315)
            ·
              refine ⟨610471647647012954769473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406981098431341969846315 610471647647012954769473)
              ·
                refine ⟨457853735735259716077105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610471647647012954769473 457853735735259716077105)
                ·
                  refine ⟨343390301801444787057829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457853735735259716077105 343390301801444787057829)
                  ·
                    refine ⟨64385681587770897573343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343390301801444787057829 64385681587770897573343)
                    ·
                      rfl

theorem cell22_188086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_188086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188086 prefixEnd_188086 := by exact prefixLift 188086
  have htrace : WordTrace (prefixWord ++ tailWord_188086) baseStart_188086 baseEnd_188086 := by
    simpa [prefixWord, tailWord_188086, baseEnd_188086] using wordTrace_append hprefix tailTrace_188086
  have hstable : (prefixWord ++ tailWord_188086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188086).length < 2 ^ (prefixWord ++ tailWord_188086).sum := by decide
  have hdescent : baseEnd_188086 < baseStart_188086 := by decide
  rcases family_descends (prefixWord ++ tailWord_188086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188095 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 7]
def baseStart_188095 : Nat := 118140960795 + 188095 * 2 ^ 59
def prefixEnd_188095 : Nat := 4983230072969 + 3 ^ 40 * 188095 * 2
def baseEnd_188095 : Nat := 21462920823899291366105

theorem tailTrace_188095 : CollatzResearch.WordTrace tailWord_188095 prefixEnd_188095 21462920823899291366105 := by
  unfold tailWord_188095
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860388253571413913581739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4573592169047609275721159 6860388253571413913581739)
  ·
    refine ⟨10290582380357120870372609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860388253571413913581739 10290582380357120870372609)
    ·
      refine ⟨7717936785267840652779457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10290582380357120870372609 7717936785267840652779457)
      ·
        refine ⟨5788452588950880489584593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7717936785267840652779457 5788452588950880489584593)
        ·
          refine ⟨4341339441713160367188445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788452588950880489584593 4341339441713160367188445)
          ·
            refine ⟨1628002290642435137695667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4341339441713160367188445 1628002290642435137695667)
            ·
              refine ⟨2442003435963652706543501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628002290642435137695667 2442003435963652706543501)
              ·
                refine ⟨915751288486369764953813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2442003435963652706543501 915751288486369764953813)
                ·
                  refine ⟨21462920823899291366105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 915751288486369764953813 21462920823899291366105)
                  ·
                    rfl

theorem cell22_188095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_188095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188095 prefixEnd_188095 := by exact prefixLift 188095
  have htrace : WordTrace (prefixWord ++ tailWord_188095) baseStart_188095 baseEnd_188095 := by
    simpa [prefixWord, tailWord_188095, baseEnd_188095] using wordTrace_append hprefix tailTrace_188095
  have hstable : (prefixWord ++ tailWord_188095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188095).length < 2 ^ (prefixWord ++ tailWord_188095).sum := by decide
  have hdescent : baseEnd_188095 < baseStart_188095 := by decide
  rcases family_descends (prefixWord ++ tailWord_188095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188150 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_188150 : Nat := 118140960795 + 188150 * 2 ^ 59
def prefixEnd_188150 : Nat := 4983230072969 + 3 ^ 40 * 188150 * 2
def baseEnd_188150 : Nat := 64407590095696063973147

theorem tailTrace_188150 : CollatzResearch.WordTrace tailWord_188150 prefixEnd_188150 64407590095696063973147 := by
  unfold tailWord_188150
  simp only [CollatzResearch.WordTrace]
  refine ⟨428899641773259894177119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4574929512248105537889269 428899641773259894177119)
  ·
    refine ⟨643349462659889841265679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428899641773259894177119 643349462659889841265679)
    ·
      refine ⟨965024193989834761898519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643349462659889841265679 965024193989834761898519)
      ·
        refine ⟨1447536290984752142847779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965024193989834761898519 1447536290984752142847779)
        ·
          refine ⟨2171304436477128214271669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447536290984752142847779 2171304436477128214271669)
          ·
            refine ⟨203559790919730770087969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2171304436477128214271669 203559790919730770087969)
            ·
              refine ⟨152669843189798077565977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203559790919730770087969 152669843189798077565977)
              ·
                refine ⟨114502382392348558174483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152669843189798077565977 114502382392348558174483)
                ·
                  refine ⟨171753573588522837261725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114502382392348558174483 171753573588522837261725)
                  ·
                    refine ⟨64407590095696063973147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171753573588522837261725 64407590095696063973147)
                    ·
                      rfl

theorem cell22_188150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_188150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188150 prefixEnd_188150 := by exact prefixLift 188150
  have htrace : WordTrace (prefixWord ++ tailWord_188150) baseStart_188150 baseEnd_188150 := by
    simpa [prefixWord, tailWord_188150, baseEnd_188150] using wordTrace_append hprefix tailTrace_188150
  have hstable : (prefixWord ++ tailWord_188150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188150).length < 2 ^ (prefixWord ++ tailWord_188150).sum := by decide
  have hdescent : baseEnd_188150 < baseStart_188150 := by decide
  rcases family_descends (prefixWord ++ tailWord_188150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188172 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_188172 : Nat := 118140960795 + 188172 * 2 ^ 59
def prefixEnd_188172 : Nat := 4983230072969 + 3 ^ 40 * 188172 * 2
def baseEnd_188172 : Nat := 64415121145295339923079

theorem tailTrace_188172 : CollatzResearch.WordTrace tailWord_188172 prefixEnd_188172 64415121145295339923079 := by
  unfold tailWord_188172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431598337146228032067385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4575464449528304042756513 3431598337146228032067385)
  ·
    refine ⟨2573698752859671024050539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3431598337146228032067385 2573698752859671024050539)
    ·
      refine ⟨3860548129289506536075809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573698752859671024050539 3860548129289506536075809)
      ·
        refine ⟨2895411096967129902056857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860548129289506536075809 2895411096967129902056857)
        ·
          refine ⟨2171558322725347426542643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895411096967129902056857 2171558322725347426542643)
          ·
            refine ⟨3257337484088021139813965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171558322725347426542643 3257337484088021139813965)
            ·
              refine ⟨1221501556533007927430237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3257337484088021139813965 1221501556533007927430237)
              ·
                refine ⟨458063083699877972786339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221501556533007927430237 458063083699877972786339)
                ·
                  refine ⟨687094625549816959179509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458063083699877972786339 687094625549816959179509)
                  ·
                    refine ⟨64415121145295339923079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687094625549816959179509 64415121145295339923079)
                    ·
                      rfl

theorem cell22_188172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_188172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188172 prefixEnd_188172 := by exact prefixLift 188172
  have htrace : WordTrace (prefixWord ++ tailWord_188172) baseStart_188172 baseEnd_188172 := by
    simpa [prefixWord, tailWord_188172, baseEnd_188172] using wordTrace_append hprefix tailTrace_188172
  have hstable : (prefixWord ++ tailWord_188172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188172).length < 2 ^ (prefixWord ++ tailWord_188172).sum := by decide
  have hdescent : baseEnd_188172 < baseStart_188172 := by decide
  rcases family_descends (prefixWord ++ tailWord_188172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188223 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 2, 3]
def baseStart_188223 : Nat := 118140960795 + 188223 * 2 ^ 59
def prefixEnd_188223 : Nat := 4983230072969 + 3 ^ 40 * 188223 * 2
def baseEnd_188223 : Nat := 64432579487548206897923

theorem tailTrace_188223 : CollatzResearch.WordTrace tailWord_188223 prefixEnd_188223 64432579487548206897923 := by
  unfold tailWord_188223
  simp only [CollatzResearch.WordTrace]
  refine ⟨6865056797107691774241323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4576704531405127849494215 6865056797107691774241323)
  ·
    refine ⟨10297585195661537661361985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6865056797107691774241323 10297585195661537661361985)
    ·
      refine ⟨7723188896746153246021489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10297585195661537661361985 7723188896746153246021489)
      ·
        refine ⟨5792391672559614934516117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7723188896746153246021489 5792391672559614934516117)
        ·
          refine ⟨271518359651231950055443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5792391672559614934516117 271518359651231950055443)
          ·
            refine ⟨407277539476847925083165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271518359651231950055443 407277539476847925083165)
            ·
              refine ⟨152729077303817971906187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407277539476847925083165 152729077303817971906187)
              ·
                refine ⟨229093615955726957859281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152729077303817971906187 229093615955726957859281)
                ·
                  refine ⟨171820211966795218394461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229093615955726957859281 171820211966795218394461)
                  ·
                    refine ⟨64432579487548206897923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171820211966795218394461 64432579487548206897923)
                    ·
                      rfl

theorem cell22_188223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_188223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188223 prefixEnd_188223 := by exact prefixLift 188223
  have htrace : WordTrace (prefixWord ++ tailWord_188223) baseStart_188223 baseEnd_188223 := by
    simpa [prefixWord, tailWord_188223, baseEnd_188223] using wordTrace_append hprefix tailTrace_188223
  have hstable : (prefixWord ++ tailWord_188223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188223).length < 2 ^ (prefixWord ++ tailWord_188223).sum := by decide
  have hdescent : baseEnd_188223 < baseStart_188223 := by decide
  rcases family_descends (prefixWord ++ tailWord_188223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188234 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_188234 : Nat := 118140960795 + 188234 * 2 ^ 59
def prefixEnd_188234 : Nat := 4983230072969 + 3 ^ 40 * 188234 * 2
def baseEnd_188234 : Nat := 64436345012347844872889

theorem tailTrace_188234 : CollatzResearch.WordTrace tailWord_188234 prefixEnd_188234 64436345012347844872889 := by
  unfold tailWord_188234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716364500016960163222939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4576972000045227101927837 1716364500016960163222939)
  ·
    refine ⟨2574546750025440244834409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716364500016960163222939 2574546750025440244834409)
    ·
      refine ⟨1930910062519080183625807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2574546750025440244834409 1930910062519080183625807)
      ·
        refine ⟨2896365093778620275438711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930910062519080183625807 2896365093778620275438711)
        ·
          refine ⟨4344547640667930413158067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896365093778620275438711 4344547640667930413158067)
          ·
            refine ⟨6516821461001895619737101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344547640667930413158067 6516821461001895619737101)
            ·
              refine ⟨2443808047875710857401413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6516821461001895619737101 2443808047875710857401413)
              ·
                refine ⟨458214008976695785762765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2443808047875710857401413 458214008976695785762765)
                ·
                  refine ⟨171830253366260919661037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458214008976695785762765 171830253366260919661037)
                  ·
                    refine ⟨64436345012347844872889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171830253366260919661037 64436345012347844872889)
                    ·
                      rfl

theorem cell22_188234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_188234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188234 prefixEnd_188234 := by exact prefixLift 188234
  have htrace : WordTrace (prefixWord ++ tailWord_188234) baseStart_188234 baseEnd_188234 := by
    simpa [prefixWord, tailWord_188234, baseEnd_188234] using wordTrace_append hprefix tailTrace_188234
  have hstable : (prefixWord ++ tailWord_188234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188234).length < 2 ^ (prefixWord ++ tailWord_188234).sum := by decide
  have hdescent : baseEnd_188234 < baseStart_188234 := by decide
  rcases family_descends (prefixWord ++ tailWord_188234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188236 : List Nat := [2, 2, 1, 3, 4, 2, 2, 6]
def baseStart_188236 : Nat := 118140960795 + 188236 * 2 ^ 59
def prefixEnd_188236 : Nat := 4983230072969 + 3 ^ 40 * 188236 * 2
def baseEnd_188236 : Nat := 7159669961468945146987

theorem tailTrace_188236 : CollatzResearch.WordTrace tailWord_188236 prefixEnd_188236 7159669961468945146987 := by
  unfold tailWord_188236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432765473030297497232281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4577020630707063329643041 3432765473030297497232281)
  ·
    refine ⟨2574574104772723122924211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3432765473030297497232281 2574574104772723122924211)
    ·
      refine ⟨3861861157159084684386317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574574104772723122924211 3861861157159084684386317)
      ·
        refine ⟨1448197933934656756644869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3861861157159084684386317 1448197933934656756644869)
        ·
          refine ⟨271537112612748141870913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1448197933934656756644869 271537112612748141870913)
          ·
            refine ⟨203652834459561106403185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271537112612748141870913 203652834459561106403185)
            ·
              refine ⟨152739625844670829802389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203652834459561106403185 152739625844670829802389)
              ·
                refine ⟨7159669961468945146987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152739625844670829802389 7159669961468945146987)
                ·
                  rfl

theorem cell22_188236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_188236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188236 prefixEnd_188236 := by exact prefixLift 188236
  have htrace : WordTrace (prefixWord ++ tailWord_188236) baseStart_188236 baseEnd_188236 := by
    simpa [prefixWord, tailWord_188236, baseEnd_188236] using wordTrace_append hprefix tailTrace_188236
  have hstable : (prefixWord ++ tailWord_188236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188236).length < 2 ^ (prefixWord ++ tailWord_188236).sum := by decide
  have hdescent : baseEnd_188236 < baseStart_188236 := by decide
  rcases family_descends (prefixWord ++ tailWord_188236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188264 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_188264 : Nat := 118140960795 + 188264 * 2 ^ 59
def prefixEnd_188264 : Nat := 4983230072969 + 3 ^ 40 * 188264 * 2
def baseEnd_188264 : Nat := 21482204875145922207599

theorem tailTrace_188264 : CollatzResearch.WordTrace tailWord_188264 prefixEnd_188264 21482204875145922207599 := by
  unfold tailWord_188264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433276094979577888241923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4577701459972770517655897 3433276094979577888241923)
  ·
    refine ⟨5149914142469366832362885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3433276094979577888241923 5149914142469366832362885)
    ·
      refine ⟨965608901713006281068041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5149914142469366832362885 965608901713006281068041)
      ·
        refine ⟨724206676284754710801031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965608901713006281068041 724206676284754710801031)
        ·
          refine ⟨1086310014427132066201547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724206676284754710801031 1086310014427132066201547)
          ·
            refine ⟨1629465021640698099302321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086310014427132066201547 1629465021640698099302321)
            ·
              refine ⟨1222098766230523574476741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1629465021640698099302321 1222098766230523574476741)
              ·
                refine ⟨229143518668223170214389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1222098766230523574476741 229143518668223170214389)
                ·
                  refine ⟨21482204875145922207599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229143518668223170214389 21482204875145922207599)
                  ·
                    rfl

theorem cell22_188264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_188264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188264 prefixEnd_188264 := by exact prefixLift 188264
  have htrace : WordTrace (prefixWord ++ tailWord_188264) baseStart_188264 baseEnd_188264 := by
    simpa [prefixWord, tailWord_188264, baseEnd_188264] using wordTrace_append hprefix tailTrace_188264
  have hstable : (prefixWord ++ tailWord_188264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188264).length < 2 ^ (prefixWord ++ tailWord_188264).sum := by decide
  have hdescent : baseEnd_188264 < baseStart_188264 := by decide
  rcases family_descends (prefixWord ++ tailWord_188264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188341 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_188341 : Nat := 118140960795 + 188341 * 2 ^ 59
def prefixEnd_188341 : Nat := 4983230072969 + 3 ^ 40 * 188341 * 2
def baseEnd_188341 : Nat := 64472973299035232447561

theorem tailTrace_188341 : CollatzResearch.WordTrace tailWord_188341 prefixEnd_188341 64472973299035232447561 := by
  unfold tailWord_188341
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869360610680197927036877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4579573740453465284691251 6869360610680197927036877)
  ·
    refine ⟨2576010229005074222638829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6869360610680197927036877 2576010229005074222638829)
    ·
      refine ⟨966003835876902833489561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2576010229005074222638829 966003835876902833489561)
      ·
        refine ⟨724502876907677125117171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966003835876902833489561 724502876907677125117171)
        ·
          refine ⟨1086754315361515687675757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724502876907677125117171 1086754315361515687675757)
          ·
            refine ⟨407532868260568382878409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1086754315361515687675757 407532868260568382878409)
            ·
              refine ⟨305649651195426287158807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407532868260568382878409 305649651195426287158807)
              ·
                refine ⟨458474476793139430738211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305649651195426287158807 458474476793139430738211)
                ·
                  refine ⟨687711715189709146107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458474476793139430738211 687711715189709146107317)
                  ·
                    refine ⟨64472973299035232447561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687711715189709146107317 64472973299035232447561)
                    ·
                      rfl

theorem cell22_188341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_188341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188341 prefixEnd_188341 := by exact prefixLift 188341
  have htrace : WordTrace (prefixWord ++ tailWord_188341) baseStart_188341 baseEnd_188341 := by
    simpa [prefixWord, tailWord_188341, baseEnd_188341] using wordTrace_append hprefix tailTrace_188341
  have hstable : (prefixWord ++ tailWord_188341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188341).length < 2 ^ (prefixWord ++ tailWord_188341).sum := by decide
  have hdescent : baseEnd_188341 < baseStart_188341 := by decide
  rcases family_descends (prefixWord ++ tailWord_188341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188422 : List Nat := [6, 2, 1, 2, 1, 2, 8]
def baseStart_188422 : Nat := 118140960795 + 188422 * 2 ^ 59
def prefixEnd_188422 : Nat := 4983230072969 + 3 ^ 40 * 188422 * 2
def baseEnd_188422 : Nat := 2388914861273260043419

theorem tailTrace_188422 : CollatzResearch.WordTrace tailWord_188422 prefixEnd_188422 2388914861273260043419 := by
  unfold tailWord_188422
  simp only [CollatzResearch.WordTrace]
  refine ⟨214759841355835898772985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4581543282257832507157013 214759841355835898772985)
  ·
    refine ⟨161069881016876924079739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214759841355835898772985 161069881016876924079739)
    ·
      refine ⟨241604821525315386119609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161069881016876924079739 241604821525315386119609)
      ·
        refine ⟨181203616143986539589707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241604821525315386119609 181203616143986539589707)
        ·
          refine ⟨271805424215979809384561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181203616143986539589707 271805424215979809384561)
          ·
            refine ⟨203854068161984857038421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271805424215979809384561 203854068161984857038421)
            ·
              refine ⟨2388914861273260043419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 203854068161984857038421 2388914861273260043419)
              ·
                rfl

theorem cell22_188422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 8].length) (baseStart_188422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188422 prefixEnd_188422 := by exact prefixLift 188422
  have htrace : WordTrace (prefixWord ++ tailWord_188422) baseStart_188422 baseEnd_188422 := by
    simpa [prefixWord, tailWord_188422, baseEnd_188422] using wordTrace_append hprefix tailTrace_188422
  have hstable : (prefixWord ++ tailWord_188422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188422).length < 2 ^ (prefixWord ++ tailWord_188422).sum := by decide
  have hdescent : baseEnd_188422 < baseStart_188422 := by decide
  rcases family_descends (prefixWord ++ tailWord_188422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188437 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_188437 : Nat := 118140960795 + 188437 * 2 ^ 59
def prefixEnd_188437 : Nat := 4983230072969 + 3 ^ 40 * 188437 * 2
def baseEnd_188437 : Nat := 64505836060922982047267

theorem tailTrace_188437 : CollatzResearch.WordTrace tailWord_188437 prefixEnd_188437 64505836060922982047267 := by
  unfold tailWord_188437
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872862018332406322531565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4581908012221604215021043 6872862018332406322531565)
  ·
    refine ⟨2577323256874652370949337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6872862018332406322531565 2577323256874652370949337)
    ·
      refine ⟨1932992442655989278212003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2577323256874652370949337 1932992442655989278212003)
      ·
        refine ⟨2899488663983983917318005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932992442655989278212003 2899488663983983917318005)
        ·
          refine ⟨271827062248498492248563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2899488663983983917318005 271827062248498492248563)
          ·
            refine ⟨407740593372747738372845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271827062248498492248563 407740593372747738372845)
            ·
              refine ⟨152902722514780401889817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407740593372747738372845 152902722514780401889817)
              ·
                refine ⟨114677041886085301417363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152902722514780401889817 114677041886085301417363)
                ·
                  refine ⟨172015562829127952126045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114677041886085301417363 172015562829127952126045)
                  ·
                    refine ⟨64505836060922982047267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172015562829127952126045 64505836060922982047267)
                    ·
                      rfl

theorem cell22_188437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_188437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188437 prefixEnd_188437 := by exact prefixLift 188437
  have htrace : WordTrace (prefixWord ++ tailWord_188437) baseStart_188437 baseEnd_188437 := by
    simpa [prefixWord, tailWord_188437, baseEnd_188437] using wordTrace_append hprefix tailTrace_188437
  have hstable : (prefixWord ++ tailWord_188437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188437).length < 2 ^ (prefixWord ++ tailWord_188437).sum := by decide
  have hdescent : baseEnd_188437 < baseStart_188437 := by decide
  rcases family_descends (prefixWord ++ tailWord_188437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188476 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_188476 : Nat := 118140960795 + 188476 * 2 ^ 59
def prefixEnd_188476 : Nat := 4983230072969 + 3 ^ 40 * 188476 * 2
def baseEnd_188476 : Nat := 64519186557939880322147

theorem tailTrace_188476 : CollatzResearch.WordTrace tailWord_188476 prefixEnd_188476 64519186557939880322147 := by
  unfold tailWord_188476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437142232595557991600641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4582856310127410655467521 3437142232595557991600641)
  ·
    refine ⟨2577856674446668493700481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3437142232595557991600641 2577856674446668493700481)
    ·
      refine ⟨1933392505835001370275361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2577856674446668493700481 1933392505835001370275361)
      ·
        refine ⟨1450044379376251027706521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1933392505835001370275361 1450044379376251027706521)
        ·
          refine ⟨1087533284532188270779891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450044379376251027706521 1087533284532188270779891)
          ·
            refine ⟨1631299926798282406169837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087533284532188270779891 1631299926798282406169837)
            ·
              refine ⟨611737472549355902313689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631299926798282406169837 611737472549355902313689)
              ·
                refine ⟨458803104412016926735267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611737472549355902313689 458803104412016926735267)
                ·
                  refine ⟨688204656618025390102901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458803104412016926735267 688204656618025390102901)
                  ·
                    refine ⟨64519186557939880322147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 688204656618025390102901 64519186557939880322147)
                    ·
                      rfl

theorem cell22_188476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_188476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188476 prefixEnd_188476 := by exact prefixLift 188476
  have htrace : WordTrace (prefixWord ++ tailWord_188476) baseStart_188476 baseEnd_188476 := by
    simpa [prefixWord, tailWord_188476, baseEnd_188476] using wordTrace_append hprefix tailTrace_188476
  have hstable : (prefixWord ++ tailWord_188476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188476).length < 2 ^ (prefixWord ++ tailWord_188476).sum := by decide
  have hdescent : baseEnd_188476 < baseStart_188476 := by decide
  rcases family_descends (prefixWord ++ tailWord_188476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188589 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_188589 : Nat := 118140960795 + 188589 * 2 ^ 59
def prefixEnd_188589 : Nat := 4983230072969 + 3 ^ 40 * 188589 * 2
def baseEnd_188589 : Nat := 64557868767245252246801

theorem tailTrace_188589 : CollatzResearch.WordTrace tailWord_188589 prefixEnd_188589 64557868767245252246801 := by
  unfold tailWord_188589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878405913781736282064821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4585603942521157521376547 6878405913781736282064821)
  ·
    refine ⟨644850554417037776443577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6878405913781736282064821 644850554417037776443577)
    ·
      refine ⟨483637915812778332332683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 644850554417037776443577 483637915812778332332683)
      ·
        refine ⟨725456873719167498499025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483637915812778332332683 725456873719167498499025)
        ·
          refine ⟨544092655289375623874269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725456873719167498499025 544092655289375623874269)
          ·
            refine ⟨204034745733515858952851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 544092655289375623874269 204034745733515858952851)
            ·
              refine ⟨306052118600273788429277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204034745733515858952851 306052118600273788429277)
              ·
                refine ⟨114769544475102670660979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306052118600273788429277 114769544475102670660979)
                ·
                  refine ⟨172154316712654005991469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114769544475102670660979 172154316712654005991469)
                  ·
                    refine ⟨64557868767245252246801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172154316712654005991469 64557868767245252246801)
                    ·
                      rfl

theorem cell22_188589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_188589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188589 prefixEnd_188589 := by exact prefixLift 188589
  have htrace : WordTrace (prefixWord ++ tailWord_188589) baseStart_188589 baseEnd_188589 := by
    simpa [prefixWord, tailWord_188589, baseEnd_188589] using wordTrace_append hprefix tailTrace_188589
  have hstable : (prefixWord ++ tailWord_188589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188589).length < 2 ^ (prefixWord ++ tailWord_188589).sum := by decide
  have hdescent : baseEnd_188589 < baseStart_188589 := by decide
  rcases family_descends (prefixWord ++ tailWord_188589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188613 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 4]
def baseStart_188613 : Nat := 118140960795 + 188613 * 2 ^ 59
def prefixEnd_188613 : Nat := 4983230072969 + 3 ^ 40 * 188613 * 2
def baseEnd_188613 : Nat := 21522028152572396548909

theorem tailTrace_188613 : CollatzResearch.WordTrace tailWord_188613 prefixEnd_188613 21522028152572396548909 := by
  unfold tailWord_188613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879281265694788380938493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4586187510463192253958995 6879281265694788380938493)
  ·
    refine ⟨2579730474635545642851935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6879281265694788380938493 2579730474635545642851935)
    ·
      refine ⟨3869595711953318464277903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579730474635545642851935 3869595711953318464277903)
      ·
        refine ⟨5804393567929977696416855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869595711953318464277903 5804393567929977696416855)
        ·
          refine ⟨8706590351894966544625283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804393567929977696416855 8706590351894966544625283)
          ·
            refine ⟨13059885527842449816937925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8706590351894966544625283 13059885527842449816937925)
            ·
              refine ⟨2448728536470459340675861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13059885527842449816937925 2448728536470459340675861)
              ·
                refine ⟨114784150147052781594181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2448728536470459340675861 114784150147052781594181)
                ·
                  refine ⟨21522028152572396548909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114784150147052781594181 21522028152572396548909)
                  ·
                    rfl

theorem cell22_188613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_188613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188613 prefixEnd_188613 := by exact prefixLift 188613
  have htrace : WordTrace (prefixWord ++ tailWord_188613) baseStart_188613 baseEnd_188613 := by
    simpa [prefixWord, tailWord_188613, baseEnd_188613] using wordTrace_append hprefix tailTrace_188613
  have hstable : (prefixWord ++ tailWord_188613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188613).length < 2 ^ (prefixWord ++ tailWord_188613).sum := by decide
  have hdescent : baseEnd_188613 < baseStart_188613 := by decide
  rcases family_descends (prefixWord ++ tailWord_188613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188641 : List Nat := [1, 2, 3, 1, 3, 1, 1, 10]
def baseStart_188641 : Nat := 118140960795 + 188641 * 2 ^ 59
def prefixEnd_188641 : Nat := 4983230072969 + 3 ^ 40 * 188641 * 2
def baseEnd_188641 : Nat := 7175074381103827771849

theorem tailTrace_188641 : CollatzResearch.WordTrace tailWord_188641 prefixEnd_188641 7175074381103827771849 := by
  unfold tailWord_188641
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880302509593349162957777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4586868339728899441971851 6880302509593349162957777)
  ·
    refine ⟨5160226882195011872218333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6880302509593349162957777 5160226882195011872218333)
    ·
      refine ⟨1935085080823129452081875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5160226882195011872218333 1935085080823129452081875)
      ·
        refine ⟨2902627621234694178122813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935085080823129452081875 2902627621234694178122813)
        ·
          refine ⟨1088485357963010316796055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2902627621234694178122813 1088485357963010316796055)
          ·
            refine ⟨1632728036944515475194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088485357963010316796055 1632728036944515475194083)
            ·
              refine ⟨2449092055416773212791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632728036944515475194083 2449092055416773212791125)
              ·
                refine ⟨7175074381103827771849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2449092055416773212791125 7175074381103827771849)
                ·
                  rfl

theorem cell22_188641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 10].length) (baseStart_188641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188641 prefixEnd_188641 := by exact prefixLift 188641
  have htrace : WordTrace (prefixWord ++ tailWord_188641) baseStart_188641 baseEnd_188641 := by
    simpa [prefixWord, tailWord_188641, baseEnd_188641] using wordTrace_append hprefix tailTrace_188641
  have hstable : (prefixWord ++ tailWord_188641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188641).length < 2 ^ (prefixWord ++ tailWord_188641).sum := by decide
  have hdescent : baseEnd_188641 < baseStart_188641 := by decide
  rcases family_descends (prefixWord ++ tailWord_188641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188671 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_188671 : Nat := 118140960795 + 188671 * 2 ^ 59
def prefixEnd_188671 : Nat := 4983230072969 + 3 ^ 40 * 188671 * 2
def baseEnd_188671 : Nat := 64585939043024371696549

theorem tailTrace_188671 : CollatzResearch.WordTrace tailWord_188671 prefixEnd_188671 64585939043024371696549 := by
  unfold tailWord_188671
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881396699484664286549867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4587597799656442857699911 6881396699484664286549867)
  ·
    refine ⟨10322095049226996429824801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6881396699484664286549867 10322095049226996429824801)
    ·
      refine ⟨7741571286920247322368601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10322095049226996429824801 7741571286920247322368601)
      ·
        refine ⟨5806178465190185491776451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7741571286920247322368601 5806178465190185491776451)
        ·
          refine ⟨8709267697785278237664677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806178465190185491776451 8709267697785278237664677)
          ·
            refine ⟨1632987693334739669562127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8709267697785278237664677 1632987693334739669562127)
            ·
              refine ⟨2449481540002109504343191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632987693334739669562127 2449481540002109504343191)
              ·
                refine ⟨3674222310003164256514787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449481540002109504343191 3674222310003164256514787)
                ·
                  refine ⟨5511333465004746384772181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674222310003164256514787 5511333465004746384772181)
                  ·
                    refine ⟨64585939043024371696549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5511333465004746384772181 64585939043024371696549)
                    ·
                      rfl

theorem cell22_188671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_188671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188671 prefixEnd_188671 := by exact prefixLift 188671
  have htrace : WordTrace (prefixWord ++ tailWord_188671) baseStart_188671 baseEnd_188671 := by
    simpa [prefixWord, tailWord_188671, baseEnd_188671] using wordTrace_append hprefix tailTrace_188671
  have hstable : (prefixWord ++ tailWord_188671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188671).length < 2 ^ (prefixWord ++ tailWord_188671).sum := by decide
  have hdescent : baseEnd_188671 < baseStart_188671 := by decide
  rcases family_descends (prefixWord ++ tailWord_188671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188707 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 1, 3]
def baseStart_188707 : Nat := 118140960795 + 188707 * 2 ^ 59
def prefixEnd_188707 : Nat := 4983230072969 + 3 ^ 40 * 188707 * 2
def baseEnd_188707 : Nat := 64598262578732277796439

theorem tailTrace_188707 : CollatzResearch.WordTrace tailWord_188707 prefixEnd_188707 64598262578732277796439 := by
  unfold tailWord_188707
  simp only [CollatzResearch.WordTrace]
  refine ⟨6882709727354242434860375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4588473151569494956573583 6882709727354242434860375)
  ·
    refine ⟨10324064591031363652290563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6882709727354242434860375 10324064591031363652290563)
    ·
      refine ⟨15486096886547045478435845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10324064591031363652290563 15486096886547045478435845)
      ·
        refine ⟨2903643166227571027206721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15486096886547045478435845 2903643166227571027206721)
        ·
          refine ⟨2177732374670678270405041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903643166227571027206721 2177732374670678270405041)
          ·
            refine ⟨1633299281003008702803781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177732374670678270405041 1633299281003008702803781)
            ·
              refine ⟨306243615188064131775709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1633299281003008702803781 306243615188064131775709)
              ·
                refine ⟨114841355695524049415891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306243615188064131775709 114841355695524049415891)
                ·
                  refine ⟨172262033543286074123837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114841355695524049415891 172262033543286074123837)
                  ·
                    refine ⟨64598262578732277796439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172262033543286074123837 64598262578732277796439)
                    ·
                      rfl

theorem cell22_188707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 3].length) (baseStart_188707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188707 prefixEnd_188707 := by exact prefixLift 188707
  have htrace : WordTrace (prefixWord ++ tailWord_188707) baseStart_188707 baseEnd_188707 := by
    simpa [prefixWord, tailWord_188707, baseEnd_188707] using wordTrace_append hprefix tailTrace_188707
  have hstable : (prefixWord ++ tailWord_188707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188707).length < 2 ^ (prefixWord ++ tailWord_188707).sum := by decide
  have hdescent : baseEnd_188707 < baseStart_188707 := by decide
  rcases family_descends (prefixWord ++ tailWord_188707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188724 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_188724 : Nat := 118140960795 + 188724 * 2 ^ 59
def prefixEnd_188724 : Nat := 4983230072969 + 3 ^ 40 * 188724 * 2
def baseEnd_188724 : Nat := 64604082026149900121387

theorem tailTrace_188724 : CollatzResearch.WordTrace tailWord_188724 prefixEnd_188724 64604082026149900121387 := by
  unfold tailWord_188724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441664884146327169114613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4588886512195102892152817 3441664884146327169114613)
  ·
    refine ⟨322656082888718172104495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3441664884146327169114613 322656082888718172104495)
    ·
      refine ⟨483984124333077258156743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322656082888718172104495 483984124333077258156743)
      ·
        refine ⟨725976186499615887235115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483984124333077258156743 725976186499615887235115)
        ·
          refine ⟨1088964279749423830852673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725976186499615887235115 1088964279749423830852673)
          ·
            refine ⟨816723209812067873139505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088964279749423830852673 816723209812067873139505)
            ·
              refine ⟨612542407359050904854629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816723209812067873139505 612542407359050904854629)
              ·
                refine ⟨114851701379822044660243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612542407359050904854629 114851701379822044660243)
                ·
                  refine ⟨172277552069733066990365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114851701379822044660243 172277552069733066990365)
                  ·
                    refine ⟨64604082026149900121387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172277552069733066990365 64604082026149900121387)
                    ·
                      rfl

theorem cell22_188724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_188724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188724 prefixEnd_188724 := by exact prefixLift 188724
  have htrace : WordTrace (prefixWord ++ tailWord_188724) baseStart_188724 baseEnd_188724 := by
    simpa [prefixWord, tailWord_188724, baseEnd_188724] using wordTrace_append hprefix tailTrace_188724
  have hstable : (prefixWord ++ tailWord_188724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188724).length < 2 ^ (prefixWord ++ tailWord_188724).sum := by decide
  have hdescent : baseEnd_188724 < baseStart_188724 := by decide
  rcases family_descends (prefixWord ++ tailWord_188724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188748 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_188748 : Nat := 118140960795 + 188748 * 2 ^ 59
def prefixEnd_188748 : Nat := 4983230072969 + 3 ^ 40 * 188748 * 2
def baseEnd_188748 : Nat := 21537432572207279173771

theorem tailTrace_188748 : CollatzResearch.WordTrace tailWord_188748 prefixEnd_188748 21537432572207279173771 := by
  unfold tailWord_188748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442102560102853218551449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4589470080137137624735265 3442102560102853218551449)
  ·
    refine ⟨2581576920077139913913587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3442102560102853218551449 2581576920077139913913587)
    ·
      refine ⟨3872365380115709870870381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581576920077139913913587 3872365380115709870870381)
      ·
        refine ⟨1452137017543391201576393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3872365380115709870870381 1452137017543391201576393)
        ·
          refine ⟨1089102763157543401182295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452137017543391201576393 1089102763157543401182295)
          ·
            refine ⟨1633654144736315101773443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089102763157543401182295 1633654144736315101773443)
            ·
              refine ⟨2450481217104472652660165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633654144736315101773443 2450481217104472652660165)
              ·
                refine ⟨459465228207088622373781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2450481217104472652660165 459465228207088622373781)
                ·
                  refine ⟨21537432572207279173771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 459465228207088622373781 21537432572207279173771)
                  ·
                    rfl

theorem cell22_188748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_188748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188748 prefixEnd_188748 := by exact prefixLift 188748
  have htrace : WordTrace (prefixWord ++ tailWord_188748) baseStart_188748 baseEnd_188748 := by
    simpa [prefixWord, tailWord_188748, baseEnd_188748] using wordTrace_append hprefix tailTrace_188748
  have hstable : (prefixWord ++ tailWord_188748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188748).length < 2 ^ (prefixWord ++ tailWord_188748).sum := by decide
  have hdescent : baseEnd_188748 < baseStart_188748 := by decide
  rcases family_descends (prefixWord ++ tailWord_188748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188797 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_188797 : Nat := 118140960795 + 188797 * 2 ^ 59
def prefixEnd_188797 : Nat := 4983230072969 + 3 ^ 40 * 188797 * 2
def baseEnd_188797 : Nat := 64629071418002043046163

theorem tailTrace_188797 : CollatzResearch.WordTrace tailWord_188797 prefixEnd_188797 64629071418002043046163 := by
  unfold tailWord_188797
  simp only [CollatzResearch.WordTrace]
  refine ⟨6885992297028187805636645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4590661531352125203757763 6885992297028187805636645)
  ·
    refine ⟨1291123555692785213556871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6885992297028187805636645 1291123555692785213556871)
    ·
      refine ⟨1936685333539177820335307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291123555692785213556871 1936685333539177820335307)
      ·
        refine ⟨2905028000308766730502961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936685333539177820335307 2905028000308766730502961)
        ·
          refine ⟨2178771000231575047877221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2905028000308766730502961 2178771000231575047877221)
          ·
            refine ⟨408519562543420321476979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2178771000231575047877221 408519562543420321476979)
            ·
              refine ⟨612779343815130482215469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408519562543420321476979 612779343815130482215469)
              ·
                refine ⟨229792253930673930830801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612779343815130482215469 229792253930673930830801)
                ·
                  refine ⟨172344190448005448123101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229792253930673930830801 172344190448005448123101)
                  ·
                    refine ⟨64629071418002043046163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172344190448005448123101 64629071418002043046163)
                    ·
                      rfl

theorem cell22_188797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_188797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188797 prefixEnd_188797 := by exact prefixLift 188797
  have htrace : WordTrace (prefixWord ++ tailWord_188797) baseStart_188797 baseEnd_188797 := by
    simpa [prefixWord, tailWord_188797, baseEnd_188797] using wordTrace_append hprefix tailTrace_188797
  have hstable : (prefixWord ++ tailWord_188797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188797).length < 2 ^ (prefixWord ++ tailWord_188797).sum := by decide
  have hdescent : baseEnd_188797 < baseStart_188797 := by decide
  rcases family_descends (prefixWord ++ tailWord_188797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188833 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 4]
def baseStart_188833 : Nat := 118140960795 + 188833 * 2 ^ 59
def prefixEnd_188833 : Nat := 4983230072969 + 3 ^ 40 * 188833 * 2
def baseEnd_188833 : Nat := 21547131651236649715351

theorem tailTrace_188833 : CollatzResearch.WordTrace tailWord_188833 prefixEnd_188833 21547131651236649715351 := by
  unfold tailWord_188833
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887305324897765953947153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4591536883265177302631435 6887305324897765953947153)
  ·
    refine ⟨5165478993673324465460365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6887305324897765953947153 5165478993673324465460365)
    ·
      refine ⟨1937054622627496674547637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5165478993673324465460365 1937054622627496674547637)
      ·
        refine ⟨181598870871327813238841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1937054622627496674547637 181598870871327813238841)
        ·
          refine ⟨136199153153495859929131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181598870871327813238841 136199153153495859929131)
          ·
            refine ⟨204298729730243789893697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136199153153495859929131 204298729730243789893697)
            ·
              refine ⟨153224047297682842420273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204298729730243789893697 153224047297682842420273)
              ·
                refine ⟨114918035473262131815205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153224047297682842420273 114918035473262131815205)
                ·
                  refine ⟨21547131651236649715351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114918035473262131815205 21547131651236649715351)
                  ·
                    rfl

theorem cell22_188833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_188833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188833 prefixEnd_188833 := by exact prefixLift 188833
  have htrace : WordTrace (prefixWord ++ tailWord_188833) baseStart_188833 baseEnd_188833 := by
    simpa [prefixWord, tailWord_188833, baseEnd_188833] using wordTrace_append hprefix tailTrace_188833
  have hstable : (prefixWord ++ tailWord_188833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188833).length < 2 ^ (prefixWord ++ tailWord_188833).sum := by decide
  have hdescent : baseEnd_188833 < baseStart_188833 := by decide
  rcases family_descends (prefixWord ++ tailWord_188833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188855 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 5]
def baseStart_188855 : Nat := 118140960795 + 188855 * 2 ^ 59
def prefixEnd_188855 : Nat := 4983230072969 + 3 ^ 40 * 188855 * 2
def baseEnd_188855 : Nat := 21549642001103075031995

theorem tailTrace_188855 : CollatzResearch.WordTrace tailWord_188855 prefixEnd_188855 21549642001103075031995 := by
  unfold tailWord_188855
  simp only [CollatzResearch.WordTrace]
  refine ⟨6888107730818063711248019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4592071820545375807498679 6888107730818063711248019)
  ·
    refine ⟨10332161596227095566872029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6888107730818063711248019 10332161596227095566872029)
    ·
      refine ⟨3874560598585160837577011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10332161596227095566872029 3874560598585160837577011)
      ·
        refine ⟨5811840897877741256365517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874560598585160837577011 5811840897877741256365517)
        ·
          refine ⟨2179440336704152971137069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5811840897877741256365517 2179440336704152971137069)
          ·
            refine ⟨817290126264057364176401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2179440336704152971137069 817290126264057364176401)
            ·
              refine ⟨612967594698043023132301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817290126264057364176401 612967594698043023132301)
              ·
                refine ⟨229862848011766133674613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 612967594698043023132301 229862848011766133674613)
                ·
                  refine ⟨21549642001103075031995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229862848011766133674613 21549642001103075031995)
                  ·
                    rfl

theorem cell22_188855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 5].length) (baseStart_188855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188855 prefixEnd_188855 := by exact prefixLift 188855
  have htrace : WordTrace (prefixWord ++ tailWord_188855) baseStart_188855 baseEnd_188855 := by
    simpa [prefixWord, tailWord_188855, baseEnd_188855] using wordTrace_append hprefix tailTrace_188855
  have hstable : (prefixWord ++ tailWord_188855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188855).length < 2 ^ (prefixWord ++ tailWord_188855).sum := by decide
  have hdescent : baseEnd_188855 < baseStart_188855 := by decide
  rcases family_descends (prefixWord ++ tailWord_188855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188876 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_188876 : Nat := 118140960795 + 188876 * 2 ^ 59
def prefixEnd_188876 : Nat := 4983230072969 + 3 ^ 40 * 188876 * 2
def baseEnd_188876 : Nat := 64656114732472170320921

theorem tailTrace_188876 : CollatzResearch.WordTrace tailWord_188876 prefixEnd_188876 64656114732472170320921 := by
  unfold tailWord_188876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444436831870992148881241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4592582442494656198508321 3444436831870992148881241)
  ·
    refine ⟨2583327623903244111660931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3444436831870992148881241 2583327623903244111660931)
    ·
      refine ⟨3874991435854866167491397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2583327623903244111660931 3874991435854866167491397)
      ·
        refine ⟨726560894222787406404637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3874991435854866167491397 726560894222787406404637)
        ·
          refine ⟨272460335333545277401739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726560894222787406404637 272460335333545277401739)
          ·
            refine ⟨408690503000317916102609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272460335333545277401739 408690503000317916102609)
            ·
              refine ⟨306517877250238437076957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408690503000317916102609 306517877250238437076957)
              ·
                refine ⟨114944203968839413903859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306517877250238437076957 114944203968839413903859)
                ·
                  refine ⟨172416305953259120855789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114944203968839413903859 172416305953259120855789)
                  ·
                    refine ⟨64656114732472170320921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172416305953259120855789 64656114732472170320921)
                    ·
                      rfl

theorem cell22_188876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_188876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188876 prefixEnd_188876 := by exact prefixLift 188876
  have htrace : WordTrace (prefixWord ++ tailWord_188876) baseStart_188876 baseEnd_188876 := by
    simpa [prefixWord, tailWord_188876, baseEnd_188876] using wordTrace_append hprefix tailTrace_188876
  have hstable : (prefixWord ++ tailWord_188876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188876).length < 2 ^ (prefixWord ++ tailWord_188876).sum := by decide
  have hdescent : baseEnd_188876 < baseStart_188876 := by decide
  rcases family_descends (prefixWord ++ tailWord_188876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188951 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 6]
def baseStart_188951 : Nat := 118140960795 + 188951 * 2 ^ 59
def prefixEnd_188951 : Nat := 4983230072969 + 3 ^ 40 * 188951 * 2
def baseEnd_188951 : Nat := 21560596255065658231897

theorem tailTrace_188951 : CollatzResearch.WordTrace tailWord_188951 prefixEnd_188951 21560596255065658231897 := by
  unfold tailWord_188951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891609138470272106742707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4594406092313514737828471 6891609138470272106742707)
  ·
    refine ⟨10337413707705408160114061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891609138470272106742707 10337413707705408160114061)
    ·
      refine ⟨3876530140389528060042773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10337413707705408160114061 3876530140389528060042773)
      ·
        refine ⟨181712350330759127814505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3876530140389528060042773 181712350330759127814505)
        ·
          refine ⟨136284262748069345860879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181712350330759127814505 136284262748069345860879)
          ·
            refine ⟨204426394122104018791319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136284262748069345860879 204426394122104018791319)
            ·
              refine ⟨306639591183156028186979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204426394122104018791319 306639591183156028186979)
              ·
                refine ⟨459959386774734042280469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306639591183156028186979 459959386774734042280469)
                ·
                  refine ⟨21560596255065658231897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 459959386774734042280469 21560596255065658231897)
                  ·
                    rfl

theorem cell22_188951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 6].length) (baseStart_188951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188951 prefixEnd_188951 := by exact prefixLift 188951
  have htrace : WordTrace (prefixWord ++ tailWord_188951) baseStart_188951 baseEnd_188951 := by
    simpa [prefixWord, tailWord_188951, baseEnd_188951] using wordTrace_append hprefix tailTrace_188951
  have hstable : (prefixWord ++ tailWord_188951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188951).length < 2 ^ (prefixWord ++ tailWord_188951).sum := by decide
  have hdescent : baseEnd_188951 < baseStart_188951 := by decide
  rcases family_descends (prefixWord ++ tailWord_188951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188977 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_188977 : Nat := 118140960795 + 188977 * 2 ^ 59
def prefixEnd_188977 : Nat := 4983230072969 + 3 ^ 40 * 188977 * 2
def baseEnd_188977 : Nat := 64690689096541573545611

theorem tailTrace_188977 : CollatzResearch.WordTrace tailWord_188977 prefixEnd_188977 64690689096541573545611 := by
  unfold tailWord_188977
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892557436376078547189185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4595038290917385698126123 6892557436376078547189185)
  ·
    refine ⟨5169418077282058910391889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6892557436376078547189185 5169418077282058910391889)
    ·
      refine ⟨3877063557961544182793917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5169418077282058910391889 3877063557961544182793917)
      ·
        refine ⟨1453898834235579068547719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3877063557961544182793917 1453898834235579068547719)
        ·
          refine ⟨2180848251353368602821579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453898834235579068547719 2180848251353368602821579)
          ·
            refine ⟨3271272377030052904232369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180848251353368602821579 3271272377030052904232369)
            ·
              refine ⟨2453454282772539678174277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271272377030052904232369 2453454282772539678174277)
              ·
                refine ⟨460022678019851189657677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2453454282772539678174277 460022678019851189657677)
                ·
                  refine ⟨172508504257444196121629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460022678019851189657677 172508504257444196121629)
                  ·
                    refine ⟨64690689096541573545611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172508504257444196121629 64690689096541573545611)
                    ·
                      rfl

theorem cell22_188977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_188977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188977 prefixEnd_188977 := by exact prefixLift 188977
  have htrace : WordTrace (prefixWord ++ tailWord_188977) baseStart_188977 baseEnd_188977 := by
    simpa [prefixWord, tailWord_188977, baseEnd_188977] using wordTrace_append hprefix tailTrace_188977
  have hstable : (prefixWord ++ tailWord_188977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188977).length < 2 ^ (prefixWord ++ tailWord_188977).sum := by decide
  have hdescent : baseEnd_188977 < baseStart_188977 := by decide
  rcases family_descends (prefixWord ++ tailWord_188977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188996 : List Nat := [2, 3, 5, 1, 2, 9]
def baseStart_188996 : Nat := 118140960795 + 188996 * 2 ^ 59
def prefixEnd_188996 : Nat := 4983230072969 + 3 ^ 40 * 188996 * 2
def baseEnd_188996 : Nat := 798730780059652559513

theorem tailTrace_188996 : CollatzResearch.WordTrace tailWord_188996 prefixEnd_188996 798730780059652559513 := by
  unfold tailWord_188996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446625211653622396065421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4595500282204829861420561 3446625211653622396065421)
  ·
    refine ⟨1292484454370108398524533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3446625211653622396065421 1292484454370108398524533)
    ·
      refine ⟨121170417597197662361675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1292484454370108398524533 121170417597197662361675)
      ·
        refine ⟨181755626395796493542513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121170417597197662361675 181755626395796493542513)
        ·
          refine ⟨136316719796847370156885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181755626395796493542513 136316719796847370156885)
          ·
            refine ⟨798730780059652559513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 136316719796847370156885 798730780059652559513)
            ·
              rfl

theorem cell22_188996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 9].length) (baseStart_188996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_188996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_188996 prefixEnd_188996 := by exact prefixLift 188996
  have htrace : WordTrace (prefixWord ++ tailWord_188996) baseStart_188996 baseEnd_188996 := by
    simpa [prefixWord, tailWord_188996, baseEnd_188996] using wordTrace_append hprefix tailTrace_188996
  have hstable : (prefixWord ++ tailWord_188996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188996).length < 2 ^ (prefixWord ++ tailWord_188996).sum := by decide
  have hdescent : baseEnd_188996 < baseStart_188996 := by decide
  rcases family_descends (prefixWord ++ tailWord_188996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189050 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_189050 : Nat := 118140960795 + 189050 * 2 ^ 59
def prefixEnd_189050 : Nat := 4983230072969 + 3 ^ 40 * 189050 * 2
def baseEnd_189050 : Nat := 64715678488393716470387

theorem tailTrace_189050 : CollatzResearch.WordTrace tailWord_189050 prefixEnd_189050 64715678488393716470387 := by
  unfold tailWord_189050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723804991277903003649151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4596813310074408009731069 1723804991277903003649151)
  ·
    refine ⟨2585707486916854505473727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1723804991277903003649151 2585707486916854505473727)
    ·
      refine ⟨3878561230375281758210591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585707486916854505473727 3878561230375281758210591)
      ·
        refine ⟨5817841845562922637315887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878561230375281758210591 5817841845562922637315887)
        ·
          refine ⟨8726762768344383955973831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817841845562922637315887 8726762768344383955973831)
          ·
            refine ⟨13090144152516575933960747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726762768344383955973831 13090144152516575933960747)
            ·
              refine ⟨19635216228774863900941121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13090144152516575933960747 19635216228774863900941121)
              ·
                refine ⟨14726412171581147925705841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19635216228774863900941121 14726412171581147925705841)
                ·
                  refine ⟨11044809128685860944279381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14726412171581147925705841 11044809128685860944279381)
                  ·
                    refine ⟨64715678488393716470387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 11044809128685860944279381 64715678488393716470387)
                    ·
                      rfl

theorem cell22_189050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_189050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189050 prefixEnd_189050 := by exact prefixLift 189050
  have htrace : WordTrace (prefixWord ++ tailWord_189050) baseStart_189050 baseEnd_189050 := by
    simpa [prefixWord, tailWord_189050, baseEnd_189050] using wordTrace_append hprefix tailTrace_189050
  have hstable : (prefixWord ++ tailWord_189050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189050).length < 2 ^ (prefixWord ++ tailWord_189050).sum := by decide
  have hdescent : baseEnd_189050 < baseStart_189050 := by decide
  rcases family_descends (prefixWord ++ tailWord_189050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189058 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_189058 : Nat := 118140960795 + 189058 * 2 ^ 59
def prefixEnd_189058 : Nat := 4983230072969 + 3 ^ 40 * 189058 * 2
def baseEnd_189058 : Nat := 21572805683961454090121

theorem tailTrace_189058 : CollatzResearch.WordTrace tailWord_189058 prefixEnd_189058 21572805683961454090121 := by
  unfold tailWord_189058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723877937270657345221957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4597007832721752920591885 1723877937270657345221957)
  ·
    refine ⟨323227113238248252229117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1723877937270657345221957 323227113238248252229117)
    ·
      refine ⟨121210167464343094585919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323227113238248252229117 121210167464343094585919)
      ·
        refine ⟨181815251196514641878879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121210167464343094585919 181815251196514641878879)
        ·
          refine ⟨272722876794771962818319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181815251196514641878879 272722876794771962818319)
          ·
            refine ⟨409084315192157944227479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272722876794771962818319 409084315192157944227479)
            ·
              refine ⟨613626472788236916341219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409084315192157944227479 613626472788236916341219)
              ·
                refine ⟨920439709182355374511829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613626472788236916341219 920439709182355374511829)
                ·
                  refine ⟨21572805683961454090121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 920439709182355374511829 21572805683961454090121)
                  ·
                    rfl

theorem cell22_189058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_189058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189058 prefixEnd_189058 := by exact prefixLift 189058
  have htrace : WordTrace (prefixWord ++ tailWord_189058) baseStart_189058 baseEnd_189058 := by
    simpa [prefixWord, tailWord_189058, baseEnd_189058] using wordTrace_append hprefix tailTrace_189058
  have hstable : (prefixWord ++ tailWord_189058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189058).length < 2 ^ (prefixWord ++ tailWord_189058).sum := by decide
  have hdescent : baseEnd_189058 < baseStart_189058 := by decide
  rcases family_descends (prefixWord ++ tailWord_189058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189084 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_189084 : Nat := 118140960795 + 189084 * 2 ^ 59
def prefixEnd_189084 : Nat := 4983230072969 + 3 ^ 40 * 189084 * 2
def baseEnd_189084 : Nat := 64727317383228961120283

theorem tailTrace_189084 : CollatzResearch.WordTrace tailWord_189084 prefixEnd_189084 64727317383228961120283 := by
  unfold tailWord_189084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448230023494217910667153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4597640031325623880889537 3448230023494217910667153)
  ·
    refine ⟨2586172517620663433000365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3448230023494217910667153 2586172517620663433000365)
    ·
      refine ⟨969814694107748787375137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2586172517620663433000365 969814694107748787375137)
      ·
        refine ⟨727361020580811590531353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969814694107748787375137 727361020580811590531353)
        ·
          refine ⟨545520765435608692898515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727361020580811590531353 545520765435608692898515)
          ·
            refine ⟨818281148153413039347773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545520765435608692898515 818281148153413039347773)
            ·
              refine ⟨306855430557529889755415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818281148153413039347773 306855430557529889755415)
              ·
                refine ⟨460283145836294834633123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306855430557529889755415 460283145836294834633123)
                ·
                  refine ⟨690424718754442251949685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460283145836294834633123 690424718754442251949685)
                  ·
                    refine ⟨64727317383228961120283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 690424718754442251949685 64727317383228961120283)
                    ·
                      rfl

theorem cell22_189084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_189084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189084 prefixEnd_189084 := by exact prefixLift 189084
  have htrace : WordTrace (prefixWord ++ tailWord_189084) baseStart_189084 baseEnd_189084 := by
    simpa [prefixWord, tailWord_189084, baseEnd_189084] using wordTrace_append hprefix tailTrace_189084
  have hstable : (prefixWord ++ tailWord_189084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189084).length < 2 ^ (prefixWord ++ tailWord_189084).sum := by decide
  have hdescent : baseEnd_189084 < baseStart_189084 := by decide
  rcases family_descends (prefixWord ++ tailWord_189084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189174 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_189174 : Nat := 118140960795 + 189174 * 2 ^ 59
def prefixEnd_189174 : Nat := 4983230072969 + 3 ^ 40 * 189174 * 2
def baseEnd_189174 : Nat := 64758126222498726370007

theorem tailTrace_189174 : CollatzResearch.WordTrace tailWord_189174 prefixEnd_189174 64758126222498726370007 := by
  unfold tailWord_189174
  simp only [CollatzResearch.WordTrace]
  refine ⟨431233913541398824506911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4599828411108254128073717 431233913541398824506911)
  ·
    refine ⟨646850870312098236760367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431233913541398824506911 646850870312098236760367)
    ·
      refine ⟨970276305468147355140551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646850870312098236760367 970276305468147355140551)
      ·
        refine ⟨1455414458202221032710827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970276305468147355140551 1455414458202221032710827)
        ·
          refine ⟨2183121687303331549066241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455414458202221032710827 2183121687303331549066241)
          ·
            refine ⟨1637341265477498661799681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183121687303331549066241 1637341265477498661799681)
            ·
              refine ⟨1228005949108123996349761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637341265477498661799681 1228005949108123996349761)
              ·
                refine ⟨921004461831092997262321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228005949108123996349761 921004461831092997262321)
                ·
                  refine ⟨690753346373319747946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921004461831092997262321 690753346373319747946741)
                  ·
                    refine ⟨64758126222498726370007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 690753346373319747946741 64758126222498726370007)
                    ·
                      rfl

theorem cell22_189174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_189174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189174 prefixEnd_189174 := by exact prefixLift 189174
  have htrace : WordTrace (prefixWord ++ tailWord_189174) baseStart_189174 baseEnd_189174 := by
    simpa [prefixWord, tailWord_189174, baseEnd_189174] using wordTrace_append hprefix tailTrace_189174
  have hstable : (prefixWord ++ tailWord_189174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189174).length < 2 ^ (prefixWord ++ tailWord_189174).sum := by decide
  have hdescent : baseEnd_189174 < baseStart_189174 := by decide
  rcases family_descends (prefixWord ++ tailWord_189174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189180 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_189180 : Nat := 118140960795 + 189180 * 2 ^ 59
def prefixEnd_189180 : Nat := 4983230072969 + 3 ^ 40 * 189180 * 2
def baseEnd_189180 : Nat := 64760180145116710719989

theorem tailTrace_189180 : CollatzResearch.WordTrace tailWord_189180 prefixEnd_189180 64760180145116710719989 := by
  unfold tailWord_189180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449980727320322108414497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4599974303093762811219329 3449980727320322108414497)
  ·
    refine ⟨2587485545490241581310873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3449980727320322108414497 2587485545490241581310873)
    ·
      refine ⟨1940614159117681185983155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2587485545490241581310873 1940614159117681185983155)
      ·
        refine ⟨2910921238676521778974733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940614159117681185983155 2910921238676521778974733)
        ·
          refine ⟨1091595464503695667115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2910921238676521778974733 1091595464503695667115525)
          ·
            refine ⟨204674149594442937584161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1091595464503695667115525 204674149594442937584161)
            ·
              refine ⟨153505612195832203188121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204674149594442937584161 153505612195832203188121)
              ·
                refine ⟨115129209146874152391091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153505612195832203188121 115129209146874152391091)
                ·
                  refine ⟨172693813720311228586637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115129209146874152391091 172693813720311228586637)
                  ·
                    refine ⟨64760180145116710719989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172693813720311228586637 64760180145116710719989)
                    ·
                      rfl

theorem cell22_189180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_189180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189180 prefixEnd_189180 := by exact prefixLift 189180
  have htrace : WordTrace (prefixWord ++ tailWord_189180) baseStart_189180 baseEnd_189180 := by
    simpa [prefixWord, tailWord_189180, baseEnd_189180] using wordTrace_append hprefix tailTrace_189180
  have hstable : (prefixWord ++ tailWord_189180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189180).length < 2 ^ (prefixWord ++ tailWord_189180).sum := by decide
  have hdescent : baseEnd_189180 < baseStart_189180 := by decide
  rcases family_descends (prefixWord ++ tailWord_189180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189187 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 6]
def baseStart_189187 : Nat := 118140960795 + 189187 * 2 ^ 59
def prefixEnd_189187 : Nat := 4983230072969 + 3 ^ 40 * 189187 * 2
def baseEnd_189187 : Nat := 21587525462723675264989

theorem tailTrace_189187 : CollatzResearch.WordTrace tailWord_189187 prefixEnd_189187 21587525462723675264989 := by
  unfold tailWord_189187
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900216765615284412333815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600144510410189608222543 6900216765615284412333815)
  ·
    refine ⟨10350325148422926618500723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900216765615284412333815 10350325148422926618500723)
    ·
      refine ⟨15525487722634389927751085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10350325148422926618500723 15525487722634389927751085)
      ·
        refine ⟨5822057895987896222906657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15525487722634389927751085 5822057895987896222906657)
        ·
          refine ⟨4366543421990922167179993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822057895987896222906657 4366543421990922167179993)
          ·
            refine ⟨3274907566493191625384995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366543421990922167179993 3274907566493191625384995)
            ·
              refine ⟨4912361349739787438077493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274907566493191625384995 4912361349739787438077493)
              ·
                refine ⟨460533876538105072319765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4912361349739787438077493 460533876538105072319765)
                ·
                  refine ⟨21587525462723675264989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 460533876538105072319765 21587525462723675264989)
                  ·
                    rfl

theorem cell22_189187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_189187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189187 prefixEnd_189187 := by exact prefixLift 189187
  have htrace : WordTrace (prefixWord ++ tailWord_189187) baseStart_189187 baseEnd_189187 := by
    simpa [prefixWord, tailWord_189187, baseEnd_189187] using wordTrace_append hprefix tailTrace_189187
  have hstable : (prefixWord ++ tailWord_189187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189187).length < 2 ^ (prefixWord ++ tailWord_189187).sum := by decide
  have hdescent : baseEnd_189187 < baseStart_189187 := by decide
  rcases family_descends (prefixWord ++ tailWord_189187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189219 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 4, 3]
def baseStart_189219 : Nat := 118140960795 + 189219 * 2 ^ 59
def prefixEnd_189219 : Nat := 4983230072969 + 3 ^ 40 * 189219 * 2
def baseEnd_189219 : Nat := 64773530642133608994869

theorem tailTrace_189219 : CollatzResearch.WordTrace tailWord_189219 prefixEnd_189219 64773530642133608994869 := by
  unfold tailWord_189219
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901383901499353877498711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600922600999569251665807 6901383901499353877498711)
  ·
    refine ⟨10352075852249030816248067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6901383901499353877498711 10352075852249030816248067)
    ·
      refine ⟨15528113778373546224372101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352075852249030816248067 15528113778373546224372101)
      ·
        refine ⟨2911521333445039917069769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15528113778373546224372101 2911521333445039917069769)
        ·
          refine ⟨2183641000083779937802327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911521333445039917069769 2183641000083779937802327)
          ·
            refine ⟨3275461500125669906703491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183641000083779937802327 3275461500125669906703491)
            ·
              refine ⟨4913192250188504860055237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275461500125669906703491 4913192250188504860055237)
              ·
                refine ⟨921223546910344661260357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4913192250188504860055237 921223546910344661260357)
                ·
                  refine ⟨172729415045689623986317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921223546910344661260357 172729415045689623986317)
                  ·
                    refine ⟨64773530642133608994869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172729415045689623986317 64773530642133608994869)
                    ·
                      rfl

theorem cell22_189219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3].length) (baseStart_189219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189219 prefixEnd_189219 := by exact prefixLift 189219
  have htrace : WordTrace (prefixWord ++ tailWord_189219) baseStart_189219 baseEnd_189219 := by
    simpa [prefixWord, tailWord_189219, baseEnd_189219] using wordTrace_append hprefix tailTrace_189219
  have hstable : (prefixWord ++ tailWord_189219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189219).length < 2 ^ (prefixWord ++ tailWord_189219).sum := by decide
  have hdescent : baseEnd_189219 < baseStart_189219 := by decide
  rcases family_descends (prefixWord ++ tailWord_189219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189221 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 4]
def baseStart_189221 : Nat := 118140960795 + 189221 * 2 ^ 59
def prefixEnd_189221 : Nat := 4983230072969 + 3 ^ 40 * 189221 * 2
def baseEnd_189221 : Nat := 21591405094335423481621

theorem tailTrace_189221 : CollatzResearch.WordTrace tailWord_189221 prefixEnd_189221 21591405094335423481621 := by
  unfold tailWord_189221
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901456847492108219071517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600971231661405479381011 6901456847492108219071517)
  ·
    refine ⟨2588046317809540582151819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6901456847492108219071517 2588046317809540582151819)
    ·
      refine ⟨3882069476714310873227729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588046317809540582151819 3882069476714310873227729)
      ·
        refine ⟨2911552107535733154920797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3882069476714310873227729 2911552107535733154920797)
        ·
          refine ⟨1091832040325899933095299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2911552107535733154920797 1091832040325899933095299)
          ·
            refine ⟨1637748060488849899642949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091832040325899933095299 1637748060488849899642949)
            ·
              refine ⟨307077761341659356183053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1637748060488849899642949 307077761341659356183053)
              ·
                refine ⟨115154160503122258568645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307077761341659356183053 115154160503122258568645)
                ·
                  refine ⟨21591405094335423481621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115154160503122258568645 21591405094335423481621)
                  ·
                    rfl

theorem cell22_189221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_189221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189221 prefixEnd_189221 := by exact prefixLift 189221
  have htrace : WordTrace (prefixWord ++ tailWord_189221) baseStart_189221 baseEnd_189221 := by
    simpa [prefixWord, tailWord_189221, baseEnd_189221] using wordTrace_append hprefix tailTrace_189221
  have hstable : (prefixWord ++ tailWord_189221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189221).length < 2 ^ (prefixWord ++ tailWord_189221).sum := by decide
  have hdescent : baseEnd_189221 < baseStart_189221 := by decide
  rcases family_descends (prefixWord ++ tailWord_189221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189234 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_189234 : Nat := 118140960795 + 189234 * 2 ^ 59
def prefixEnd_189234 : Nat := 4983230072969 + 3 ^ 40 * 189234 * 2
def baseEnd_189234 : Nat := 64778665448678569869823

theorem tailTrace_189234 : CollatzResearch.WordTrace tailWord_189234 prefixEnd_189234 64778665448678569869823 := by
  unfold tailWord_189234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725482749111252859823689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4601287330963340959529837 1725482749111252859823689)
  ·
    refine ⟨1294112061833439644867767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1725482749111252859823689 1294112061833439644867767)
    ·
      refine ⟨1941168092750159467301651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1294112061833439644867767 1941168092750159467301651)
      ·
        refine ⟨2911752139125239200952477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941168092750159467301651 2911752139125239200952477)
        ·
          refine ⟨1091907052171964700357179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2911752139125239200952477 1091907052171964700357179)
          ·
            refine ⟨1637860578257947050535769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091907052171964700357179 1637860578257947050535769)
            ·
              refine ⟨1228395433693460287901827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637860578257947050535769 1228395433693460287901827)
              ·
                refine ⟨1842593150540190431852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228395433693460287901827 1842593150540190431852741)
                ·
                  refine ⟨345486215726285705972389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842593150540190431852741 345486215726285705972389)
                  ·
                    refine ⟨64778665448678569869823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345486215726285705972389 64778665448678569869823)
                    ·
                      rfl

theorem cell22_189234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_189234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189234 prefixEnd_189234 := by exact prefixLift 189234
  have htrace : WordTrace (prefixWord ++ tailWord_189234) baseStart_189234 baseEnd_189234 := by
    simpa [prefixWord, tailWord_189234, baseEnd_189234] using wordTrace_append hprefix tailTrace_189234
  have hstable : (prefixWord ++ tailWord_189234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189234).length < 2 ^ (prefixWord ++ tailWord_189234).sum := by decide
  have hdescent : baseEnd_189234 < baseStart_189234 := by decide
  rcases family_descends (prefixWord ++ tailWord_189234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189238 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_189238 : Nat := 118140960795 + 189238 * 2 ^ 59
def prefixEnd_189238 : Nat := 4983230072969 + 3 ^ 40 * 189238 * 2
def baseEnd_189238 : Nat := 21593344910141297589937

theorem tailTrace_189238 : CollatzResearch.WordTrace tailWord_189238 prefixEnd_189238 21593344910141297589937 := by
  unfold tailWord_189238
  simp only [CollatzResearch.WordTrace]
  refine ⟨431379805526907507652523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4601384592287013414960245 431379805526907507652523)
  ·
    refine ⟨647069708290361261478785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431379805526907507652523 647069708290361261478785)
    ·
      refine ⟨485302281217770946109089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 647069708290361261478785 485302281217770946109089)
      ·
        refine ⟨363976710913328209581817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485302281217770946109089 363976710913328209581817)
        ·
          refine ⟨272982533184996157186363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363976710913328209581817 272982533184996157186363)
          ·
            refine ⟨409473799777494235779545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272982533184996157186363 409473799777494235779545)
            ·
              refine ⟨307105349833120676834659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409473799777494235779545 307105349833120676834659)
              ·
                refine ⟨460658024749681015251989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307105349833120676834659 460658024749681015251989)
                ·
                  refine ⟨21593344910141297589937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 460658024749681015251989 21593344910141297589937)
                  ·
                    rfl

theorem cell22_189238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_189238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189238 prefixEnd_189238 := by exact prefixLift 189238
  have htrace : WordTrace (prefixWord ++ tailWord_189238) baseStart_189238 baseEnd_189238 := by
    simpa [prefixWord, tailWord_189238, baseEnd_189238] using wordTrace_append hprefix tailTrace_189238
  have hstable : (prefixWord ++ tailWord_189238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189238).length < 2 ^ (prefixWord ++ tailWord_189238).sum := by decide
  have hdescent : baseEnd_189238 < baseStart_189238 := by decide
  rcases family_descends (prefixWord ++ tailWord_189238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189298 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_189298 : Nat := 118140960795 + 189298 * 2 ^ 59
def prefixEnd_189298 : Nat := 4983230072969 + 3 ^ 40 * 189298 * 2
def baseEnd_189298 : Nat := 64800573956603736269627

theorem tailTrace_189298 : CollatzResearch.WordTrace tailWord_189298 prefixEnd_189298 64800573956603736269627 := by
  unfold tailWord_189298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726066317053287592406137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4602843512142100246416365 1726066317053287592406137)
  ·
    refine ⟨1294549737789965694304603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1726066317053287592406137 1294549737789965694304603)
    ·
      refine ⟨1941824606684948541456905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1294549737789965694304603 1941824606684948541456905)
      ·
        refine ⟨1456368455013711406092679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1941824606684948541456905 1456368455013711406092679)
        ·
          refine ⟨2184552682520567109139019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456368455013711406092679 2184552682520567109139019)
          ·
            refine ⟨3276829023780850663708529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184552682520567109139019 3276829023780850663708529)
            ·
              refine ⟨2457621767835637997781397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3276829023780850663708529 2457621767835637997781397)
              ·
                refine ⟨115201020367295531146003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2457621767835637997781397 115201020367295531146003)
                ·
                  refine ⟨172801530550943296719005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115201020367295531146003 172801530550943296719005)
                  ·
                    refine ⟨64800573956603736269627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172801530550943296719005 64800573956603736269627)
                    ·
                      rfl

theorem cell22_189298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_189298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189298 prefixEnd_189298 := by exact prefixLift 189298
  have htrace : WordTrace (prefixWord ++ tailWord_189298) baseStart_189298 baseEnd_189298 := by
    simpa [prefixWord, tailWord_189298, baseEnd_189298] using wordTrace_append hprefix tailTrace_189298
  have hstable : (prefixWord ++ tailWord_189298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189298).length < 2 ^ (prefixWord ++ tailWord_189298).sum := by decide
  have hdescent : baseEnd_189298 < baseStart_189298 := by decide
  rcases family_descends (prefixWord ++ tailWord_189298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189309 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_189309 : Nat := 118140960795 + 189309 * 2 ^ 59
def prefixEnd_189309 : Nat := 4983230072969 + 3 ^ 40 * 189309 * 2
def baseEnd_189309 : Nat := 64804339481403374244593

theorem tailTrace_189309 : CollatzResearch.WordTrace tailWord_189309 prefixEnd_189309 64804339481403374244593 := by
  unfold tailWord_189309
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904666471173299248274981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4603110980782199498849987 6904666471173299248274981)
  ·
    refine ⟨1294624963344993609051559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6904666471173299248274981 1294624963344993609051559)
    ·
      refine ⟨1941937445017490413577339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1294624963344993609051559 1941937445017490413577339)
      ·
        refine ⟨2912906167526235620366009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941937445017490413577339 2912906167526235620366009)
        ·
          refine ⟨2184679625644676715274507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2912906167526235620366009 2184679625644676715274507)
          ·
            refine ⟨3277019438467015072911761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184679625644676715274507 3277019438467015072911761)
            ·
              refine ⟨2457764578850261304683821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277019438467015072911761 2457764578850261304683821)
              ·
                refine ⟨921661717068847989256433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2457764578850261304683821 921661717068847989256433)
                ·
                  refine ⟨691246287801635991942325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921661717068847989256433 691246287801635991942325)
                  ·
                    refine ⟨64804339481403374244593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 691246287801635991942325 64804339481403374244593)
                    ·
                      rfl

theorem cell22_189309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_189309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189309 prefixEnd_189309 := by exact prefixLift 189309
  have htrace : WordTrace (prefixWord ++ tailWord_189309) baseStart_189309 baseEnd_189309 := by
    simpa [prefixWord, tailWord_189309, baseEnd_189309] using wordTrace_append hprefix tailTrace_189309
  have hstable : (prefixWord ++ tailWord_189309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189309).length < 2 ^ (prefixWord ++ tailWord_189309).sum := by decide
  have hdescent : baseEnd_189309 < baseStart_189309 := by decide
  rcases family_descends (prefixWord ++ tailWord_189309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189311 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 5]
def baseStart_189311 : Nat := 118140960795 + 189311 * 2 ^ 59
def prefixEnd_189311 : Nat := 4983230072969 + 3 ^ 40 * 189311 * 2
def baseEnd_189311 : Nat := 21601674707425345231529

theorem tailTrace_189311 : CollatzResearch.WordTrace tailWord_189311 prefixEnd_189311 21601674707425345231529 := by
  unfold tailWord_189311
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904739417166053589847787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4603159611444035726565191 6904739417166053589847787)
  ·
    refine ⟨10357109125749080384771681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6904739417166053589847787 10357109125749080384771681)
    ·
      refine ⟨7767831844311810288578761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10357109125749080384771681 7767831844311810288578761)
      ·
        refine ⟨5825873883233857716434071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7767831844311810288578761 5825873883233857716434071)
        ·
          refine ⟨8738810824850786574651107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5825873883233857716434071 8738810824850786574651107)
          ·
            refine ⟨13108216237276179861976661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738810824850786574651107 13108216237276179861976661)
            ·
              refine ⟨153611909030580232757539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 13108216237276179861976661 153611909030580232757539)
              ·
                refine ⟨230417863545870349136309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153611909030580232757539 230417863545870349136309)
                ·
                  refine ⟨21601674707425345231529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230417863545870349136309 21601674707425345231529)
                  ·
                    rfl

theorem cell22_189311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 5].length) (baseStart_189311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189311 prefixEnd_189311 := by exact prefixLift 189311
  have htrace : WordTrace (prefixWord ++ tailWord_189311) baseStart_189311 baseEnd_189311 := by
    simpa [prefixWord, tailWord_189311, baseEnd_189311] using wordTrace_append hprefix tailTrace_189311
  have hstable : (prefixWord ++ tailWord_189311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189311).length < 2 ^ (prefixWord ++ tailWord_189311).sum := by decide
  have hdescent : baseEnd_189311 < baseStart_189311 := by decide
  rcases family_descends (prefixWord ++ tailWord_189311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189356 : List Nat := [2, 2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_189356 : Nat := 118140960795 + 189356 * 2 ^ 59
def prefixEnd_189356 : Nat := 4983230072969 + 3 ^ 40 * 189356 * 2
def baseEnd_189356 : Nat := 21606809513970306106483

theorem tailTrace_189356 : CollatzResearch.WordTrace tailWord_189356 prefixEnd_189356 21606809513970306106483 := by
  unfold tailWord_189356
  simp only [CollatzResearch.WordTrace]
  refine ⟨3453190351001513137617961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4604253801335350850157281 3453190351001513137617961)
  ·
    refine ⟨2589892763251134853213471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3453190351001513137617961 2589892763251134853213471)
    ·
      refine ⟨3884839144876702279820207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589892763251134853213471 3884839144876702279820207)
      ·
        refine ⟨5827258717315053419730311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884839144876702279820207 5827258717315053419730311)
        ·
          refine ⟨8740888075972580129595467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827258717315053419730311 8740888075972580129595467)
          ·
            refine ⟨13111332113958870194393201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740888075972580129595467 13111332113958870194393201)
            ·
              refine ⟨9833499085469152645794901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13111332113958870194393201 9833499085469152645794901)
              ·
                refine ⟨115236317407841632567909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9833499085469152645794901 115236317407841632567909)
                ·
                  refine ⟨21606809513970306106483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115236317407841632567909 21606809513970306106483)
                  ·
                    rfl

theorem cell22_189356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_189356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189356 prefixEnd_189356 := by exact prefixLift 189356
  have htrace : WordTrace (prefixWord ++ tailWord_189356) baseStart_189356 baseEnd_189356 := by
    simpa [prefixWord, tailWord_189356, baseEnd_189356] using wordTrace_append hprefix tailTrace_189356
  have hstable : (prefixWord ++ tailWord_189356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189356).length < 2 ^ (prefixWord ++ tailWord_189356).sum := by decide
  have hdescent : baseEnd_189356 < baseStart_189356 := by decide
  rcases family_descends (prefixWord ++ tailWord_189356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189405 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_189405 : Nat := 118140960795 + 189405 * 2 ^ 59
def prefixEnd_189405 : Nat := 4983230072969 + 3 ^ 40 * 189405 * 2
def baseEnd_189405 : Nat := 64837202243291123844299

theorem tailTrace_189405 : CollatzResearch.WordTrace tailWord_189405 prefixEnd_189405 64837202243291123844299 := by
  unfold tailWord_189405
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908167878825507643769669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4605445252550338429179779 6908167878825507643769669)
  ·
    refine ⟨1295281477279782683206813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6908167878825507643769669 1295281477279782683206813)
    ·
      refine ⟨485730553979918506202555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1295281477279782683206813 485730553979918506202555)
      ·
        refine ⟨728595830969877759303833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485730553979918506202555 728595830969877759303833)
        ·
          refine ⟨546446873227408319477875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728595830969877759303833 546446873227408319477875)
          ·
            refine ⟨819670309841112479216813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546446873227408319477875 819670309841112479216813)
            ·
              refine ⟨307376366190417179706305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819670309841112479216813 307376366190417179706305)
              ·
                refine ⟨230532274642812884779729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307376366190417179706305 230532274642812884779729)
                ·
                  refine ⟨172899205982109663584797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230532274642812884779729 172899205982109663584797)
                  ·
                    refine ⟨64837202243291123844299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172899205982109663584797 64837202243291123844299)
                    ·
                      rfl

theorem cell22_189405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_189405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189405 prefixEnd_189405 := by exact prefixLift 189405
  have htrace : WordTrace (prefixWord ++ tailWord_189405) baseStart_189405 baseEnd_189405 := by
    simpa [prefixWord, tailWord_189405, baseEnd_189405] using wordTrace_append hprefix tailTrace_189405
  have hstable : (prefixWord ++ tailWord_189405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189405).length < 2 ^ (prefixWord ++ tailWord_189405).sum := by decide
  have hdescent : baseEnd_189405 < baseStart_189405 := by decide
  rcases family_descends (prefixWord ++ tailWord_189405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189422 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_189422 : Nat := 118140960795 + 189422 * 2 ^ 59
def prefixEnd_189422 : Nat := 4983230072969 + 3 ^ 40 * 189422 * 2
def baseEnd_189422 : Nat := 64843021690708746169247

theorem tailTrace_189422 : CollatzResearch.WordTrace tailWord_189422 prefixEnd_189422 64843021690708746169247 := by
  unfold tailWord_189422
  simp only [CollatzResearch.WordTrace]
  refine ⟨863598489970489943392315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4605858613175946364759013 863598489970489943392315)
  ·
    refine ⟨1295397734955734915088473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863598489970489943392315 1295397734955734915088473)
    ·
      refine ⟨971548301216801186316355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1295397734955734915088473 971548301216801186316355)
      ·
        refine ⟨1457322451825201779474533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971548301216801186316355 1457322451825201779474533)
        ·
          refine ⟨273247959717225333651475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1457322451825201779474533 273247959717225333651475)
          ·
            refine ⟨409871939575838000477213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273247959717225333651475 409871939575838000477213)
            ·
              refine ⟨153701977340939250178955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409871939575838000477213 153701977340939250178955)
              ·
                refine ⟨230552966011408875268433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153701977340939250178955 230552966011408875268433)
                ·
                  refine ⟨172914724508556656451325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230552966011408875268433 172914724508556656451325)
                  ·
                    refine ⟨64843021690708746169247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172914724508556656451325 64843021690708746169247)
                    ·
                      rfl

theorem cell22_189422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_189422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189422 prefixEnd_189422 := by exact prefixLift 189422
  have htrace : WordTrace (prefixWord ++ tailWord_189422) baseStart_189422 baseEnd_189422 := by
    simpa [prefixWord, tailWord_189422, baseEnd_189422] using wordTrace_append hprefix tailTrace_189422
  have hstable : (prefixWord ++ tailWord_189422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189422).length < 2 ^ (prefixWord ++ tailWord_189422).sum := by decide
  have hdescent : baseEnd_189422 < baseStart_189422 := by decide
  rcases family_descends (prefixWord ++ tailWord_189422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189523 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 2, 3]
def baseStart_189523 : Nat := 118140960795 + 189523 * 2 ^ 59
def prefixEnd_189523 : Nat := 4983230072969 + 3 ^ 40 * 189523 * 2
def baseEnd_189523 : Nat := 64877596054778149393937

theorem tailTrace_189523 : CollatzResearch.WordTrace tailWord_189523 prefixEnd_189523 64877596054778149393937 := by
  unfold tailWord_189523
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912471692398013796565223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4608314461598675864376815 6912471692398013796565223)
  ·
    refine ⟨10368707538597020694847835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6912471692398013796565223 10368707538597020694847835)
    ·
      refine ⟨15553061307895531042271753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368707538597020694847835 15553061307895531042271753)
      ·
        refine ⟨11664795980921648281703815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15553061307895531042271753 11664795980921648281703815)
        ·
          refine ⟨17497193971382472422555723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11664795980921648281703815 17497193971382472422555723)
          ·
            refine ⟨26245790957073708633833585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17497193971382472422555723 26245790957073708633833585)
            ·
              refine ⟨19684343217805281475375189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26245790957073708633833585 19684343217805281475375189)
              ·
                refine ⟨230675897083655642289553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19684343217805281475375189 230675897083655642289553)
                ·
                  refine ⟨173006922812741731717165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230675897083655642289553 173006922812741731717165)
                  ·
                    refine ⟨64877596054778149393937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173006922812741731717165 64877596054778149393937)
                    ·
                      rfl

theorem cell22_189523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3].length) (baseStart_189523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189523 prefixEnd_189523 := by exact prefixLift 189523
  have htrace : WordTrace (prefixWord ++ tailWord_189523) baseStart_189523 baseEnd_189523 := by
    simpa [prefixWord, tailWord_189523, baseEnd_189523] using wordTrace_append hprefix tailTrace_189523
  have hstable : (prefixWord ++ tailWord_189523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189523).length < 2 ^ (prefixWord ++ tailWord_189523).sum := by decide
  have hdescent : baseEnd_189523 < baseStart_189523 := by decide
  rcases family_descends (prefixWord ++ tailWord_189523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189636 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_189636 : Nat := 118140960795 + 189636 * 2 ^ 59
def prefixEnd_189636 : Nat := 4983230072969 + 3 ^ 40 * 189636 * 2
def baseEnd_189636 : Nat := 64916278264083521318591

theorem tailTrace_189636 : CollatzResearch.WordTrace tailWord_189636 prefixEnd_189636 64916278264083521318591 := by
  unfold tailWord_189636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458296570494317047714381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4611062093992422730285841 3458296570494317047714381)
  ·
    refine ⟨1296861213935368892892893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3458296570494317047714381 1296861213935368892892893)
    ·
      refine ⟨486322955225763334834835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1296861213935368892892893 486322955225763334834835)
      ·
        refine ⟨729484432838645002252253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486322955225763334834835 729484432838645002252253)
        ·
          refine ⟨273556662314491875844595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 729484432838645002252253 273556662314491875844595)
          ·
            refine ⟨410334993471737813766893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273556662314491875844595 410334993471737813766893)
            ·
              refine ⟨153875622551901680162585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410334993471737813766893 153875622551901680162585)
              ·
                refine ⟨115406716913926260121939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153875622551901680162585 115406716913926260121939)
                ·
                  refine ⟨173110075370889390182909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115406716913926260121939 173110075370889390182909)
                  ·
                    refine ⟨64916278264083521318591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173110075370889390182909 64916278264083521318591)
                    ·
                      rfl

theorem cell22_189636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_189636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189636 prefixEnd_189636 := by exact prefixLift 189636
  have htrace : WordTrace (prefixWord ++ tailWord_189636) baseStart_189636 baseEnd_189636 := by
    simpa [prefixWord, tailWord_189636, baseEnd_189636] using wordTrace_append hprefix tailTrace_189636
  have hstable : (prefixWord ++ tailWord_189636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189636).length < 2 ^ (prefixWord ++ tailWord_189636).sum := by decide
  have hdescent : baseEnd_189636 < baseStart_189636 := by decide
  rcases family_descends (prefixWord ++ tailWord_189636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189658 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_189658 : Nat := 118140960795 + 189658 * 2 ^ 59
def prefixEnd_189658 : Nat := 4983230072969 + 3 ^ 40 * 189658 * 2
def baseEnd_189658 : Nat := 64923809313682797268523

theorem tailTrace_189658 : CollatzResearch.WordTrace tailWord_189658 prefixEnd_189658 64923809313682797268523 := by
  unfold tailWord_189658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729348886727232963182407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4611597031272621235153085 1729348886727232963182407)
  ·
    refine ⟨2594023330090849444773611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1729348886727232963182407 2594023330090849444773611)
    ·
      refine ⟨3891034995136274167160417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594023330090849444773611 3891034995136274167160417)
      ·
        refine ⟨2918276246352205625370313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3891034995136274167160417 2918276246352205625370313)
        ·
          refine ⟨2188707184764154219027735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2918276246352205625370313 2188707184764154219027735)
          ·
            refine ⟨3283060777146231328541603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188707184764154219027735 3283060777146231328541603)
            ·
              refine ⟨4924591165719346992812405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283060777146231328541603 4924591165719346992812405)
              ·
                refine ⟨461680421786188780576163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4924591165719346992812405 461680421786188780576163)
                ·
                  refine ⟨692520632679283170864245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461680421786188780576163 692520632679283170864245)
                  ·
                    refine ⟨64923809313682797268523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 692520632679283170864245 64923809313682797268523)
                    ·
                      rfl

theorem cell22_189658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_189658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189658 prefixEnd_189658 := by exact prefixLift 189658
  have htrace : WordTrace (prefixWord ++ tailWord_189658) baseStart_189658 baseEnd_189658 := by
    simpa [prefixWord, tailWord_189658, baseEnd_189658] using wordTrace_append hprefix tailTrace_189658
  have hstable : (prefixWord ++ tailWord_189658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189658).length < 2 ^ (prefixWord ++ tailWord_189658).sum := by decide
  have hdescent : baseEnd_189658 < baseStart_189658 := by decide
  rcases family_descends (prefixWord ++ tailWord_189658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189694 : List Nat := [4, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_189694 : Nat := 118140960795 + 189694 * 2 ^ 59
def prefixEnd_189694 : Nat := 4983230072969 + 3 ^ 40 * 189694 * 2
def baseEnd_189694 : Nat := 21645377616463567789471

theorem tailTrace_189694 : CollatzResearch.WordTrace tailWord_189694 prefixEnd_189694 21645377616463567789471 := by
  unfold tailWord_189694
  simp only [CollatzResearch.WordTrace]
  refine ⟨864838571847313750130017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4612472383185673334026757 864838571847313750130017)
  ·
    refine ⟨648628928885485312597513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 864838571847313750130017 648628928885485312597513)
    ·
      refine ⟨486471696664113984448135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 648628928885485312597513 486471696664113984448135)
      ·
        refine ⟨729707544996170976672203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486471696664113984448135 729707544996170976672203)
        ·
          refine ⟨1094561317494256465008305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729707544996170976672203 1094561317494256465008305)
          ·
            refine ⟨820920988120692348756229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1094561317494256465008305 820920988120692348756229)
            ·
              refine ⟨153922685272629815391793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 820920988120692348756229 153922685272629815391793)
              ·
                refine ⟨115442013954472361543845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153922685272629815391793 115442013954472361543845)
                ·
                  refine ⟨21645377616463567789471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115442013954472361543845 21645377616463567789471)
                  ·
                    rfl

theorem cell22_189694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_189694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189694 prefixEnd_189694 := by exact prefixLift 189694
  have htrace : WordTrace (prefixWord ++ tailWord_189694) baseStart_189694 baseEnd_189694 := by
    simpa [prefixWord, tailWord_189694, baseEnd_189694] using wordTrace_append hprefix tailTrace_189694
  have hstable : (prefixWord ++ tailWord_189694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189694).length < 2 ^ (prefixWord ++ tailWord_189694).sum := by decide
  have hdescent : baseEnd_189694 < baseStart_189694 := by decide
  rcases family_descends (prefixWord ++ tailWord_189694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189720 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_189720 : Nat := 118140960795 + 189720 * 2 ^ 59
def prefixEnd_189720 : Nat := 4983230072969 + 3 ^ 40 * 189720 * 2
def baseEnd_189720 : Nat := 64945033180735302218333

theorem tailTrace_189720 : CollatzResearch.WordTrace tailWord_189720 prefixEnd_189720 64945033180735302218333 := by
  unfold tailWord_189720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459828436342158220743307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4613104581789544294324409 3459828436342158220743307)
  ·
    refine ⟨5189742654513237331114961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459828436342158220743307 5189742654513237331114961)
    ·
      refine ⟨3892306990884927998336221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5189742654513237331114961 3892306990884927998336221)
      ·
        refine ⟨1459615121581847999376083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3892306990884927998336221 1459615121581847999376083)
        ·
          refine ⟨2189422682372771999064125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459615121581847999376083 2189422682372771999064125)
          ·
            refine ⟨821033505889789499649047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2189422682372771999064125 821033505889789499649047)
            ·
              refine ⟨1231550258834684249473571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821033505889789499649047 1231550258834684249473571)
              ·
                refine ⟨1847325388252026374210357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231550258834684249473571 1847325388252026374210357)
                ·
                  refine ⟨173186755148627472582221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1847325388252026374210357 173186755148627472582221)
                  ·
                    refine ⟨64945033180735302218333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173186755148627472582221 64945033180735302218333)
                    ·
                      rfl

theorem cell22_189720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_189720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189720 prefixEnd_189720 := by exact prefixLift 189720
  have htrace : WordTrace (prefixWord ++ tailWord_189720) baseStart_189720 baseEnd_189720 := by
    simpa [prefixWord, tailWord_189720, baseEnd_189720] using wordTrace_append hprefix tailTrace_189720
  have hstable : (prefixWord ++ tailWord_189720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189720).length < 2 ^ (prefixWord ++ tailWord_189720).sum := by decide
  have hdescent : baseEnd_189720 < baseStart_189720 := by decide
  rcases family_descends (prefixWord ++ tailWord_189720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189767 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 5]
def baseStart_189767 : Nat := 118140960795 + 189767 * 2 ^ 59
def prefixEnd_189767 : Nat := 4983230072969 + 3 ^ 40 * 189767 * 2
def baseEnd_189767 : Nat := 21653707413747615431063

theorem tailTrace_189767 : CollatzResearch.WordTrace tailWord_189767 prefixEnd_189767 21653707413747615431063 := by
  unfold tailWord_189767
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921371103514043468447555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4614247402342695645631703 6921371103514043468447555)
  ·
    refine ⟨10382056655271065202671333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921371103514043468447555 10382056655271065202671333)
    ·
      refine ⟨1946635622863324725500875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10382056655271065202671333 1946635622863324725500875)
      ·
        refine ⟨2919953434294987088251313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946635622863324725500875 2919953434294987088251313)
        ·
          refine ⟨2189965075721240316188485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919953434294987088251313 2189965075721240316188485)
          ·
            refine ⟨410618451697732559285341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2189965075721240316188485 410618451697732559285341)
            ·
              refine ⟨153981919386649709732003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410618451697732559285341 153981919386649709732003)
              ·
                refine ⟨230972879079974564598005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153981919386649709732003 230972879079974564598005)
                ·
                  refine ⟨21653707413747615431063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230972879079974564598005 21653707413747615431063)
                  ·
                    rfl

theorem cell22_189767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 5].length) (baseStart_189767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189767 prefixEnd_189767 := by exact prefixLift 189767
  have htrace : WordTrace (prefixWord ++ tailWord_189767) baseStart_189767 baseEnd_189767 := by
    simpa [prefixWord, tailWord_189767, baseEnd_189767] using wordTrace_append hprefix tailTrace_189767
  have hstable : (prefixWord ++ tailWord_189767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189767).length < 2 ^ (prefixWord ++ tailWord_189767).sum := by decide
  have hdescent : baseEnd_189767 < baseStart_189767 := by decide
  rcases family_descends (prefixWord ++ tailWord_189767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189917 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_189917 : Nat := 118140960795 + 189917 * 2 ^ 59
def prefixEnd_189917 : Nat := 4983230072969 + 3 ^ 40 * 189917 * 2
def baseEnd_189917 : Nat := 65012470306692455042729

theorem tailTrace_189917 : CollatzResearch.WordTrace tailWord_189917 prefixEnd_189917 65012470306692455042729 := by
  unfold tailWord_189917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926842052970619086408005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4617894701980412724272003 6926842052970619086408005)
  ·
    refine ⟨1298782884931991078701501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6926842052970619086408005 1298782884931991078701501)
    ·
      refine ⟨487043581849496654513063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1298782884931991078701501 487043581849496654513063)
      ·
        refine ⟨730565372774244981769595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487043581849496654513063 730565372774244981769595)
        ·
          refine ⟨1095848059161367472654393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730565372774244981769595 1095848059161367472654393)
          ·
            refine ⟨821886044371025604490795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095848059161367472654393 821886044371025604490795)
            ·
              refine ⟨1232829066556538406736193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821886044371025604490795 1232829066556538406736193)
              ·
                refine ⟨924621799917403805052145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232829066556538406736193 924621799917403805052145)
                ·
                  refine ⟨693466349938052853789109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924621799917403805052145 693466349938052853789109)
                  ·
                    refine ⟨65012470306692455042729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 693466349938052853789109 65012470306692455042729)
                    ·
                      rfl

theorem cell22_189917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_189917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189917 prefixEnd_189917 := by exact prefixLift 189917
  have htrace : WordTrace (prefixWord ++ tailWord_189917) baseStart_189917 baseEnd_189917 := by
    simpa [prefixWord, tailWord_189917, baseEnd_189917] using wordTrace_append hprefix tailTrace_189917
  have hstable : (prefixWord ++ tailWord_189917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189917).length < 2 ^ (prefixWord ++ tailWord_189917).sum := by decide
  have hdescent : baseEnd_189917 < baseStart_189917 := by decide
  rcases family_descends (prefixWord ++ tailWord_189917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189949 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_189949 : Nat := 118140960795 + 189949 * 2 ^ 59
def prefixEnd_189949 : Nat := 4983230072969 + 3 ^ 40 * 189949 * 2
def baseEnd_189949 : Nat := 65023424560655038242631

theorem tailTrace_189949 : CollatzResearch.WordTrace tailWord_189949 prefixEnd_189949 65023424560655038242631 := by
  unfold tailWord_189949
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928009188854688551572901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4618672792569792367715267 6928009188854688551572901)
  ·
    refine ⟨1299001722910254103419919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6928009188854688551572901 1299001722910254103419919)
    ·
      refine ⟨1948502584365381155129879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299001722910254103419919 1948502584365381155129879)
      ·
        refine ⟨2922753876548071732694819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948502584365381155129879 2922753876548071732694819)
        ·
          refine ⟨4384130814822107599042229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922753876548071732694819 4384130814822107599042229)
          ·
            refine ⟨411012263889572587410209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4384130814822107599042229 411012263889572587410209)
            ·
              refine ⟨308259197917179440557657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411012263889572587410209 308259197917179440557657)
              ·
                refine ⟨231194398437884580418243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308259197917179440557657 231194398437884580418243)
                ·
                  refine ⟨346791597656826870627365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231194398437884580418243 346791597656826870627365)
                  ·
                    refine ⟨65023424560655038242631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346791597656826870627365 65023424560655038242631)
                    ·
                      rfl

theorem cell22_189949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_189949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189949 prefixEnd_189949 := by exact prefixLift 189949
  have htrace : WordTrace (prefixWord ++ tailWord_189949) baseStart_189949 baseEnd_189949 := by
    simpa [prefixWord, tailWord_189949, baseEnd_189949] using wordTrace_append hprefix tailTrace_189949
  have hstable : (prefixWord ++ tailWord_189949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189949).length < 2 ^ (prefixWord ++ tailWord_189949).sum := by decide
  have hdescent : baseEnd_189949 < baseStart_189949 := by decide
  rcases family_descends (prefixWord ++ tailWord_189949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189981 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 4]
def baseStart_189981 : Nat := 118140960795 + 189981 * 2 ^ 59
def prefixEnd_189981 : Nat := 4983230072969 + 3 ^ 40 * 189981 * 2
def baseEnd_189981 : Nat := 21678126271539207147511

theorem tailTrace_189981 : CollatzResearch.WordTrace tailWord_189981 prefixEnd_189981 21678126271539207147511 := by
  unfold tailWord_189981
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929176324738758016737797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4619450883159172011158531 6929176324738758016737797)
  ·
    refine ⟨1299220560888517128138337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6929176324738758016737797 1299220560888517128138337)
    ·
      refine ⟨974415420666387846103753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1299220560888517128138337 974415420666387846103753)
      ·
        refine ⟨730811565499790884577815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 974415420666387846103753 730811565499790884577815)
        ·
          refine ⟨1096217348249686326866723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730811565499790884577815 1096217348249686326866723)
          ·
            refine ⟨1644326022374529490300085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096217348249686326866723 1644326022374529490300085)
            ·
              refine ⟨154155564597612139715633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1644326022374529490300085 154155564597612139715633)
              ·
                refine ⟨115616673448209104786725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154155564597612139715633 115616673448209104786725)
                ·
                  refine ⟨21678126271539207147511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115616673448209104786725 21678126271539207147511)
                  ·
                    rfl

theorem cell22_189981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_189981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_189981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_189981 prefixEnd_189981 := by exact prefixLift 189981
  have htrace : WordTrace (prefixWord ++ tailWord_189981) baseStart_189981 baseEnd_189981 := by
    simpa [prefixWord, tailWord_189981, baseEnd_189981] using wordTrace_append hprefix tailTrace_189981
  have hstable : (prefixWord ++ tailWord_189981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189981).length < 2 ^ (prefixWord ++ tailWord_189981).sum := by decide
  have hdescent : baseEnd_189981 < baseStart_189981 := by decide
  rcases family_descends (prefixWord ++ tailWord_189981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190052 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_190052 : Nat := 118140960795 + 190052 * 2 ^ 59
def prefixEnd_190052 : Nat := 4983230072969 + 3 ^ 40 * 190052 * 2
def baseEnd_190052 : Nat := 65058683565597102917315

theorem tailTrace_190052 : CollatzResearch.WordTrace tailWord_190052 prefixEnd_190052 65058683565597102917315 := by
  unfold tailWord_190052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465882953740768571286205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4621177271654358095048273 3465882953740768571286205)
  ·
    refine ⟨1299706107652788214232327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3465882953740768571286205 1299706107652788214232327)
    ·
      refine ⟨1949559161479182321348491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299706107652788214232327 1949559161479182321348491)
      ·
        refine ⟨2924338742218773482022737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949559161479182321348491 2924338742218773482022737)
        ·
          refine ⟨2193254056664080111517053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924338742218773482022737 2193254056664080111517053)
          ·
            refine ⟨822470271249030041818895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2193254056664080111517053 822470271249030041818895)
            ·
              refine ⟨1233705406873545062728343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822470271249030041818895 1233705406873545062728343)
              ·
                refine ⟨1850558110310317594092515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233705406873545062728343 1850558110310317594092515)
                ·
                  refine ⟨2775837165465476391138773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850558110310317594092515 2775837165465476391138773)
                  ·
                    refine ⟨65058683565597102917315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2775837165465476391138773 65058683565597102917315)
                    ·
                      rfl

theorem cell22_190052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_190052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190052 prefixEnd_190052 := by exact prefixLift 190052
  have htrace : WordTrace (prefixWord ++ tailWord_190052) baseStart_190052 baseEnd_190052 := by
    simpa [prefixWord, tailWord_190052, baseEnd_190052] using wordTrace_append hprefix tailTrace_190052
  have hstable : (prefixWord ++ tailWord_190052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190052).length < 2 ^ (prefixWord ++ tailWord_190052).sum := by decide
  have hdescent : baseEnd_190052 < baseStart_190052 := by decide
  rcases family_descends (prefixWord ++ tailWord_190052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190088 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_190088 : Nat := 118140960795 + 190088 * 2 ^ 59
def prefixEnd_190088 : Nat := 4983230072969 + 3 ^ 40 * 190088 * 2
def baseEnd_190088 : Nat := 21690335700435003005735

theorem tailTrace_190088 : CollatzResearch.WordTrace tailWord_190088 prefixEnd_190088 21690335700435003005735 := by
  unfold tailWord_190088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466539467675557645441459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4622052623567410193921945 3466539467675557645441459)
  ·
    refine ⟨5199809201513336468162189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3466539467675557645441459 5199809201513336468162189)
    ·
      refine ⟨1949928450567501175560821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5199809201513336468162189 1949928450567501175560821)
      ·
        refine ⟨182805792240703235208827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1949928450567501175560821 182805792240703235208827)
        ·
          refine ⟨274208688361054852813241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182805792240703235208827 274208688361054852813241)
          ·
            refine ⟨205656516270791139609931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274208688361054852813241 205656516270791139609931)
            ·
              refine ⟨308484774406186709414897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205656516270791139609931 308484774406186709414897)
              ·
                refine ⟨231363580804640032061173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308484774406186709414897 231363580804640032061173)
                ·
                  refine ⟨21690335700435003005735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231363580804640032061173 21690335700435003005735)
                  ·
                    rfl

theorem cell22_190088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_190088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190088 prefixEnd_190088 := by exact prefixLift 190088
  have htrace : WordTrace (prefixWord ++ tailWord_190088) baseStart_190088 baseEnd_190088 := by
    simpa [prefixWord, tailWord_190088, baseEnd_190088] using wordTrace_append hprefix tailTrace_190088
  have hstable : (prefixWord ++ tailWord_190088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190088).length < 2 ^ (prefixWord ++ tailWord_190088).sum := by decide
  have hdescent : baseEnd_190088 < baseStart_190088 := by decide
  rcases family_descends (prefixWord ++ tailWord_190088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190127 : List Nat := [1, 1, 2, 1, 2, 4, 3, 8]
def baseStart_190127 : Nat := 118140960795 + 190127 * 2 ^ 59
def prefixEnd_190127 : Nat := 4983230072969 + 3 ^ 40 * 190127 * 2
def baseEnd_190127 : Nat := 7231595288702434143565

theorem tailTrace_190127 : CollatzResearch.WordTrace tailWord_190127 prefixEnd_190127 7231595288702434143565 := by
  unfold tailWord_190127
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934501382209824951552635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4623000921473216634368423 6934501382209824951552635)
  ·
    refine ⟨10401752073314737427328953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6934501382209824951552635 10401752073314737427328953)
    ·
      refine ⟨7801314054986053070496715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10401752073314737427328953 7801314054986053070496715)
      ·
        refine ⟨11701971082479079605745073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801314054986053070496715 11701971082479079605745073)
        ·
          refine ⟨8776478311859309704308805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11701971082479079605745073 8776478311859309704308805)
          ·
            refine ⟨1645589683473620569557901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8776478311859309704308805 1645589683473620569557901)
            ·
              refine ⟨617096131302607713584213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645589683473620569557901 617096131302607713584213)
              ·
                refine ⟨7231595288702434143565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 617096131302607713584213 7231595288702434143565)
                ·
                  rfl

theorem cell22_190127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 8].length) (baseStart_190127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190127 prefixEnd_190127 := by exact prefixLift 190127
  have htrace : WordTrace (prefixWord ++ tailWord_190127) baseStart_190127 baseEnd_190127 := by
    simpa [prefixWord, tailWord_190127, baseEnd_190127] using wordTrace_append hprefix tailTrace_190127
  have hstable : (prefixWord ++ tailWord_190127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190127).length < 2 ^ (prefixWord ++ tailWord_190127).sum := by decide
  have hdescent : baseEnd_190127 < baseStart_190127 := by decide
  rcases family_descends (prefixWord ++ tailWord_190127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190150 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_190150 : Nat := 118140960795 + 190150 * 2 ^ 59
def prefixEnd_190150 : Nat := 4983230072969 + 3 ^ 40 * 190150 * 2
def baseEnd_190150 : Nat := 21697410322785837989005

theorem tailTrace_190150 : CollatzResearch.WordTrace tailWord_190150 prefixEnd_190150 21697410322785837989005 := by
  unfold tailWord_190150
  simp only [CollatzResearch.WordTrace]
  refine ⟨216729383160203121238747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4623560174084333253093269 216729383160203121238747)
  ·
    refine ⟨325094074740304681858121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216729383160203121238747 325094074740304681858121)
    ·
      refine ⟨243820556055228511393591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325094074740304681858121 243820556055228511393591)
      ·
        refine ⟨365730834082842767090387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243820556055228511393591 365730834082842767090387)
        ·
          refine ⟨548596251124264150635581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365730834082842767090387 548596251124264150635581)
          ·
            refine ⟨205723594171599056488343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548596251124264150635581 205723594171599056488343)
            ·
              refine ⟨308585391257398584732515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205723594171599056488343 308585391257398584732515)
              ·
                refine ⟨462878086886097877098773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308585391257398584732515 462878086886097877098773)
                ·
                  refine ⟨21697410322785837989005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 462878086886097877098773 21697410322785837989005)
                  ·
                    rfl

theorem cell22_190150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_190150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190150 prefixEnd_190150 := by exact prefixLift 190150
  have htrace : WordTrace (prefixWord ++ tailWord_190150) baseStart_190150 baseEnd_190150 := by
    simpa [prefixWord, tailWord_190150, baseEnd_190150] using wordTrace_append hprefix tailTrace_190150
  have hstable : (prefixWord ++ tailWord_190150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190150).length < 2 ^ (prefixWord ++ tailWord_190150).sum := by decide
  have hdescent : baseEnd_190150 < baseStart_190150 := by decide
  rcases family_descends (prefixWord ++ tailWord_190150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190204 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_190204 : Nat := 118140960795 + 190204 * 2 ^ 59
def prefixEnd_190204 : Nat := 4983230072969 + 3 ^ 40 * 190204 * 2
def baseEnd_190204 : Nat := 65110716271919373116849

theorem tailTrace_190204 : CollatzResearch.WordTrace tailWord_190204 prefixEnd_190204 65110716271919373116849 := by
  unfold tailWord_190204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468654901465433551052833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4624873201953911401403777 3468654901465433551052833)
  ·
    refine ⟨2601491176099075163289625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3468654901465433551052833 2601491176099075163289625)
    ·
      refine ⟨1951118382074306372467219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2601491176099075163289625 1951118382074306372467219)
      ·
        refine ⟨2926677573111459558700829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951118382074306372467219 2926677573111459558700829)
        ·
          refine ⟨1097504089916797334512811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2926677573111459558700829 1097504089916797334512811)
          ·
            refine ⟨1646256134875196001769217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097504089916797334512811 1646256134875196001769217)
            ·
              refine ⟨1234692101156397001326913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646256134875196001769217 1234692101156397001326913)
              ·
                refine ⟨926019075867297750995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234692101156397001326913 926019075867297750995185)
                ·
                  refine ⟨694514306900473313246389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 926019075867297750995185 694514306900473313246389)
                  ·
                    refine ⟨65110716271919373116849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 694514306900473313246389 65110716271919373116849)
                    ·
                      rfl

theorem cell22_190204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_190204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190204 prefixEnd_190204 := by exact prefixLift 190204
  have htrace : WordTrace (prefixWord ++ tailWord_190204) baseStart_190204 baseEnd_190204 := by
    simpa [prefixWord, tailWord_190204, baseEnd_190204] using wordTrace_append hprefix tailTrace_190204
  have hstable : (prefixWord ++ tailWord_190204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190204).length < 2 ^ (prefixWord ++ tailWord_190204).sum := by decide
  have hdescent : baseEnd_190204 < baseStart_190204 := by decide
  rcases family_descends (prefixWord ++ tailWord_190204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190210 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_190210 : Nat := 118140960795 + 190210 * 2 ^ 59
def prefixEnd_190210 : Nat := 4983230072969 + 3 ^ 40 * 190210 * 2
def baseEnd_190210 : Nat := 65112770194537357466831

theorem tailTrace_190210 : CollatzResearch.WordTrace tailWord_190210 prefixEnd_190210 65112770194537357466831 := by
  unfold tailWord_190210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734382160227282531706021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4625019093939420084549389 1734382160227282531706021)
  ·
    refine ⟨325196655042615474694879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1734382160227282531706021 325196655042615474694879)
    ·
      refine ⟨487794982563923212042319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325196655042615474694879 487794982563923212042319)
      ·
        refine ⟨731692473845884818063479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487794982563923212042319 731692473845884818063479)
        ·
          refine ⟨1097538710768827227095219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731692473845884818063479 1097538710768827227095219)
          ·
            refine ⟨1646308066153240840642829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097538710768827227095219 1646308066153240840642829)
            ·
              refine ⟨617365524807465315241061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646308066153240840642829 617365524807465315241061)
              ·
                refine ⟨115756035901399746607699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617365524807465315241061 115756035901399746607699)
                ·
                  refine ⟨173634053852099619911549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115756035901399746607699 173634053852099619911549)
                  ·
                    refine ⟨65112770194537357466831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173634053852099619911549 65112770194537357466831)
                    ·
                      rfl

theorem cell22_190210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_190210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190210 prefixEnd_190210 := by exact prefixLift 190210
  have htrace : WordTrace (prefixWord ++ tailWord_190210) baseStart_190210 baseEnd_190210 := by
    simpa [prefixWord, tailWord_190210, baseEnd_190210] using wordTrace_append hprefix tailTrace_190210
  have hstable : (prefixWord ++ tailWord_190210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190210).length < 2 ^ (prefixWord ++ tailWord_190210).sum := by decide
  have hdescent : baseEnd_190210 < baseStart_190210 := by decide
  rcases family_descends (prefixWord ++ tailWord_190210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190219 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_190219 : Nat := 118140960795 + 190219 * 2 ^ 59
def prefixEnd_190219 : Nat := 4983230072969 + 3 ^ 40 * 190219 * 2
def baseEnd_190219 : Nat := 65115851078464333991803

theorem tailTrace_190219 : CollatzResearch.WordTrace tailWord_190219 prefixEnd_190219 65115851078464333991803 := by
  unfold tailWord_190219
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937856897876524663901711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4625237931917683109267807 6937856897876524663901711)
  ·
    refine ⟨10406785346814786995852567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937856897876524663901711 10406785346814786995852567)
    ·
      refine ⟨15610178020222180493778851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406785346814786995852567 15610178020222180493778851)
      ·
        refine ⟨23415267030333270740668277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15610178020222180493778851 23415267030333270740668277)
        ·
          refine ⟨2195181284093744131937651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23415267030333270740668277 2195181284093744131937651)
          ·
            refine ⟨3292771926140616197906477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195181284093744131937651 3292771926140616197906477)
            ·
              refine ⟨1234789472302731074214929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3292771926140616197906477 1234789472302731074214929)
              ·
                refine ⟨926092104227048305661197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234789472302731074214929 926092104227048305661197)
                ·
                  refine ⟨347284539085143114622949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926092104227048305661197 347284539085143114622949)
                  ·
                    refine ⟨65115851078464333991803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347284539085143114622949 65115851078464333991803)
                    ·
                      rfl

theorem cell22_190219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_190219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190219 prefixEnd_190219 := by exact prefixLift 190219
  have htrace : WordTrace (prefixWord ++ tailWord_190219) baseStart_190219 baseEnd_190219 := by
    simpa [prefixWord, tailWord_190219, baseEnd_190219] using wordTrace_append hprefix tailTrace_190219
  have hstable : (prefixWord ++ tailWord_190219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190219).length < 2 ^ (prefixWord ++ tailWord_190219).sum := by decide
  have hdescent : baseEnd_190219 < baseStart_190219 := by decide
  rcases family_descends (prefixWord ++ tailWord_190219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190234 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_190234 : Nat := 118140960795 + 190234 * 2 ^ 59
def prefixEnd_190234 : Nat := 4983230072969 + 3 ^ 40 * 190234 * 2
def baseEnd_190234 : Nat := 21706995295003098288919

theorem tailTrace_190234 : CollatzResearch.WordTrace tailWord_190234 prefixEnd_190234 21706995295003098288919 := by
  unfold tailWord_190234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734600998205545556424439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4625602661881454817131837 1734600998205545556424439)
  ·
    refine ⟨2601901497308318334636659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1734600998205545556424439 2601901497308318334636659)
    ·
      refine ⟨3902852245962477501954989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601901497308318334636659 3902852245962477501954989)
      ·
        refine ⟨1463569592235929063233121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3902852245962477501954989 1463569592235929063233121)
        ·
          refine ⟨1097677194176946797424841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463569592235929063233121 1097677194176946797424841)
          ·
            refine ⟨823257895632710098068631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097677194176946797424841 823257895632710098068631)
            ·
              refine ⟨1234886843449065147102947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823257895632710098068631 1234886843449065147102947)
              ·
                refine ⟨1852330265173597720654421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234886843449065147102947 1852330265173597720654421)
                ·
                  refine ⟨21706995295003098288919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1852330265173597720654421 21706995295003098288919)
                  ·
                    rfl

theorem cell22_190234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_190234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190234 prefixEnd_190234 := by exact prefixLift 190234
  have htrace : WordTrace (prefixWord ++ tailWord_190234) baseStart_190234 baseEnd_190234 := by
    simpa [prefixWord, tailWord_190234, baseEnd_190234] using wordTrace_append hprefix tailTrace_190234
  have hstable : (prefixWord ++ tailWord_190234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190234).length < 2 ^ (prefixWord ++ tailWord_190234).sum := by decide
  have hdescent : baseEnd_190234 < baseStart_190234 := by decide
  rcases family_descends (prefixWord ++ tailWord_190234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190236 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_190236 : Nat := 118140960795 + 190236 * 2 ^ 59
def prefixEnd_190236 : Nat := 4983230072969 + 3 ^ 40 * 190236 * 2
def baseEnd_190236 : Nat := 65121670525881956316751

theorem tailTrace_190236 : CollatzResearch.WordTrace tailWord_190236 prefixEnd_190236 65121670525881956316751 := by
  unfold tailWord_190236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3469238469407468283635281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4625651292543291044847041 3469238469407468283635281)
  ·
    refine ⟨2601928852055601212726461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3469238469407468283635281 2601928852055601212726461)
    ·
      refine ⟨975723319520850454772423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2601928852055601212726461 975723319520850454772423)
      ·
        refine ⟨1463584979281275682158635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975723319520850454772423 1463584979281275682158635)
        ·
          refine ⟨2195377468921913523237953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463584979281275682158635 2195377468921913523237953)
          ·
            refine ⟨1646533101691435142428465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195377468921913523237953 1646533101691435142428465)
            ·
              refine ⟨1234899826268576356821349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646533101691435142428465 1234899826268576356821349)
              ·
                refine ⟨231543717425358066904003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1234899826268576356821349 231543717425358066904003)
                ·
                  refine ⟨347315576138037100356005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231543717425358066904003 347315576138037100356005)
                  ·
                    refine ⟨65121670525881956316751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347315576138037100356005 65121670525881956316751)
                    ·
                      rfl

theorem cell22_190236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_190236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190236 prefixEnd_190236 := by exact prefixLift 190236
  have htrace : WordTrace (prefixWord ++ tailWord_190236) baseStart_190236 baseEnd_190236 := by
    simpa [prefixWord, tailWord_190236, baseEnd_190236] using wordTrace_append hprefix tailTrace_190236
  have hstable : (prefixWord ++ tailWord_190236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190236).length < 2 ^ (prefixWord ++ tailWord_190236).sum := by decide
  have hdescent : baseEnd_190236 < baseStart_190236 := by decide
  rcases family_descends (prefixWord ++ tailWord_190236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190309 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_190309 : Nat := 118140960795 + 190309 * 2 ^ 59
def prefixEnd_190309 : Nat := 4983230072969 + 3 ^ 40 * 190309 * 2
def baseEnd_190309 : Nat := 65146659917734099241527

theorem tailTrace_190309 : CollatzResearch.WordTrace tailWord_190309 prefixEnd_190309 65146659917734099241527 := by
  unfold tailWord_190309
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941139467550470034677981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4627426311700313356451987 6941139467550470034677981)
  ·
    refine ⟨2602927300331426263004243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6941139467550470034677981 2602927300331426263004243)
    ·
      refine ⟨3904390950497139394506365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602927300331426263004243 3904390950497139394506365)
      ·
        refine ⟨1464146606436427272939887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3904390950497139394506365 1464146606436427272939887)
        ·
          refine ⟨2196219909654640909409831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464146606436427272939887 2196219909654640909409831)
          ·
            refine ⟨3294329864481961364114747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196219909654640909409831 3294329864481961364114747)
            ·
              refine ⟨4941494796722942046172121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294329864481961364114747 4941494796722942046172121)
              ·
                refine ⟨3706121097542206534629091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941494796722942046172121 3706121097542206534629091)
                ·
                  refine ⟨5559181646313309801943637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706121097542206534629091 5559181646313309801943637)
                  ·
                    refine ⟨65146659917734099241527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5559181646313309801943637 65146659917734099241527)
                    ·
                      rfl

theorem cell22_190309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_190309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190309 prefixEnd_190309 := by exact prefixLift 190309
  have htrace : WordTrace (prefixWord ++ tailWord_190309) baseStart_190309 baseEnd_190309 := by
    simpa [prefixWord, tailWord_190309, baseEnd_190309] using wordTrace_append hprefix tailTrace_190309
  have hstable : (prefixWord ++ tailWord_190309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190309).length < 2 ^ (prefixWord ++ tailWord_190309).sum := by decide
  have hdescent : baseEnd_190309 < baseStart_190309 := by decide
  rcases family_descends (prefixWord ++ tailWord_190309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190334 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_190334 : Nat := 118140960795 + 190334 * 2 ^ 59
def prefixEnd_190334 : Nat := 4983230072969 + 3 ^ 40 * 190334 * 2
def baseEnd_190334 : Nat := 65155217928642367366451

theorem tailTrace_190334 : CollatzResearch.WordTrace tailWord_190334 prefixEnd_190334 65155217928642367366451 := by
  unfold tailWord_190334
  simp only [CollatzResearch.WordTrace]
  refine ⟨867756411557487413042257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4628034194973266202892037 867756411557487413042257)
  ·
    refine ⟨650817308668115559781693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 867756411557487413042257 650817308668115559781693)
    ·
      refine ⟨244056490750543334918135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 650817308668115559781693 244056490750543334918135)
      ·
        refine ⟨366084736125815002377203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244056490750543334918135 366084736125815002377203)
        ·
          refine ⟨549127104188722503565805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366084736125815002377203 549127104188722503565805)
          ·
            refine ⟨205922664070770938837177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549127104188722503565805 205922664070770938837177)
            ·
              refine ⟨154441998053078204127883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205922664070770938837177 154441998053078204127883)
              ·
                refine ⟨231662997079617306191825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154441998053078204127883 231662997079617306191825)
                ·
                  refine ⟨173747247809712979643869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231662997079617306191825 173747247809712979643869)
                  ·
                    refine ⟨65155217928642367366451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173747247809712979643869 65155217928642367366451)
                    ·
                      rfl

theorem cell22_190334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_190334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190334 prefixEnd_190334 := by exact prefixLift 190334
  have htrace : WordTrace (prefixWord ++ tailWord_190334) baseStart_190334 baseEnd_190334 := by
    simpa [prefixWord, tailWord_190334, baseEnd_190334] using wordTrace_append hprefix tailTrace_190334
  have hstable : (prefixWord ++ tailWord_190334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190334).length < 2 ^ (prefixWord ++ tailWord_190334).sum := by decide
  have hdescent : baseEnd_190334 < baseStart_190334 := by decide
  rcases family_descends (prefixWord ++ tailWord_190334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190341 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 5]
def baseStart_190341 : Nat := 118140960795 + 190341 * 2 ^ 59
def prefixEnd_190341 : Nat := 4983230072969 + 3 ^ 40 * 190341 * 2
def baseEnd_190341 : Nat := 21719204723898894147143

theorem tailTrace_190341 : CollatzResearch.WordTrace tailWord_190341 prefixEnd_190341 21719204723898894147143 := by
  unfold tailWord_190341
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942306603434539499842877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4628204402289692999895251 6942306603434539499842877)
  ·
    refine ⟨2603364976287952312441079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6942306603434539499842877 2603364976287952312441079)
    ·
      refine ⟨3905047464431928468661619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603364976287952312441079 3905047464431928468661619)
      ·
        refine ⟨5857571196647892702992429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905047464431928468661619 5857571196647892702992429)
        ·
          refine ⟨2196589198742959763622161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5857571196647892702992429 2196589198742959763622161)
          ·
            refine ⟨1647441899057219822716621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196589198742959763622161 1647441899057219822716621)
            ·
              refine ⟨617790712146457433518733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1647441899057219822716621 617790712146457433518733)
              ·
                refine ⟨231671517054921537569525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617790712146457433518733 231671517054921537569525)
                ·
                  refine ⟨21719204723898894147143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231671517054921537569525 21719204723898894147143)
                  ·
                    rfl

theorem cell22_190341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_190341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190341 prefixEnd_190341 := by exact prefixLift 190341
  have htrace : WordTrace (prefixWord ++ tailWord_190341) baseStart_190341 baseEnd_190341 := by
    simpa [prefixWord, tailWord_190341, baseEnd_190341] using wordTrace_append hprefix tailTrace_190341
  have hstable : (prefixWord ++ tailWord_190341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190341).length < 2 ^ (prefixWord ++ tailWord_190341).sum := by decide
  have hdescent : baseEnd_190341 < baseStart_190341 := by decide
  rcases family_descends (prefixWord ++ tailWord_190341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190420 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_190420 : Nat := 118140960795 + 190420 * 2 ^ 59
def prefixEnd_190420 : Nat := 4983230072969 + 3 ^ 40 * 190420 * 2
def baseEnd_190420 : Nat := 21728219162055603238729

theorem tailTrace_190420 : CollatzResearch.WordTrace tailWord_190420 prefixEnd_190420 21728219162055603238729 := by
  unfold tailWord_190420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472593985074167995984357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4630125313432223994645809 3472593985074167995984357)
  ·
    refine ⟨651111372201406499247067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3472593985074167995984357 651111372201406499247067)
    ·
      refine ⟨976667058302109748870601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 651111372201406499247067 976667058302109748870601)
      ·
        refine ⟨732500293726582311652951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 976667058302109748870601 732500293726582311652951)
        ·
          refine ⟨1098750440589873467479427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732500293726582311652951 1098750440589873467479427)
          ·
            refine ⟨1648125660884810201219141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098750440589873467479427 1648125660884810201219141)
            ·
              refine ⟨309023561415901912728589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1648125660884810201219141 309023561415901912728589)
              ·
                refine ⟨115883835530963217273221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309023561415901912728589 115883835530963217273221)
                ·
                  refine ⟨21728219162055603238729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115883835530963217273221 21728219162055603238729)
                  ·
                    rfl

theorem cell22_190420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_190420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190420 prefixEnd_190420 := by exact prefixLift 190420
  have htrace : WordTrace (prefixWord ++ tailWord_190420) baseStart_190420 baseEnd_190420 := by
    simpa [prefixWord, tailWord_190420, baseEnd_190420] using wordTrace_append hprefix tailTrace_190420
  have hstable : (prefixWord ++ tailWord_190420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190420).length < 2 ^ (prefixWord ++ tailWord_190420).sum := by decide
  have hdescent : baseEnd_190420 < baseStart_190420 := by decide
  rcases family_descends (prefixWord ++ tailWord_190420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190422 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_190422 : Nat := 118140960795 + 190422 * 2 ^ 59
def prefixEnd_190422 : Nat := 4983230072969 + 3 ^ 40 * 190422 * 2
def baseEnd_190422 : Nat := 65185342127039471166181

theorem tailTrace_190422 : CollatzResearch.WordTrace tailWord_190422 prefixEnd_190422 65185342127039471166181 := by
  unfold tailWord_190422
  simp only [CollatzResearch.WordTrace]
  refine ⟨434078807258818145846345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4630173944094060222361013 434078807258818145846345)
  ·
    refine ⟨325559105444113609384759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 434078807258818145846345 325559105444113609384759)
    ·
      refine ⟨488338658166170414077139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325559105444113609384759 488338658166170414077139)
      ·
        refine ⟨732507987249255621115709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488338658166170414077139 732507987249255621115709)
        ·
          refine ⟨274690495218470857918391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732507987249255621115709 274690495218470857918391)
          ·
            refine ⟨412035742827706286877587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274690495218470857918391 412035742827706286877587)
            ·
              refine ⟨618053614241559430316381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412035742827706286877587 618053614241559430316381)
              ·
                refine ⟨231770105340584786368643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618053614241559430316381 231770105340584786368643)
                ·
                  refine ⟨347655158010877179552965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231770105340584786368643 347655158010877179552965)
                  ·
                    refine ⟨65185342127039471166181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347655158010877179552965 65185342127039471166181)
                    ·
                      rfl

theorem cell22_190422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_190422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190422 prefixEnd_190422 := by exact prefixLift 190422
  have htrace : WordTrace (prefixWord ++ tailWord_190422) baseStart_190422 baseEnd_190422 := by
    simpa [prefixWord, tailWord_190422, baseEnd_190422] using wordTrace_append hprefix tailTrace_190422
  have hstable : (prefixWord ++ tailWord_190422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190422).length < 2 ^ (prefixWord ++ tailWord_190422).sum := by decide
  have hdescent : baseEnd_190422 < baseStart_190422 := by decide
  rcases family_descends (prefixWord ++ tailWord_190422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190431 : List Nat := [1, 1, 2, 3, 4, 2, 9]
def baseStart_190431 : Nat := 118140960795 + 190431 * 2 ^ 59
def prefixEnd_190431 : Nat := 4983230072969 + 3 ^ 40 * 190431 * 2
def baseEnd_190431 : Nat := 2414386037443201766339

theorem tailTrace_190431 : CollatzResearch.WordTrace tailWord_190431 prefixEnd_190431 2414386037443201766339 := by
  unfold tailWord_190431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945589173108484870619147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4630392782072323247079431 6945589173108484870619147)
  ·
    refine ⟨10418383759662727305928721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945589173108484870619147 10418383759662727305928721)
    ·
      refine ⟨7813787819747045479446541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10418383759662727305928721 7813787819747045479446541)
      ·
        refine ⟨2930170432405142054792453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7813787819747045479446541 2930170432405142054792453)
        ·
          refine ⟨549406956075964135273585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2930170432405142054792453 549406956075964135273585)
          ·
            refine ⟨412055217056973101455189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549406956075964135273585 412055217056973101455189)
            ·
              refine ⟨2414386037443201766339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 412055217056973101455189 2414386037443201766339)
              ·
                rfl

theorem cell22_190431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 9].length) (baseStart_190431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190431 prefixEnd_190431 := by exact prefixLift 190431
  have htrace : WordTrace (prefixWord ++ tailWord_190431) baseStart_190431 baseEnd_190431 := by
    simpa [prefixWord, tailWord_190431, baseEnd_190431] using wordTrace_append hprefix tailTrace_190431
  have hstable : (prefixWord ++ tailWord_190431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190431).length < 2 ^ (prefixWord ++ tailWord_190431).sum := by decide
  have hdescent : baseEnd_190431 < baseStart_190431 := by decide
  rcases family_descends (prefixWord ++ tailWord_190431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190435 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 2, 3]
def baseStart_190435 : Nat := 118140960795 + 190435 * 2 ^ 59
def prefixEnd_190435 : Nat := 4983230072969 + 3 ^ 40 * 190435 * 2
def baseEnd_190435 : Nat := 65189792292711770591141

theorem tailTrace_190435 : CollatzResearch.WordTrace tailWord_190435 prefixEnd_190435 65189792292711770591141 := by
  unfold tailWord_190435
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945735065093993553764759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4630490043395995702509839 6945735065093993553764759)
  ·
    refine ⟨10418602597640990330647139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945735065093993553764759 10418602597640990330647139)
    ·
      refine ⟨15627903896461485495970709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10418602597640990330647139 15627903896461485495970709)
      ·
        refine ⟨732557995146632132623627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15627903896461485495970709 732557995146632132623627)
        ·
          refine ⟨1098836992719948198935441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732557995146632132623627 1098836992719948198935441)
          ·
            refine ⟨824127744539961149201581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098836992719948198935441 824127744539961149201581)
            ·
              refine ⟨309047904202485430950593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 824127744539961149201581 309047904202485430950593)
              ·
                refine ⟨231785928151864073212945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309047904202485430950593 231785928151864073212945)
                ·
                  refine ⟨173839446113898054909709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231785928151864073212945 173839446113898054909709)
                  ·
                    refine ⟨65189792292711770591141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173839446113898054909709 65189792292711770591141)
                    ·
                      rfl

theorem cell22_190435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3].length) (baseStart_190435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190435 prefixEnd_190435 := by exact prefixLift 190435
  have htrace : WordTrace (prefixWord ++ tailWord_190435) baseStart_190435 baseEnd_190435 := by
    simpa [prefixWord, tailWord_190435, baseEnd_190435] using wordTrace_append hprefix tailTrace_190435
  have hstable : (prefixWord ++ tailWord_190435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190435).length < 2 ^ (prefixWord ++ tailWord_190435).sum := by decide
  have hdescent : baseEnd_190435 < baseStart_190435 := by decide
  rcases family_descends (prefixWord ++ tailWord_190435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190461 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_190461 : Nat := 118140960795 + 190461 * 2 ^ 59
def prefixEnd_190461 : Nat := 4983230072969 + 3 ^ 40 * 190461 * 2
def baseEnd_190461 : Nat := 65198692624056369441061

theorem tailTrace_190461 : CollatzResearch.WordTrace tailWord_190461 prefixEnd_190461 65198692624056369441061 := by
  unfold tailWord_190461
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946683362999799994211237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631122241999866662807491 6946683362999799994211237)
  ·
    refine ⟨1302503130562462498914607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6946683362999799994211237 1302503130562462498914607)
    ·
      refine ⟨1953754695843693748371911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302503130562462498914607 1953754695843693748371911)
      ·
        refine ⟨2930632043765540622557867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953754695843693748371911 2930632043765540622557867)
        ·
          refine ⟨4395948065648310933836801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930632043765540622557867 4395948065648310933836801)
          ·
            refine ⟨3296961049236233200377601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4395948065648310933836801 3296961049236233200377601)
            ·
              refine ⟨2472720786927174900283201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296961049236233200377601 2472720786927174900283201)
              ·
                refine ⟨1854540590195381175212401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472720786927174900283201 1854540590195381175212401)
                ·
                  refine ⟨1390905442646535881409301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854540590195381175212401 1390905442646535881409301)
                  ·
                    refine ⟨65198692624056369441061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1390905442646535881409301 65198692624056369441061)
                    ·
                      rfl

theorem cell22_190461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_190461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190461 prefixEnd_190461 := by exact prefixLift 190461
  have htrace : WordTrace (prefixWord ++ tailWord_190461) baseStart_190461 baseEnd_190461 := by
    simpa [prefixWord, tailWord_190461, baseEnd_190461] using wordTrace_append hprefix tailTrace_190461
  have hstable : (prefixWord ++ tailWord_190461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190461).length < 2 ^ (prefixWord ++ tailWord_190461).sum := by decide
  have hdescent : baseEnd_190461 < baseStart_190461 := by decide
  rcases family_descends (prefixWord ++ tailWord_190461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190476 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_190476 : Nat := 118140960795 + 190476 * 2 ^ 59
def prefixEnd_190476 : Nat := 4983230072969 + 3 ^ 40 * 190476 * 2
def baseEnd_190476 : Nat := 21734609143533776772005

theorem tailTrace_190476 : CollatzResearch.WordTrace tailWord_190476 prefixEnd_190476 21734609143533776772005 := by
  unfold tailWord_190476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473615228972728778003641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4631486971963638370671521 3473615228972728778003641)
  ·
    refine ⟨2605211421729546583502731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3473615228972728778003641 2605211421729546583502731)
    ·
      refine ⟨3907817132594319875254097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2605211421729546583502731 3907817132594319875254097)
      ·
        refine ⟨2930862849445739906440573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3907817132594319875254097 2930862849445739906440573)
        ·
          refine ⟨1099073568542152464915215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2930862849445739906440573 1099073568542152464915215)
          ·
            refine ⟨1648610352813228697372823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099073568542152464915215 1648610352813228697372823)
            ·
              refine ⟨2472915529219843046059235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648610352813228697372823 2472915529219843046059235)
              ·
                refine ⟨3709373293829764569088853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472915529219843046059235 3709373293829764569088853)
                ·
                  refine ⟨21734609143533776772005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3709373293829764569088853 21734609143533776772005)
                  ·
                    rfl

theorem cell22_190476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_190476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190476 prefixEnd_190476 := by exact prefixLift 190476
  have htrace : WordTrace (prefixWord ++ tailWord_190476) baseStart_190476 baseEnd_190476 := by
    simpa [prefixWord, tailWord_190476, baseEnd_190476] using wordTrace_append hprefix tailTrace_190476
  have hstable : (prefixWord ++ tailWord_190476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190476).length < 2 ^ (prefixWord ++ tailWord_190476).sum := by decide
  have hdescent : baseEnd_190476 < baseStart_190476 := by decide
  rcases family_descends (prefixWord ++ tailWord_190476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_190491 : Nat := 118140960795 + 190491 * 2 ^ 59
def prefixEnd_190491 : Nat := 4983230072969 + 3 ^ 40 * 190491 * 2
def baseEnd_190491 : Nat := 65208962237146291190969

theorem tailTrace_190491 : CollatzResearch.WordTrace tailWord_190491 prefixEnd_190491 65208962237146291190969 := by
  unfold tailWord_190491
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947777552891115117803327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631851701927410078535551 6947777552891115117803327)
  ·
    refine ⟨10421666329336672676704991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947777552891115117803327 10421666329336672676704991)
    ·
      refine ⟨15632499494005009015057487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421666329336672676704991 15632499494005009015057487)
      ·
        refine ⟨23448749241007513522586231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15632499494005009015057487 23448749241007513522586231)
        ·
          refine ⟨35173123861511270283879347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23448749241007513522586231 35173123861511270283879347)
          ·
            refine ⟨52759685792266905425819021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35173123861511270283879347 52759685792266905425819021)
            ·
              refine ⟨19784882172100089534682133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52759685792266905425819021 19784882172100089534682133)
              ·
                refine ⟨927416351817191696938225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19784882172100089534682133 927416351817191696938225)
                ·
                  refine ⟨695562263862893772703669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927416351817191696938225 695562263862893772703669)
                  ·
                    refine ⟨65208962237146291190969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 695562263862893772703669 65208962237146291190969)
                    ·
                      rfl

theorem cell22_190491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_190491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190491 prefixEnd_190491 := by exact prefixLift 190491
  have htrace : WordTrace (prefixWord ++ tailWord_190491) baseStart_190491 baseEnd_190491 := by
    simpa [prefixWord, tailWord_190491, baseEnd_190491] using wordTrace_append hprefix tailTrace_190491
  have hstable : (prefixWord ++ tailWord_190491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190491).length < 2 ^ (prefixWord ++ tailWord_190491).sum := by decide
  have hdescent : baseEnd_190491 < baseStart_190491 := by decide
  rcases family_descends (prefixWord ++ tailWord_190491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190493 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 7]
def baseStart_190493 : Nat := 118140960795 + 190493 * 2 ^ 59
def prefixEnd_190493 : Nat := 4983230072969 + 3 ^ 40 * 190493 * 2
def baseEnd_190493 : Nat := 21736548959339650880321

theorem tailTrace_190493 : CollatzResearch.WordTrace tailWord_190493 prefixEnd_190493 21736548959339650880321 := by
  unfold tailWord_190493
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947850498883869459376133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631900332589246306250755 6947850498883869459376133)
  ·
    refine ⟨1302721968540725523633025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6947850498883869459376133 1302721968540725523633025)
    ·
      refine ⟨977041476405544142724769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1302721968540725523633025 977041476405544142724769)
      ·
        refine ⟨732781107304158107043577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 977041476405544142724769 732781107304158107043577)
        ·
          refine ⟨549585830478118580282683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732781107304158107043577 549585830478118580282683)
          ·
            refine ⟨824378745717177870424025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549585830478118580282683 824378745717177870424025)
            ·
              refine ⟨618284059287883402818019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824378745717177870424025 618284059287883402818019)
              ·
                refine ⟨927426088931825104227029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618284059287883402818019 927426088931825104227029)
                ·
                  refine ⟨21736548959339650880321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 927426088931825104227029 21736548959339650880321)
                  ·
                    rfl

theorem cell22_190493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_190493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190493 prefixEnd_190493 := by exact prefixLift 190493
  have htrace : WordTrace (prefixWord ++ tailWord_190493) baseStart_190493 baseEnd_190493 := by
    simpa [prefixWord, tailWord_190493, baseEnd_190493] using wordTrace_append hprefix tailTrace_190493
  have hstable : (prefixWord ++ tailWord_190493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190493).length < 2 ^ (prefixWord ++ tailWord_190493).sum := by decide
  have hdescent : baseEnd_190493 < baseStart_190493 := by decide
  rcases family_descends (prefixWord ++ tailWord_190493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190497 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_190497 : Nat := 118140960795 + 190497 * 2 ^ 59
def prefixEnd_190497 : Nat := 4983230072969 + 3 ^ 40 * 190497 * 2
def baseEnd_190497 : Nat := 65211016159764275540951

theorem tailTrace_190497 : CollatzResearch.WordTrace tailWord_190497 prefixEnd_190497 65211016159764275540951 := by
  unfold tailWord_190497
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947996390869378142521745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631997593912918761681163 6947996390869378142521745)
  ·
    refine ⟨5210997293152033606891309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6947996390869378142521745 5210997293152033606891309)
    ·
      refine ⟨1954123984932012602584241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5210997293152033606891309 1954123984932012602584241)
      ·
        refine ⟨1465592988699009451938181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954123984932012602584241 1465592988699009451938181)
        ·
          refine ⟨274798685381064272238409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1465592988699009451938181 274798685381064272238409)
          ·
            refine ⟨206099014035798204178807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274798685381064272238409 206099014035798204178807)
            ·
              refine ⟨309148521053697306268211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206099014035798204178807 309148521053697306268211)
              ·
                refine ⟨463722781580545959402317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309148521053697306268211 463722781580545959402317)
                ·
                  refine ⟨173896043092704734775869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463722781580545959402317 173896043092704734775869)
                  ·
                    refine ⟨65211016159764275540951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173896043092704734775869 65211016159764275540951)
                    ·
                      rfl

theorem cell22_190497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_190497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190497 prefixEnd_190497 := by exact prefixLift 190497
  have htrace : WordTrace (prefixWord ++ tailWord_190497) baseStart_190497 baseEnd_190497 := by
    simpa [prefixWord, tailWord_190497, baseEnd_190497] using wordTrace_append hprefix tailTrace_190497
  have hstable : (prefixWord ++ tailWord_190497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190497).length < 2 ^ (prefixWord ++ tailWord_190497).sum := by decide
  have hdescent : baseEnd_190497 < baseStart_190497 := by decide
  rcases family_descends (prefixWord ++ tailWord_190497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190510 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_190510 : Nat := 118140960795 + 190510 * 2 ^ 59
def prefixEnd_190510 : Nat := 4983230072969 + 3 ^ 40 * 190510 * 2
def baseEnd_190510 : Nat := 21738488775145524988637

theorem tailTrace_190510 : CollatzResearch.WordTrace tailWord_190510 prefixEnd_190510 21738488775145524988637 := by
  unfold tailWord_190510
  simp only [CollatzResearch.WordTrace]
  refine ⟨868558817477785170343123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4632313693214854241829989 868558817477785170343123)
  ·
    refine ⟨1302838226216677755514685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868558817477785170343123 1302838226216677755514685)
    ·
      refine ⟨488564334831254158318007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1302838226216677755514685 488564334831254158318007)
      ·
        refine ⟨732846502246881237477011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488564334831254158318007 732846502246881237477011)
        ·
          refine ⟨1099269753370321856215517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732846502246881237477011 1099269753370321856215517)
          ·
            refine ⟨412226157513870696080819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1099269753370321856215517 412226157513870696080819)
            ·
              refine ⟨618339236270806044121229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412226157513870696080819 618339236270806044121229)
              ·
                refine ⟨231877213601552266545461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618339236270806044121229 231877213601552266545461)
                ·
                  refine ⟨21738488775145524988637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231877213601552266545461 21738488775145524988637)
                  ·
                    rfl

theorem cell22_190510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_190510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190510 prefixEnd_190510 := by exact prefixLift 190510
  have htrace : WordTrace (prefixWord ++ tailWord_190510) baseStart_190510 baseEnd_190510 := by
    simpa [prefixWord, tailWord_190510, baseEnd_190510] using wordTrace_append hprefix tailTrace_190510
  have hstable : (prefixWord ++ tailWord_190510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190510).length < 2 ^ (prefixWord ++ tailWord_190510).sum := by decide
  have hdescent : baseEnd_190510 < baseStart_190510 := by decide
  rcases family_descends (prefixWord ++ tailWord_190510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190585 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_190585 : Nat := 118140960795 + 190585 * 2 ^ 59
def prefixEnd_190585 : Nat := 4983230072969 + 3 ^ 40 * 190585 * 2
def baseEnd_190585 : Nat := 65241140358161379340681

theorem tailTrace_190585 : CollatzResearch.WordTrace tailWord_190585 prefixEnd_190585 65241140358161379340681 := by
  unfold tailWord_190585
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951206014550569171725209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4634137343033712781150139 6951206014550569171725209)
  ·
    refine ⟨5213404510912926878793907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6951206014550569171725209 5213404510912926878793907)
    ·
      refine ⟨7820106766369390318190861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213404510912926878793907 7820106766369390318190861)
      ·
        refine ⟨2932540037388521369321573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7820106766369390318190861 2932540037388521369321573)
        ·
          refine ⟨549851257010347756747795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2932540037388521369321573 549851257010347756747795)
          ·
            refine ⟨824776885515521635121693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549851257010347756747795 824776885515521635121693)
            ·
              refine ⟨309291332068320613170635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 824776885515521635121693 309291332068320613170635)
              ·
                refine ⟨463936998102480919755953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309291332068320613170635 463936998102480919755953)
                ·
                  refine ⟨347952748576860689816965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463936998102480919755953 347952748576860689816965)
                  ·
                    refine ⟨65241140358161379340681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347952748576860689816965 65241140358161379340681)
                    ·
                      rfl

theorem cell22_190585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_190585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190585 prefixEnd_190585 := by exact prefixLift 190585
  have htrace : WordTrace (prefixWord ++ tailWord_190585) baseStart_190585 baseEnd_190585 := by
    simpa [prefixWord, tailWord_190585, baseEnd_190585] using wordTrace_append hprefix tailTrace_190585
  have hstable : (prefixWord ++ tailWord_190585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190585).length < 2 ^ (prefixWord ++ tailWord_190585).sum := by decide
  have hdescent : baseEnd_190585 < baseStart_190585 := by decide
  rcases family_descends (prefixWord ++ tailWord_190585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190634 : List Nat := [3, 1, 5, 1, 2, 2, 2, 6]
def baseStart_190634 : Nat := 118140960795 + 190634 * 2 ^ 59
def prefixEnd_190634 : Nat := 4983230072969 + 3 ^ 40 * 190634 * 2
def baseEnd_190634 : Nat := 7250879339949064985059

theorem tailTrace_190634 : CollatzResearch.WordTrace tailWord_190634 prefixEnd_190634 7250879339949064985059 := by
  unfold tailWord_190634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738248297843262635064739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4635328794248700360172637 1738248297843262635064739)
  ·
    refine ⟨2607372446764893952597109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738248297843262635064739 2607372446764893952597109)
    ·
      refine ⟨244441166884208808055979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2607372446764893952597109 244441166884208808055979)
      ·
        refine ⟨366661750326313212083969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244441166884208808055979 366661750326313212083969)
        ·
          refine ⟨274996312744734909062977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366661750326313212083969 274996312744734909062977)
          ·
            refine ⟨206247234558551181797233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274996312744734909062977 206247234558551181797233)
            ·
              refine ⟨154685425918913386347925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206247234558551181797233 154685425918913386347925)
              ·
                refine ⟨7250879339949064985059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154685425918913386347925 7250879339949064985059)
                ·
                  rfl

theorem cell22_190634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_190634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190634 prefixEnd_190634 := by exact prefixLift 190634
  have htrace : WordTrace (prefixWord ++ tailWord_190634) baseStart_190634 baseEnd_190634 := by
    simpa [prefixWord, tailWord_190634, baseEnd_190634] using wordTrace_append hprefix tailTrace_190634
  have hstable : (prefixWord ++ tailWord_190634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190634).length < 2 ^ (prefixWord ++ tailWord_190634).sum := by decide
  have hdescent : baseEnd_190634 < baseStart_190634 := by decide
  rcases family_descends (prefixWord ++ tailWord_190634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190705 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_190705 : Nat := 118140960795 + 190705 * 2 ^ 59
def prefixEnd_190705 : Nat := 4983230072969 + 3 ^ 40 * 190705 * 2
def baseEnd_190705 : Nat := 65282218810521066340313

theorem tailTrace_190705 : CollatzResearch.WordTrace tailWord_190705 prefixEnd_190705 65282218810521066340313 := by
  unfold tailWord_190705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955582774115829666093569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4637055182743886444062379 6955582774115829666093569)
  ·
    refine ⟨5216687080586872249570177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6955582774115829666093569 5216687080586872249570177)
    ·
      refine ⟨3912515310440154187177633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5216687080586872249570177 3912515310440154187177633)
      ·
        refine ⟨2934386482830115640383225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3912515310440154187177633 2934386482830115640383225)
        ·
          refine ⟨2200789862122586730287419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2934386482830115640383225 2200789862122586730287419)
          ·
            refine ⟨3301184793183880095431129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200789862122586730287419 3301184793183880095431129)
            ·
              refine ⟨2475888594887910071573347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3301184793183880095431129 2475888594887910071573347)
              ·
                refine ⟨3713832892331865107360021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475888594887910071573347 3713832892331865107360021)
                ·
                  refine ⟨174085916828056176907501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3713832892331865107360021 174085916828056176907501)
                  ·
                    refine ⟨65282218810521066340313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174085916828056176907501 65282218810521066340313)
                    ·
                      rfl

theorem cell22_190705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_190705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190705 prefixEnd_190705 := by exact prefixLift 190705
  have htrace : WordTrace (prefixWord ++ tailWord_190705) baseStart_190705 baseEnd_190705 := by
    simpa [prefixWord, tailWord_190705, baseEnd_190705] using wordTrace_append hprefix tailTrace_190705
  have hstable : (prefixWord ++ tailWord_190705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190705).length < 2 ^ (prefixWord ++ tailWord_190705).sum := by decide
  have hdescent : baseEnd_190705 < baseStart_190705 := by decide
  rcases family_descends (prefixWord ++ tailWord_190705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190720 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_190720 : Nat := 118140960795 + 190720 * 2 ^ 59
def prefixEnd_190720 : Nat := 4983230072969 + 3 ^ 40 * 190720 * 2
def baseEnd_190720 : Nat := 65287353617066027215267

theorem tailTrace_190720 : CollatzResearch.WordTrace tailWord_190720 prefixEnd_190720 65287353617066027215267 := by
  unfold tailWord_190720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478064934530743613944807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4637419912707658151926409 3478064934530743613944807)
  ·
    refine ⟨5217097401796115420917211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3478064934530743613944807 5217097401796115420917211)
    ·
      refine ⟨7825646102694173131375817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217097401796115420917211 7825646102694173131375817)
      ·
        refine ⟨5869234577020629848531863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7825646102694173131375817 5869234577020629848531863)
        ·
          refine ⟨8803851865530944772797795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869234577020629848531863 8803851865530944772797795)
          ·
            refine ⟨13205777798296417159196693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8803851865530944772797795 13205777798296417159196693)
            ·
              refine ⟨619020834295144554337345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13205777798296417159196693 619020834295144554337345)
              ·
                refine ⟨464265625721358415753009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619020834295144554337345 464265625721358415753009)
                ·
                  refine ⟨348199219291018811814757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464265625721358415753009 348199219291018811814757)
                  ·
                    refine ⟨65287353617066027215267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348199219291018811814757 65287353617066027215267)
                    ·
                      rfl

theorem cell22_190720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_190720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190720 prefixEnd_190720 := by exact prefixLift 190720
  have htrace : WordTrace (prefixWord ++ tailWord_190720) baseStart_190720 baseEnd_190720 := by
    simpa [prefixWord, tailWord_190720, baseEnd_190720] using wordTrace_append hprefix tailTrace_190720
  have hstable : (prefixWord ++ tailWord_190720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190720).length < 2 ^ (prefixWord ++ tailWord_190720).sum := by decide
  have hdescent : baseEnd_190720 < baseStart_190720 := by decide
  rcases family_descends (prefixWord ++ tailWord_190720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190724 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_190724 : Nat := 118140960795 + 190724 * 2 ^ 59
def prefixEnd_190724 : Nat := 4983230072969 + 3 ^ 40 * 190724 * 2
def baseEnd_190724 : Nat := 21762907632937116705085

theorem tailTrace_190724 : CollatzResearch.WordTrace tailWord_190724 prefixEnd_190724 21762907632937116705085 := by
  unfold tailWord_190724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478137880523497955517613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4637517174031330607356817 3478137880523497955517613)
  ·
    refine ⟨1304301705196311733319105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3478137880523497955517613 1304301705196311733319105)
    ·
      refine ⟨978226278897233799989329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304301705196311733319105 978226278897233799989329)
      ·
        refine ⟨733669709172925349991997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978226278897233799989329 733669709172925349991997)
        ·
          refine ⟨275126140939847006246999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 733669709172925349991997 275126140939847006246999)
          ·
            refine ⟨412689211409770509370499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275126140939847006246999 412689211409770509370499)
            ·
              refine ⟨619033817114655764055749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412689211409770509370499 619033817114655764055749)
              ·
                refine ⟨116068840708997955760453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619033817114655764055749 116068840708997955760453)
                ·
                  refine ⟨21762907632937116705085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116068840708997955760453 21762907632937116705085)
                  ·
                    rfl

theorem cell22_190724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_190724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190724 prefixEnd_190724 := by exact prefixLift 190724
  have htrace : WordTrace (prefixWord ++ tailWord_190724) baseStart_190724 baseEnd_190724 := by
    simpa [prefixWord, tailWord_190724, baseEnd_190724] using wordTrace_append hprefix tailTrace_190724
  have hstable : (prefixWord ++ tailWord_190724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190724).length < 2 ^ (prefixWord ++ tailWord_190724).sum := by decide
  have hdescent : baseEnd_190724 < baseStart_190724 := by decide
  rcases family_descends (prefixWord ++ tailWord_190724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190752 : List Nat := [2, 1, 1, 5, 2, 2, 3, 6]
def baseStart_190752 : Nat := 118140960795 + 190752 * 2 ^ 59
def prefixEnd_190752 : Nat := 4983230072969 + 3 ^ 40 * 190752 * 2
def baseEnd_190752 : Nat := 7255367541225401157241

theorem tailTrace_190752 : CollatzResearch.WordTrace tailWord_190752 prefixEnd_190752 7255367541225401157241 := by
  unfold tailWord_190752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478648502472778346527255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4638198003297037795369673 3478648502472778346527255)
  ·
    refine ⟨5217972753709167519790883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3478648502472778346527255 5217972753709167519790883)
    ·
      refine ⟨7826959130563751279686325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217972753709167519790883 7826959130563751279686325)
      ·
        refine ⟨733777418490351682470593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7826959130563751279686325 733777418490351682470593)
        ·
          refine ⟨550333063867763761852945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733777418490351682470593 550333063867763761852945)
          ·
            refine ⟨412749797900822821389709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550333063867763761852945 412749797900822821389709)
            ·
              refine ⟨154781174212808558021141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412749797900822821389709 154781174212808558021141)
              ·
                refine ⟨7255367541225401157241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154781174212808558021141 7255367541225401157241)
                ·
                  rfl

theorem cell22_190752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_190752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190752 prefixEnd_190752 := by exact prefixLift 190752
  have htrace : WordTrace (prefixWord ++ tailWord_190752) baseStart_190752 baseEnd_190752 := by
    simpa [prefixWord, tailWord_190752, baseEnd_190752] using wordTrace_append hprefix tailTrace_190752
  have hstable : (prefixWord ++ tailWord_190752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190752).length < 2 ^ (prefixWord ++ tailWord_190752).sum := by decide
  have hdescent : baseEnd_190752 < baseStart_190752 := by decide
  rcases family_descends (prefixWord ++ tailWord_190752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190754 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_190754 : Nat := 118140960795 + 190754 * 2 ^ 59
def prefixEnd_190754 : Nat := 4983230072969 + 3 ^ 40 * 190754 * 2
def baseEnd_190754 : Nat := 65298992511901271865163

theorem tailTrace_190754 : CollatzResearch.WordTrace tailWord_190754 prefixEnd_190754 65298992511901271865163 := by
  unfold tailWord_190754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739342487734577758656829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4638246633958874023084877 1739342487734577758656829)
  ·
    refine ⟨652253432900466659496311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1739342487734577758656829 652253432900466659496311)
    ·
      refine ⟨978380149350699989244467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652253432900466659496311 978380149350699989244467)
      ·
        refine ⟨1467570224026049983866701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978380149350699989244467 1467570224026049983866701)
        ·
          refine ⟨550338834009768743950013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1467570224026049983866701 550338834009768743950013)
          ·
            refine ⟨206377062753663278981255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 550338834009768743950013 206377062753663278981255)
            ·
              refine ⟨309565594130494918471883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206377062753663278981255 309565594130494918471883)
              ·
                refine ⟨464348391195742377707825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309565594130494918471883 464348391195742377707825)
                ·
                  refine ⟨348261293396806783280869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464348391195742377707825 348261293396806783280869)
                  ·
                    refine ⟨65298992511901271865163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348261293396806783280869 65298992511901271865163)
                    ·
                      rfl

theorem cell22_190754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_190754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190754 prefixEnd_190754 := by exact prefixLift 190754
  have htrace : WordTrace (prefixWord ++ tailWord_190754) baseStart_190754 baseEnd_190754 := by
    simpa [prefixWord, tailWord_190754, baseEnd_190754] using wordTrace_append hprefix tailTrace_190754
  have hstable : (prefixWord ++ tailWord_190754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190754).length < 2 ^ (prefixWord ++ tailWord_190754).sum := by decide
  have hdescent : baseEnd_190754 < baseStart_190754 := by decide
  rcases family_descends (prefixWord ++ tailWord_190754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190780 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_190780 : Nat := 118140960795 + 190780 * 2 ^ 59
def prefixEnd_190780 : Nat := 4983230072969 + 3 ^ 40 * 190780 * 2
def baseEnd_190780 : Nat := 21769297614415290238361

theorem tailTrace_190780 : CollatzResearch.WordTrace tailWord_190780 prefixEnd_190780 21769297614415290238361 := by
  unfold tailWord_190780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479159124422058737536897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4638878832562744983382529 3479159124422058737536897)
  ·
    refine ⟨2609369343316544053152673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3479159124422058737536897 2609369343316544053152673)
    ·
      refine ⟨1957027007487408039864505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2609369343316544053152673 1957027007487408039864505)
      ·
        refine ⟨1467770255615556029898379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957027007487408039864505 1467770255615556029898379)
        ·
          refine ⟨2201655383423334044847569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467770255615556029898379 2201655383423334044847569)
          ·
            refine ⟨1651241537567500533635677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201655383423334044847569 1651241537567500533635677)
            ·
              refine ⟨619215576587812700113379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1651241537567500533635677 619215576587812700113379)
              ·
                refine ⟨928823364881719050170069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619215576587812700113379 928823364881719050170069)
                ·
                  refine ⟨21769297614415290238361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 928823364881719050170069 21769297614415290238361)
                  ·
                    rfl

theorem cell22_190780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_190780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190780 prefixEnd_190780 := by exact prefixLift 190780
  have htrace : WordTrace (prefixWord ++ tailWord_190780) baseStart_190780 baseEnd_190780 := by
    simpa [prefixWord, tailWord_190780, baseEnd_190780] using wordTrace_append hprefix tailTrace_190780
  have hstable : (prefixWord ++ tailWord_190780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190780).length < 2 ^ (prefixWord ++ tailWord_190780).sum := by decide
  have hdescent : baseEnd_190780 < baseStart_190780 := by decide
  rcases family_descends (prefixWord ++ tailWord_190780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190818 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_190818 : Nat := 118140960795 + 190818 * 2 ^ 59
def prefixEnd_190818 : Nat := 4983230072969 + 3 ^ 40 * 190818 * 2
def baseEnd_190818 : Nat := 65320901019826438264967

theorem tailTrace_190818 : CollatzResearch.WordTrace tailWord_190818 prefixEnd_190818 65320901019826438264967 := by
  unfold tailWord_190818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739926055676612491239277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4639802815137633309971405 1739926055676612491239277)
  ·
    refine ⟨652472270878729684214729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1739926055676612491239277 652472270878729684214729)
    ·
      refine ⟨489354203159047263161047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 652472270878729684214729 489354203159047263161047)
      ·
        refine ⟨734031304738570894741571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489354203159047263161047 734031304738570894741571)
        ·
          refine ⟨1101046957107856342112357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734031304738570894741571 1101046957107856342112357)
          ·
            refine ⟨206446304457723064146067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1101046957107856342112357 206446304457723064146067)
            ·
              refine ⟨309669456686584596219101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206446304457723064146067 309669456686584596219101)
              ·
                refine ⟨116126046257469223582163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309669456686584596219101 116126046257469223582163)
                ·
                  refine ⟨174189069386203835373245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116126046257469223582163 174189069386203835373245)
                  ·
                    refine ⟨65320901019826438264967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174189069386203835373245 65320901019826438264967)
                    ·
                      rfl

theorem cell22_190818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_190818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190818 prefixEnd_190818 := by exact prefixLift 190818
  have htrace : WordTrace (prefixWord ++ tailWord_190818) baseStart_190818 baseEnd_190818 := by
    simpa [prefixWord, tailWord_190818, baseEnd_190818] using wordTrace_append hprefix tailTrace_190818
  have hstable : (prefixWord ++ tailWord_190818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190818).length < 2 ^ (prefixWord ++ tailWord_190818).sum := by decide
  have hdescent : baseEnd_190818 < baseStart_190818 := by decide
  rcases family_descends (prefixWord ++ tailWord_190818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190878 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_190878 : Nat := 118140960795 + 190878 * 2 ^ 59
def prefixEnd_190878 : Nat := 4983230072969 + 3 ^ 40 * 190878 * 2
def baseEnd_190878 : Nat := 65341440246006281764783

theorem tailTrace_190878 : CollatzResearch.WordTrace tailWord_190878 prefixEnd_190878 65341440246006281764783 := by
  unfold tailWord_190878
  simp only [CollatzResearch.WordTrace]
  refine ⟨870236575311135026517661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4641261734992720141427525 870236575311135026517661)
  ·
    refine ⟨326338715741675634944123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 870236575311135026517661 326338715741675634944123)
    ·
      refine ⟨489508073612513452416185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326338715741675634944123 489508073612513452416185)
      ·
        refine ⟨367131055209385089312139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489508073612513452416185 367131055209385089312139)
        ·
          refine ⟨550696582814077633968209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367131055209385089312139 550696582814077633968209)
          ·
            refine ⟨413022437110558225476157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550696582814077633968209 413022437110558225476157)
            ·
              refine ⟨154883413916459334553559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413022437110558225476157 154883413916459334553559)
              ·
                refine ⟨232325120874689001830339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154883413916459334553559 232325120874689001830339)
                ·
                  refine ⟨348487681312033502745509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232325120874689001830339 348487681312033502745509)
                  ·
                    refine ⟨65341440246006281764783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348487681312033502745509 65341440246006281764783)
                    ·
                      rfl

theorem cell22_190878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_190878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190878 prefixEnd_190878 := by exact prefixLift 190878
  have htrace : WordTrace (prefixWord ++ tailWord_190878) baseStart_190878 baseEnd_190878 := by
    simpa [prefixWord, tailWord_190878, baseEnd_190878] using wordTrace_append hprefix tailTrace_190878
  have hstable : (prefixWord ++ tailWord_190878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190878).length < 2 ^ (prefixWord ++ tailWord_190878).sum := by decide
  have hdescent : baseEnd_190878 < baseStart_190878 := by decide
  rcases family_descends (prefixWord ++ tailWord_190878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190915 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 9]
def baseStart_190915 : Nat := 118140960795 + 190915 * 2 ^ 59
def prefixEnd_190915 : Nat := 4983230072969 + 3 ^ 40 * 190915 * 2
def baseEnd_190915 : Nat := 21784702034050172863223

theorem tailTrace_190915 : CollatzResearch.WordTrace tailWord_190915 prefixEnd_190915 21784702034050172863223 := by
  unfold tailWord_190915
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963242103355035531238199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4642161402236690354158799 6963242103355035531238199)
  ·
    refine ⟨10444863155032553296857299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6963242103355035531238199 10444863155032553296857299)
    ·
      refine ⟨15667294732548829945285949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10444863155032553296857299 15667294732548829945285949)
      ·
        refine ⟨5875235524705811229482231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15667294732548829945285949 5875235524705811229482231)
        ·
          refine ⟨8812853287058716844223347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875235524705811229482231 8812853287058716844223347)
          ·
            refine ⟨13219279930588075266335021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8812853287058716844223347 13219279930588075266335021)
            ·
              refine ⟨4957229973970528224875633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13219279930588075266335021 4957229973970528224875633)
              ·
                refine ⟨3717922480477896168656725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957229973970528224875633 3717922480477896168656725)
                ·
                  refine ⟨21784702034050172863223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3717922480477896168656725 21784702034050172863223)
                  ·
                    rfl

theorem cell22_190915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_190915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190915 prefixEnd_190915 := by exact prefixLift 190915
  have htrace : WordTrace (prefixWord ++ tailWord_190915) baseStart_190915 baseEnd_190915 := by
    simpa [prefixWord, tailWord_190915, baseEnd_190915] using wordTrace_append hprefix tailTrace_190915
  have hstable : (prefixWord ++ tailWord_190915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190915).length < 2 ^ (prefixWord ++ tailWord_190915).sum := by decide
  have hdescent : baseEnd_190915 < baseStart_190915 := by decide
  rcases family_descends (prefixWord ++ tailWord_190915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190919 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 3, 3]
def baseStart_190919 : Nat := 118140960795 + 190919 * 2 ^ 59
def prefixEnd_190919 : Nat := 4983230072969 + 3 ^ 40 * 190919 * 2
def baseEnd_190919 : Nat := 65355475383895841489657

theorem tailTrace_190919 : CollatzResearch.WordTrace tailWord_190919 prefixEnd_190919 65355475383895841489657 := by
  unfold tailWord_190919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963387995340544214383811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4642258663560362809589207 6963387995340544214383811)
  ·
    refine ⟨10445081993010816321575717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6963387995340544214383811 10445081993010816321575717)
    ·
      refine ⟨1958452873689528060295447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10445081993010816321575717 1958452873689528060295447)
      ·
        refine ⟨2937679310534292090443171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958452873689528060295447 2937679310534292090443171)
        ·
          refine ⟨4406518965801438135664757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937679310534292090443171 4406518965801438135664757)
          ·
            refine ⟨413111153043884825218571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4406518965801438135664757 413111153043884825218571)
            ·
              refine ⟨619666729565827237827857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413111153043884825218571 619666729565827237827857)
              ·
                refine ⟨464750047174370428370893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619666729565827237827857 464750047174370428370893)
                ·
                  refine ⟨174281267690388910639085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464750047174370428370893 174281267690388910639085)
                  ·
                    refine ⟨65355475383895841489657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174281267690388910639085 65355475383895841489657)
                    ·
                      rfl

theorem cell22_190919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_190919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190919 prefixEnd_190919 := by exact prefixLift 190919
  have htrace : WordTrace (prefixWord ++ tailWord_190919) baseStart_190919 baseEnd_190919 := by
    simpa [prefixWord, tailWord_190919, baseEnd_190919] using wordTrace_append hprefix tailTrace_190919
  have hstable : (prefixWord ++ tailWord_190919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190919).length < 2 ^ (prefixWord ++ tailWord_190919).sum := by decide
  have hdescent : baseEnd_190919 < baseStart_190919 := by decide
  rcases family_descends (prefixWord ++ tailWord_190919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190949 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 7]
def baseStart_190949 : Nat := 118140960795 + 190949 * 2 ^ 59
def prefixEnd_190949 : Nat := 4983230072969 + 3 ^ 40 * 190949 * 2
def baseEnd_190949 : Nat := 21788581665661921079855

theorem tailTrace_190949 : CollatzResearch.WordTrace tailWord_190949 prefixEnd_190949 21788581665661921079855 := by
  unfold tailWord_190949
  simp only [CollatzResearch.WordTrace]
  refine ⟨6964482185231859337975901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4642988123487906225317267 6964482185231859337975901)
  ·
    refine ⟨2611680819461947251740963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6964482185231859337975901 2611680819461947251740963)
    ·
      refine ⟨3917521229192920877611445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611680819461947251740963 3917521229192920877611445)
      ·
        refine ⟨367267615236836332276073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3917521229192920877611445 367267615236836332276073)
        ·
          refine ⟨275450711427627249207055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367267615236836332276073 275450711427627249207055)
          ·
            refine ⟨413176067141440873810583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275450711427627249207055 413176067141440873810583)
            ·
              refine ⟨619764100712161310715875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413176067141440873810583 619764100712161310715875)
              ·
                refine ⟨929646151068241966073813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619764100712161310715875 929646151068241966073813)
                ·
                  refine ⟨21788581665661921079855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 929646151068241966073813 21788581665661921079855)
                  ·
                    rfl

theorem cell22_190949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_190949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190949 prefixEnd_190949 := by exact prefixLift 190949
  have htrace : WordTrace (prefixWord ++ tailWord_190949) baseStart_190949 baseEnd_190949 := by
    simpa [prefixWord, tailWord_190949, baseEnd_190949] using wordTrace_append hprefix tailTrace_190949
  have hstable : (prefixWord ++ tailWord_190949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190949).length < 2 ^ (prefixWord ++ tailWord_190949).sum := by decide
  have hdescent : baseEnd_190949 < baseStart_190949 := by decide
  rcases family_descends (prefixWord ++ tailWord_190949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190966 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_190966 : Nat := 118140960795 + 190966 * 2 ^ 59
def prefixEnd_190966 : Nat := 4983230072969 + 3 ^ 40 * 190966 * 2
def baseEnd_190966 : Nat := 21790521481467795188171

theorem tailTrace_190966 : CollatzResearch.WordTrace tailWord_190966 prefixEnd_190966 21790521481467795188171 := by
  unfold tailWord_190966
  simp only [CollatzResearch.WordTrace]
  refine ⟨435318889135641952584047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4643401484113514160896501 435318889135641952584047)
  ·
    refine ⟨652978333703462928876071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 435318889135641952584047 652978333703462928876071)
    ·
      refine ⟨979467500555194393314107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652978333703462928876071 979467500555194393314107)
      ·
        refine ⟨1469201250832791589971161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979467500555194393314107 1469201250832791589971161)
        ·
          refine ⟨1101900938124593692478371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469201250832791589971161 1101900938124593692478371)
          ·
            refine ⟨1652851407186890538717557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101900938124593692478371 1652851407186890538717557)
            ·
              refine ⟨154954819423770988004771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1652851407186890538717557 154954819423770988004771)
              ·
                refine ⟨232432229135656482007157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154954819423770988004771 232432229135656482007157)
                ·
                  refine ⟨21790521481467795188171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232432229135656482007157 21790521481467795188171)
                  ·
                    rfl

theorem cell22_190966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_190966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190966 prefixEnd_190966 := by exact prefixLift 190966
  have htrace : WordTrace (prefixWord ++ tailWord_190966) baseStart_190966 baseEnd_190966 := by
    simpa [prefixWord, tailWord_190966, baseEnd_190966] using wordTrace_append hprefix tailTrace_190966
  have hstable : (prefixWord ++ tailWord_190966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190966).length < 2 ^ (prefixWord ++ tailWord_190966).sum := by decide
  have hdescent : baseEnd_190966 < baseStart_190966 := by decide
  rcases family_descends (prefixWord ++ tailWord_190966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190979 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 1, 4]
def baseStart_190979 : Nat := 118140960795 + 190979 * 2 ^ 59
def prefixEnd_190979 : Nat := 4983230072969 + 3 ^ 40 * 190979 * 2
def baseEnd_190979 : Nat := 65376014610075684989473

theorem tailTrace_190979 : CollatzResearch.WordTrace tailWord_190979 prefixEnd_190979 65376014610075684989473 := by
  unfold tailWord_190979
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965576375123174461567991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4643717583415449641045327 6965576375123174461567991)
  ·
    refine ⟨10448364562684761692351987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6965576375123174461567991 10448364562684761692351987)
    ·
      refine ⟨15672546844027142538527981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448364562684761692351987 15672546844027142538527981)
      ·
        refine ⟨5877205066510178451947993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15672546844027142538527981 5877205066510178451947993)
        ·
          refine ⟨4407903799882633838960995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877205066510178451947993 4407903799882633838960995)
          ·
            refine ⟨6611855699823950758441493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407903799882633838960995 6611855699823950758441493)
            ·
              refine ⟨309930735929247691801945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6611855699823950758441493 309930735929247691801945)
              ·
                refine ⟨232448051946935768851459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309930735929247691801945 232448051946935768851459)
                ·
                  refine ⟨348672077920403653277189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232448051946935768851459 348672077920403653277189)
                  ·
                    refine ⟨65376014610075684989473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348672077920403653277189 65376014610075684989473)
                    ·
                      rfl

theorem cell22_190979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4].length) (baseStart_190979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_190979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_190979 prefixEnd_190979 := by exact prefixLift 190979
  have htrace : WordTrace (prefixWord ++ tailWord_190979) baseStart_190979 baseEnd_190979 := by
    simpa [prefixWord, tailWord_190979, baseEnd_190979] using wordTrace_append hprefix tailTrace_190979
  have hstable : (prefixWord ++ tailWord_190979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190979).length < 2 ^ (prefixWord ++ tailWord_190979).sum := by decide
  have hdescent : baseEnd_190979 < baseStart_190979 := by decide
  rcases family_descends (prefixWord ++ tailWord_190979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191009 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_191009 : Nat := 118140960795 + 191009 * 2 ^ 59
def prefixEnd_191009 : Nat := 4983230072969 + 3 ^ 40 * 191009 * 2
def baseEnd_191009 : Nat := 65386284223165606739381

theorem tailTrace_191009 : CollatzResearch.WordTrace tailWord_191009 prefixEnd_191009 65386284223165606739381 := by
  unfold tailWord_191009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966670565014489585160081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4644447043342993056773387 6966670565014489585160081)
  ·
    refine ⟨5225002923760867188870061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6966670565014489585160081 5225002923760867188870061)
    ·
      refine ⟨1959376096410325195826273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5225002923760867188870061 1959376096410325195826273)
      ·
        refine ⟨1469532072307743896869705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959376096410325195826273 1469532072307743896869705)
        ·
          refine ⟨1102149054230807922652279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469532072307743896869705 1102149054230807922652279)
          ·
            refine ⟨1653223581346211883978419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102149054230807922652279 1653223581346211883978419)
            ·
              refine ⟨2479835372019317825967629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653223581346211883978419 2479835372019317825967629)
              ·
                refine ⟨929938264507244184737861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479835372019317825967629 929938264507244184737861)
                ·
                  refine ⟨174363424595108284638349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929938264507244184737861 174363424595108284638349)
                  ·
                    refine ⟨65386284223165606739381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174363424595108284638349 65386284223165606739381)
                    ·
                      rfl

theorem cell22_191009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_191009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191009 prefixEnd_191009 := by exact prefixLift 191009
  have htrace : WordTrace (prefixWord ++ tailWord_191009) baseStart_191009 baseEnd_191009 := by
    simpa [prefixWord, tailWord_191009, baseEnd_191009] using wordTrace_append hprefix tailTrace_191009
  have hstable : (prefixWord ++ tailWord_191009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191009).length < 2 ^ (prefixWord ++ tailWord_191009).sum := by decide
  have hdescent : baseEnd_191009 < baseStart_191009 := by decide
  rcases family_descends (prefixWord ++ tailWord_191009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191041 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_191041 : Nat := 118140960795 + 191041 * 2 ^ 59
def prefixEnd_191041 : Nat := 4983230072969 + 3 ^ 40 * 191041 * 2
def baseEnd_191041 : Nat := 65397238477128189939283

theorem tailTrace_191041 : CollatzResearch.WordTrace tailWord_191041 prefixEnd_191041 65397238477128189939283 := by
  unfold tailWord_191041
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967837700898559050324977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4645225133932372700216651 6967837700898559050324977)
  ·
    refine ⟨5225878275673919287743733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6967837700898559050324977 5225878275673919287743733)
    ·
      refine ⟨489926088344429933225975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5225878275673919287743733 489926088344429933225975)
      ·
        refine ⟨734889132516644899838963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489926088344429933225975 734889132516644899838963)
        ·
          refine ⟨1102333698774967349758445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734889132516644899838963 1102333698774967349758445)
          ·
            refine ⟨413375137040612756159417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1102333698774967349758445 413375137040612756159417)
            ·
              refine ⟨310031352780459567119563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413375137040612756159417 310031352780459567119563)
              ·
                refine ⟨465047029170689350679345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310031352780459567119563 465047029170689350679345)
                ·
                  refine ⟨348785271878017013009509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465047029170689350679345 348785271878017013009509)
                  ·
                    refine ⟨65397238477128189939283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348785271878017013009509 65397238477128189939283)
                    ·
                      rfl

theorem cell22_191041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_191041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191041 prefixEnd_191041 := by exact prefixLift 191041
  have htrace : WordTrace (prefixWord ++ tailWord_191041) baseStart_191041 baseEnd_191041 := by
    simpa [prefixWord, tailWord_191041, baseEnd_191041] using wordTrace_append hprefix tailTrace_191041
  have hstable : (prefixWord ++ tailWord_191041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191041).length < 2 ^ (prefixWord ++ tailWord_191041).sum := by decide
  have hdescent : baseEnd_191041 < baseStart_191041 := by decide
  rcases family_descends (prefixWord ++ tailWord_191041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191084 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_191084 : Nat := 118140960795 + 191084 * 2 ^ 59
def prefixEnd_191084 : Nat := 4983230072969 + 3 ^ 40 * 191084 * 2
def baseEnd_191084 : Nat := 21803986085296803704717

theorem tailTrace_191084 : CollatzResearch.WordTrace tailWord_191084 prefixEnd_191084 21803986085296803704717 := by
  unfold tailWord_191084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484703019871388697070153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4646270693161851596093537 3484703019871388697070153)
  ·
    refine ⟨2613527264903541522802615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3484703019871388697070153 2613527264903541522802615)
    ·
      refine ⟨3920290897355312284203923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2613527264903541522802615 3920290897355312284203923)
      ·
        refine ⟨5880436346032968426305885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920290897355312284203923 5880436346032968426305885)
        ·
          refine ⟨2205163629762363159864707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5880436346032968426305885 2205163629762363159864707)
          ·
            refine ⟨3307745444643544739797061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205163629762363159864707 3307745444643544739797061)
            ·
              refine ⟨620202270870664638711949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3307745444643544739797061 620202270870664638711949)
              ·
                refine ⟨232575851576499239516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620202270870664638711949 232575851576499239516981)
                ·
                  refine ⟨21803986085296803704717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232575851576499239516981 21803986085296803704717)
                  ·
                    rfl

theorem cell22_191084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_191084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191084 prefixEnd_191084 := by exact prefixLift 191084
  have htrace : WordTrace (prefixWord ++ tailWord_191084) baseStart_191084 baseEnd_191084 := by
    simpa [prefixWord, tailWord_191084, baseEnd_191084] using wordTrace_append hprefix tailTrace_191084
  have hstable : (prefixWord ++ tailWord_191084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191084).length < 2 ^ (prefixWord ++ tailWord_191084).sum := by decide
  have hdescent : baseEnd_191084 < baseStart_191084 := by decide
  rcases family_descends (prefixWord ++ tailWord_191084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191129 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 6]
def baseStart_191129 : Nat := 118140960795 + 191129 * 2 ^ 59
def prefixEnd_191129 : Nat := 4983230072969 + 3 ^ 40 * 191129 * 2
def baseEnd_191129 : Nat := 21809120891841764579671

theorem tailTrace_191129 : CollatzResearch.WordTrace tailWord_191129 prefixEnd_191129 21809120891841764579671 := by
  unfold tailWord_191129
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971047324579750079528441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4647364883053166719685627 6971047324579750079528441)
  ·
    refine ⟨5228285493434812559646331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6971047324579750079528441 5228285493434812559646331)
    ·
      refine ⟨7842428240152218839469497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5228285493434812559646331 7842428240152218839469497)
      ·
        refine ⟨5881821180114164129602123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7842428240152218839469497 5881821180114164129602123)
        ·
          refine ⟨8822731770171246194403185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881821180114164129602123 8822731770171246194403185)
          ·
            refine ⟨6617048827628434645802389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8822731770171246194403185 6617048827628434645802389)
            ·
              refine ⟨310174163795082874021987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6617048827628434645802389 310174163795082874021987)
              ·
                refine ⟨465261245692624311032981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310174163795082874021987 465261245692624311032981)
                ·
                  refine ⟨21809120891841764579671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 465261245692624311032981 21809120891841764579671)
                  ·
                    rfl

theorem cell22_191129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_191129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191129 prefixEnd_191129 := by exact prefixLift 191129
  have htrace : WordTrace (prefixWord ++ tailWord_191129) baseStart_191129 baseEnd_191129 := by
    simpa [prefixWord, tailWord_191129, baseEnd_191129] using wordTrace_append hprefix tailTrace_191129
  have hstable : (prefixWord ++ tailWord_191129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191129).length < 2 ^ (prefixWord ++ tailWord_191129).sum := by decide
  have hdescent : baseEnd_191129 < baseStart_191129 := by decide
  rcases family_descends (prefixWord ++ tailWord_191129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191176 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_191176 : Nat := 118140960795 + 191176 * 2 ^ 59
def prefixEnd_191176 : Nat := 4983230072969 + 3 ^ 40 * 191176 * 2
def baseEnd_191176 : Nat := 65443451736032837813869

theorem tailTrace_191176 : CollatzResearch.WordTrace tailWord_191176 prefixEnd_191176 65443451736032837813869 := by
  unfold tailWord_191176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486380777704738553244691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4648507703606318070992921 3486380777704738553244691)
  ·
    refine ⟨5229571166557107829867037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486380777704738553244691 5229571166557107829867037)
    ·
      refine ⟨1961089187458915436200139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5229571166557107829867037 1961089187458915436200139)
      ·
        refine ⟨2941633781188373154300209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961089187458915436200139 2941633781188373154300209)
        ·
          refine ⟨2206225335891279865725157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2941633781188373154300209 2206225335891279865725157)
          ·
            refine ⟨413667250479614974823467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2206225335891279865725157 413667250479614974823467)
            ·
              refine ⟨620500875719422462235201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413667250479614974823467 620500875719422462235201)
              ·
                refine ⟨465375656789566846676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620500875719422462235201 465375656789566846676401)
                ·
                  refine ⟨349031742592175135007301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465375656789566846676401 349031742592175135007301)
                  ·
                    refine ⟨65443451736032837813869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349031742592175135007301 65443451736032837813869)
                    ·
                      rfl

theorem cell22_191176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_191176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191176 prefixEnd_191176 := by exact prefixLift 191176
  have htrace : WordTrace (prefixWord ++ tailWord_191176) baseStart_191176 baseEnd_191176 := by
    simpa [prefixWord, tailWord_191176, baseEnd_191176] using wordTrace_append hprefix tailTrace_191176
  have hstable : (prefixWord ++ tailWord_191176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191176).length < 2 ^ (prefixWord ++ tailWord_191176).sum := by decide
  have hdescent : baseEnd_191176 < baseStart_191176 := by decide
  rcases family_descends (prefixWord ++ tailWord_191176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191180 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_191180 : Nat := 118140960795 + 191180 * 2 ^ 59
def prefixEnd_191180 : Nat := 4983230072969 + 3 ^ 40 * 191180 * 2
def baseEnd_191180 : Nat := 21814940339259386904619

theorem tailTrace_191180 : CollatzResearch.WordTrace tailWord_191180 prefixEnd_191180 21814940339259386904619 := by
  unfold tailWord_191180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486453723697492894817497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4648604964929990526423329 3486453723697492894817497)
  ·
    refine ⟨2614840292773119671113123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3486453723697492894817497 2614840292773119671113123)
    ·
      refine ⟨3922260439159679506669685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614840292773119671113123 3922260439159679506669685)
      ·
        refine ⟨367711916171219953750283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3922260439159679506669685 367711916171219953750283)
        ·
          refine ⟨551567874256829930625425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367711916171219953750283 551567874256829930625425)
          ·
            refine ⟨413675905692622447969069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551567874256829930625425 413675905692622447969069)
            ·
              refine ⟨155128464634733417988401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413675905692622447969069 155128464634733417988401)
              ·
                refine ⟨116346348476050063491301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155128464634733417988401 116346348476050063491301)
                ·
                  refine ⟨21814940339259386904619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116346348476050063491301 21814940339259386904619)
                  ·
                    rfl

theorem cell22_191180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_191180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191180 prefixEnd_191180 := by exact prefixLift 191180
  have htrace : WordTrace (prefixWord ++ tailWord_191180) baseStart_191180 baseEnd_191180 := by
    simpa [prefixWord, tailWord_191180, baseEnd_191180] using wordTrace_append hprefix tailTrace_191180
  have hstable : (prefixWord ++ tailWord_191180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191180).length < 2 ^ (prefixWord ++ tailWord_191180).sum := by decide
  have hdescent : baseEnd_191180 < baseStart_191180 := by decide
  rcases family_descends (prefixWord ++ tailWord_191180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191223 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 1, 3]
def baseStart_191223 : Nat := 118140960795 + 191223 * 2 ^ 59
def prefixEnd_191223 : Nat := 4983230072969 + 3 ^ 40 * 191223 * 2
def baseEnd_191223 : Nat := 65459540796540381888725

theorem tailTrace_191223 : CollatzResearch.WordTrace tailWord_191223 prefixEnd_191223 65459540796540381888725 := by
  unfold tailWord_191223
  simp only [CollatzResearch.WordTrace]
  refine ⟨6974475786239204133450323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4649650524159469422300215 6974475786239204133450323)
  ·
    refine ⟨10461713679358806200175485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6974475786239204133450323 10461713679358806200175485)
    ·
      refine ⟨3923142629759552325065807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10461713679358806200175485 3923142629759552325065807)
      ·
        refine ⟨5884713944639328487598711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923142629759552325065807 5884713944639328487598711)
        ·
          refine ⟨8827070916958992731398067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884713944639328487598711 8827070916958992731398067)
          ·
            refine ⟨13240606375438489097097101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827070916958992731398067 13240606375438489097097101)
            ·
              refine ⟨4965227390789433411411413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13240606375438489097097101 4965227390789433411411413)
              ·
                refine ⟨116372516971627345579955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4965227390789433411411413 116372516971627345579955)
                ·
                  refine ⟨174558775457441018369933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116372516971627345579955 174558775457441018369933)
                  ·
                    refine ⟨65459540796540381888725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174558775457441018369933 65459540796540381888725)
                    ·
                      rfl

theorem cell22_191223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_191223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191223 prefixEnd_191223 := by exact prefixLift 191223
  have htrace : WordTrace (prefixWord ++ tailWord_191223) baseStart_191223 baseEnd_191223 := by
    simpa [prefixWord, tailWord_191223, baseEnd_191223] using wordTrace_append hprefix tailTrace_191223
  have hstable : (prefixWord ++ tailWord_191223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191223).length < 2 ^ (prefixWord ++ tailWord_191223).sum := by decide
  have hdescent : baseEnd_191223 < baseStart_191223 := by decide
  rcases family_descends (prefixWord ++ tailWord_191223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191240 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 1, 3]
def baseStart_191240 : Nat := 118140960795 + 191240 * 2 ^ 59
def prefixEnd_191240 : Nat := 4983230072969 + 3 ^ 40 * 191240 * 2
def baseEnd_191240 : Nat := 65465360243958004213673

theorem tailTrace_191240 : CollatzResearch.WordTrace tailWord_191240 prefixEnd_191240 65465360243958004213673 := by
  unfold tailWord_191240
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487547913588808018409587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4650063884785077357879449 3487547913588808018409587)
  ·
    refine ⟨5231321870383212027614381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487547913588808018409587 5231321870383212027614381)
    ·
      refine ⟨1961745701393704510355393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5231321870383212027614381 1961745701393704510355393)
      ·
        refine ⟨1471309276045278382766545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1961745701393704510355393 1471309276045278382766545)
        ·
          refine ⟨1103481957033958787074909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471309276045278382766545 1103481957033958787074909)
          ·
            refine ⟨413805733887734545153091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103481957033958787074909 413805733887734545153091)
            ·
              refine ⟨620708600831601817729637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413805733887734545153091 620708600831601817729637)
              ·
                refine ⟨116382862655925340824307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620708600831601817729637 116382862655925340824307)
                ·
                  refine ⟨174574293983888011236461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116382862655925340824307 174574293983888011236461)
                  ·
                    refine ⟨65465360243958004213673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174574293983888011236461 65465360243958004213673)
                    ·
                      rfl

theorem cell22_191240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_191240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191240 prefixEnd_191240 := by exact prefixLift 191240
  have htrace : WordTrace (prefixWord ++ tailWord_191240) baseStart_191240 baseEnd_191240 := by
    simpa [prefixWord, tailWord_191240, baseEnd_191240] using wordTrace_append hprefix tailTrace_191240
  have hstable : (prefixWord ++ tailWord_191240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191240).length < 2 ^ (prefixWord ++ tailWord_191240).sum := by decide
  have hdescent : baseEnd_191240 < baseStart_191240 := by decide
  rcases family_descends (prefixWord ++ tailWord_191240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191274 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_191274 : Nat := 118140960795 + 191274 * 2 ^ 59
def prefixEnd_191274 : Nat := 4983230072969 + 3 ^ 40 * 191274 * 2
def baseEnd_191274 : Nat := 65476999138793248863569

theorem tailTrace_191274 : CollatzResearch.WordTrace tailWord_191274 prefixEnd_191274 65476999138793248863569 := by
  unfold tailWord_191274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744083977263609960889219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4650890606036293229037917 1744083977263609960889219)
  ·
    refine ⟨2616125965895414941333829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1744083977263609960889219 2616125965895414941333829)
    ·
      refine ⟨490523618605390301500093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2616125965895414941333829 490523618605390301500093)
      ·
        refine ⟨183946356977021363062535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490523618605390301500093 183946356977021363062535)
        ·
          refine ⟨275919535465532044593803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183946356977021363062535 275919535465532044593803)
          ·
            refine ⟨413879303198298066890705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275919535465532044593803 413879303198298066890705)
            ·
              refine ⟨310409477398723550168029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413879303198298066890705 310409477398723550168029)
              ·
                refine ⟨116403554024521331313011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310409477398723550168029 116403554024521331313011)
                ·
                  refine ⟨174605331036781996969517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116403554024521331313011 174605331036781996969517)
                  ·
                    refine ⟨65476999138793248863569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174605331036781996969517 65476999138793248863569)
                    ·
                      rfl

theorem cell22_191274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_191274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191274 prefixEnd_191274 := by exact prefixLift 191274
  have htrace : WordTrace (prefixWord ++ tailWord_191274) baseStart_191274 baseEnd_191274 := by
    simpa [prefixWord, tailWord_191274, baseEnd_191274] using wordTrace_append hprefix tailTrace_191274
  have hstable : (prefixWord ++ tailWord_191274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191274).length < 2 ^ (prefixWord ++ tailWord_191274).sum := by decide
  have hdescent : baseEnd_191274 < baseStart_191274 := by decide
  rcases family_descends (prefixWord ++ tailWord_191274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191283 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 1, 4]
def baseStart_191283 : Nat := 118140960795 + 191283 * 2 ^ 59
def prefixEnd_191283 : Nat := 4983230072969 + 3 ^ 40 * 191283 * 2
def baseEnd_191283 : Nat := 65480080022720225388541

theorem tailTrace_191283 : CollatzResearch.WordTrace tailWord_191283 prefixEnd_191283 65480080022720225388541 := by
  unfold tailWord_191283
  simp only [CollatzResearch.WordTrace]
  refine ⟨6976664166021834380634503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4651109444014556253756335 6976664166021834380634503)
  ·
    refine ⟨10464996249032751570951755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6976664166021834380634503 10464996249032751570951755)
    ·
      refine ⟨15697494373549127356427633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10464996249032751570951755 15697494373549127356427633)
      ·
        refine ⟨11773120780161845517320725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15697494373549127356427633 11773120780161845517320725)
        ·
          refine ⟨551865036570086508624409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11773120780161845517320725 551865036570086508624409)
          ·
            refine ⟨413898777427564881468307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551865036570086508624409 413898777427564881468307)
            ·
              refine ⟨620848166141347322202461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413898777427564881468307 620848166141347322202461)
              ·
                refine ⟨232818062303005245825923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620848166141347322202461 232818062303005245825923)
                ·
                  refine ⟨349227093454507868738885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232818062303005245825923 349227093454507868738885)
                  ·
                    refine ⟨65480080022720225388541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349227093454507868738885 65480080022720225388541)
                    ·
                      rfl

theorem cell22_191283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4].length) (baseStart_191283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191283 prefixEnd_191283 := by exact prefixLift 191283
  have htrace : WordTrace (prefixWord ++ tailWord_191283) baseStart_191283 baseEnd_191283 := by
    simpa [prefixWord, tailWord_191283, baseEnd_191283] using wordTrace_append hprefix tailTrace_191283
  have hstable : (prefixWord ++ tailWord_191283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191283).length < 2 ^ (prefixWord ++ tailWord_191283).sum := by decide
  have hdescent : baseEnd_191283 < baseStart_191283 := by decide
  rcases family_descends (prefixWord ++ tailWord_191283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191448 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_191448 : Nat := 118140960795 + 191448 * 2 ^ 59
def prefixEnd_191448 : Nat := 4983230072969 + 3 ^ 40 * 191448 * 2
def baseEnd_191448 : Nat := 65536562894714795013035

theorem tailTrace_191448 : CollatzResearch.WordTrace tailWord_191448 prefixEnd_191448 65536562894714795013035 := by
  unfold tailWord_191448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491341105212033780195499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4655121473616045040260665 3491341105212033780195499)
  ·
    refine ⟨5237011657818050670293249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491341105212033780195499 5237011657818050670293249)
    ·
      refine ⟨3927758743363538002719937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237011657818050670293249 3927758743363538002719937)
      ·
        refine ⟨2945819057522653502039953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3927758743363538002719937 2945819057522653502039953)
        ·
          refine ⟨2209364293141990126529965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945819057522653502039953 2209364293141990126529965)
          ·
            refine ⟨828511609928246297448737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2209364293141990126529965 828511609928246297448737)
            ·
              refine ⟨621383707446184723086553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828511609928246297448737 621383707446184723086553)
              ·
                refine ⟨466037780584638542314915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621383707446184723086553 466037780584638542314915)
                ·
                  refine ⟨699056670876957813472373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466037780584638542314915 699056670876957813472373)
                  ·
                    refine ⟨65536562894714795013035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 699056670876957813472373 65536562894714795013035)
                    ·
                      rfl

theorem cell22_191448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_191448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191448 prefixEnd_191448 := by exact prefixLift 191448
  have htrace : WordTrace (prefixWord ++ tailWord_191448) baseStart_191448 baseEnd_191448 := by
    simpa [prefixWord, tailWord_191448, baseEnd_191448] using wordTrace_append hprefix tailTrace_191448
  have hstable : (prefixWord ++ tailWord_191448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191448).length < 2 ^ (prefixWord ++ tailWord_191448).sum := by decide
  have hdescent : baseEnd_191448 < baseStart_191448 := by decide
  rcases family_descends (prefixWord ++ tailWord_191448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191450 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_191450 : Nat := 118140960795 + 191450 * 2 ^ 59
def prefixEnd_191450 : Nat := 4983230072969 + 3 ^ 40 * 191450 * 2
def baseEnd_191450 : Nat := 21845749178529152154343

theorem tailTrace_191450 : CollatzResearch.WordTrace tailWord_191450 prefixEnd_191450 21845749178529152154343 := by
  unfold tailWord_191450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745688789104205475490951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4655170104277881267975869 1745688789104205475490951)
  ·
    refine ⟨2618533183656308213236427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745688789104205475490951 2618533183656308213236427)
    ·
      refine ⟨3927799775484462319854641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2618533183656308213236427 3927799775484462319854641)
      ·
        refine ⟨2945849831613346739890981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3927799775484462319854641 2945849831613346739890981)
        ·
          refine ⟨552346843427502513729559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2945849831613346739890981 552346843427502513729559)
          ·
            refine ⟨828520265141253770594339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552346843427502513729559 828520265141253770594339)
            ·
              refine ⟨1242780397711880655891509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828520265141253770594339 1242780397711880655891509)
              ·
                refine ⟨116510662285488811489829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1242780397711880655891509 116510662285488811489829)
                ·
                  refine ⟨21845749178529152154343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116510662285488811489829 21845749178529152154343)
                  ·
                    rfl

theorem cell22_191450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_191450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191450 prefixEnd_191450 := by exact prefixLift 191450
  have htrace : WordTrace (prefixWord ++ tailWord_191450) baseStart_191450 baseEnd_191450 := by
    simpa [prefixWord, tailWord_191450, baseEnd_191450] using wordTrace_append hprefix tailTrace_191450
  have hstable : (prefixWord ++ tailWord_191450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191450).length < 2 ^ (prefixWord ++ tailWord_191450).sum := by decide
  have hdescent : baseEnd_191450 < baseStart_191450 := by decide
  rcases family_descends (prefixWord ++ tailWord_191450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191523 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 7]
def baseStart_191523 : Nat := 118140960795 + 191523 * 2 ^ 59
def prefixEnd_191523 : Nat := 4983230072969 + 3 ^ 40 * 191523 * 2
def baseEnd_191523 : Nat := 21854078975813199795935

theorem tailTrace_191523 : CollatzResearch.WordTrace tailWord_191523 prefixEnd_191523 21854078975813199795935 := by
  unfold tailWord_191523
  simp only [CollatzResearch.WordTrace]
  refine ⟨6985417685152355369371223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4656945123434903579580815 6985417685152355369371223)
  ·
    refine ⟨10478126527728533054056835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6985417685152355369371223 10478126527728533054056835)
    ·
      refine ⟨15717189791592799581085253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10478126527728533054056835 15717189791592799581085253)
      ·
        refine ⟨2946973085923649921453485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15717189791592799581085253 2946973085923649921453485)
        ·
          refine ⟨1105114907221368720545057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946973085923649921453485 1105114907221368720545057)
          ·
            refine ⟨828836180416026540408793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105114907221368720545057 828836180416026540408793)
            ·
              refine ⟨621627135312019905306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828836180416026540408793 621627135312019905306595)
              ·
                refine ⟨932440702968029857959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621627135312019905306595 932440702968029857959893)
                ·
                  refine ⟨21854078975813199795935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 932440702968029857959893 21854078975813199795935)
                  ·
                    rfl

theorem cell22_191523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_191523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191523 prefixEnd_191523 := by exact prefixLift 191523
  have htrace : WordTrace (prefixWord ++ tailWord_191523) baseStart_191523 baseEnd_191523 := by
    simpa [prefixWord, tailWord_191523, baseEnd_191523] using wordTrace_append hprefix tailTrace_191523
  have hstable : (prefixWord ++ tailWord_191523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191523).length < 2 ^ (prefixWord ++ tailWord_191523).sum := by decide
  have hdescent : baseEnd_191523 < baseStart_191523 := by decide
  rcases family_descends (prefixWord ++ tailWord_191523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191538 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_191538 : Nat := 118140960795 + 191538 * 2 ^ 59
def prefixEnd_191538 : Nat := 4983230072969 + 3 ^ 40 * 191538 * 2
def baseEnd_191538 : Nat := 65567371733984560262759

theorem tailTrace_191538 : CollatzResearch.WordTrace tailWord_191538 prefixEnd_191538 65567371733984560262759 := by
  unfold tailWord_191538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746491195024503232791817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4657309853398675287444845 1746491195024503232791817)
  ·
    refine ⟨1309868396268377424593863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1746491195024503232791817 1309868396268377424593863)
    ·
      refine ⟨1964802594402566136890795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309868396268377424593863 1964802594402566136890795)
      ·
        refine ⟨2947203891603849205336193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964802594402566136890795 2947203891603849205336193)
        ·
          refine ⟨2210402918702886904002145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947203891603849205336193 2210402918702886904002145)
          ·
            refine ⟨1657802189027165178001609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210402918702886904002145 1657802189027165178001609)
            ·
              refine ⟨1243351641770373883501207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657802189027165178001609 1243351641770373883501207)
              ·
                refine ⟨1865027462655560825251811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243351641770373883501207 1865027462655560825251811)
                ·
                  refine ⟨2797541193983341237877717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865027462655560825251811 2797541193983341237877717)
                  ·
                    refine ⟨65567371733984560262759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2797541193983341237877717 65567371733984560262759)
                    ·
                      rfl

theorem cell22_191538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_191538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191538 prefixEnd_191538 := by exact prefixLift 191538
  have htrace : WordTrace (prefixWord ++ tailWord_191538) baseStart_191538 baseEnd_191538 := by
    simpa [prefixWord, tailWord_191538, baseEnd_191538] using wordTrace_append hprefix tailTrace_191538
  have hstable : (prefixWord ++ tailWord_191538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191538).length < 2 ^ (prefixWord ++ tailWord_191538).sum := by decide
  have hdescent : baseEnd_191538 < baseStart_191538 := by decide
  rcases family_descends (prefixWord ++ tailWord_191538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191583 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_191583 : Nat := 118140960795 + 191583 * 2 ^ 59
def prefixEnd_191583 : Nat := 4983230072969 + 3 ^ 40 * 191583 * 2
def baseEnd_191583 : Nat := 65582776153619442887621

theorem tailTrace_191583 : CollatzResearch.WordTrace tailWord_191583 prefixEnd_191583 65582776153619442887621 := by
  unfold tailWord_191583
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987606064934985616555403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4658404043289990411036935 6987606064934985616555403)
  ·
    refine ⟨10481409097402478424833105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987606064934985616555403 10481409097402478424833105)
    ·
      refine ⟨7861056823051858818624829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10481409097402478424833105 7861056823051858818624829)
      ·
        refine ⟨2947896308644447056984311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7861056823051858818624829 2947896308644447056984311)
        ·
          refine ⟨4421844462966670585476467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947896308644447056984311 4421844462966670585476467)
          ·
            refine ⟨6632766694450005878214701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421844462966670585476467 6632766694450005878214701)
            ·
              refine ⟨2487287510418752204330513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632766694450005878214701 2487287510418752204330513)
              ·
                refine ⟨1865465632814064153247885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487287510418752204330513 1865465632814064153247885)
                ·
                  refine ⟨699549612305274057467957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1865465632814064153247885 699549612305274057467957)
                  ·
                    refine ⟨65582776153619442887621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 699549612305274057467957 65582776153619442887621)
                    ·
                      rfl

theorem cell22_191583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_191583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191583 prefixEnd_191583 := by exact prefixLift 191583
  have htrace : WordTrace (prefixWord ++ tailWord_191583) baseStart_191583 baseEnd_191583 := by
    simpa [prefixWord, tailWord_191583, baseEnd_191583] using wordTrace_append hprefix tailTrace_191583
  have hstable : (prefixWord ++ tailWord_191583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191583).length < 2 ^ (prefixWord ++ tailWord_191583).sum := by decide
  have hdescent : baseEnd_191583 < baseStart_191583 := by decide
  rcases family_descends (prefixWord ++ tailWord_191583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191600 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_191600 : Nat := 118140960795 + 191600 * 2 ^ 59
def prefixEnd_191600 : Nat := 4983230072969 + 3 ^ 40 * 191600 * 2
def baseEnd_191600 : Nat := 65588595601037065212569

theorem tailTrace_191600 : CollatzResearch.WordTrace tailWord_191600 prefixEnd_191600 65588595601037065212569 := by
  unfold tailWord_191600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494113052936698759962127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4658817403915598346616169 3494113052936698759962127)
  ·
    refine ⟨5241169579405048139943191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494113052936698759962127 5241169579405048139943191)
    ·
      refine ⟨7861754369107572209914787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241169579405048139943191 7861754369107572209914787)
      ·
        refine ⟨11792631553661358314872181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861754369107572209914787 11792631553661358314872181)
        ·
          refine ⟨1105559208155752342019267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11792631553661358314872181 1105559208155752342019267)
          ·
            refine ⟨1658338812233628513028901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105559208155752342019267 1658338812233628513028901)
            ·
              refine ⟨310938527293805346192919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1658338812233628513028901 310938527293805346192919)
              ·
                refine ⟨466407790940708019289379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310938527293805346192919 466407790940708019289379)
                ·
                  refine ⟨699611686411062028934069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466407790940708019289379 699611686411062028934069)
                  ·
                    refine ⟨65588595601037065212569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 699611686411062028934069 65588595601037065212569)
                    ·
                      rfl

theorem cell22_191600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_191600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191600 prefixEnd_191600 := by exact prefixLift 191600
  have htrace : WordTrace (prefixWord ++ tailWord_191600) baseStart_191600 baseEnd_191600 := by
    simpa [prefixWord, tailWord_191600, baseEnd_191600] using wordTrace_append hprefix tailTrace_191600
  have hstable : (prefixWord ++ tailWord_191600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191600).length < 2 ^ (prefixWord ++ tailWord_191600).sum := by decide
  have hdescent : baseEnd_191600 < baseStart_191600 := by decide
  rcases family_descends (prefixWord ++ tailWord_191600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191621 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_191621 : Nat := 118140960795 + 191621 * 2 ^ 59
def prefixEnd_191621 : Nat := 4983230072969 + 3 ^ 40 * 191621 * 2
def baseEnd_191621 : Nat := 65595784330200010437505

theorem tailTrace_191621 : CollatzResearch.WordTrace tailWord_191621 prefixEnd_191621 65595784330200010437505 := by
  unfold tailWord_191621
  simp only [CollatzResearch.WordTrace]
  refine ⟨6988992038797318106438717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4659328025864878737625811 6988992038797318106438717)
  ·
    refine ⟨2620872014548994289914519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6988992038797318106438717 2620872014548994289914519)
    ·
      refine ⟨3931308021823491434871779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620872014548994289914519 3931308021823491434871779)
      ·
        refine ⟨5896962032735237152307669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931308021823491434871779 5896962032735237152307669)
        ·
          refine ⟨138210047642232120757211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5896962032735237152307669 138210047642232120757211)
          ·
            refine ⟨207315071463348181135817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138210047642232120757211 207315071463348181135817)
            ·
              refine ⟨155486303597511135851863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207315071463348181135817 155486303597511135851863)
              ·
                refine ⟨233229455396266703777795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155486303597511135851863 233229455396266703777795)
                ·
                  refine ⟨349844183094400055666693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233229455396266703777795 349844183094400055666693)
                  ·
                    refine ⟨65595784330200010437505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349844183094400055666693 65595784330200010437505)
                    ·
                      rfl

theorem cell22_191621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_191621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191621 prefixEnd_191621 := by exact prefixLift 191621
  have htrace : WordTrace (prefixWord ++ tailWord_191621) baseStart_191621 baseEnd_191621 := by
    simpa [prefixWord, tailWord_191621, baseEnd_191621] using wordTrace_append hprefix tailTrace_191621
  have hstable : (prefixWord ++ tailWord_191621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191621).length < 2 ^ (prefixWord ++ tailWord_191621).sum := by decide
  have hdescent : baseEnd_191621 < baseStart_191621 := by decide
  rcases family_descends (prefixWord ++ tailWord_191621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191628 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_191628 : Nat := 118140960795 + 191628 * 2 ^ 59
def prefixEnd_191628 : Nat := 4983230072969 + 3 ^ 40 * 191628 * 2
def baseEnd_191628 : Nat := 65598180573254325512483

theorem tailTrace_191628 : CollatzResearch.WordTrace tailWord_191628 prefixEnd_191628 65598180573254325512483 := by
  unfold tailWord_191628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494623674885979150971769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4659498233181305534629025 3494623674885979150971769)
  ·
    refine ⟨2620967756164484363228827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3494623674885979150971769 2620967756164484363228827)
    ·
      refine ⟨3931451634246726544843241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620967756164484363228827 3931451634246726544843241)
      ·
        refine ⟨2948588725685044908632431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3931451634246726544843241 2948588725685044908632431)
        ·
          refine ⟨4422883088527567362948647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948588725685044908632431 4422883088527567362948647)
          ·
            refine ⟨6634324632791351044422971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422883088527567362948647 6634324632791351044422971)
            ·
              refine ⟨9951486949187026566634457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634324632791351044422971 9951486949187026566634457)
              ·
                refine ⟨7463615211890269924975843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951486949187026566634457 7463615211890269924975843)
                ·
                  refine ⟨11195422817835404887463765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7463615211890269924975843 11195422817835404887463765)
                  ·
                    refine ⟨65598180573254325512483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 11195422817835404887463765 65598180573254325512483)
                    ·
                      rfl

theorem cell22_191628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_191628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191628 prefixEnd_191628 := by exact prefixLift 191628
  have htrace : WordTrace (prefixWord ++ tailWord_191628) baseStart_191628 baseEnd_191628 := by
    simpa [prefixWord, tailWord_191628, baseEnd_191628] using wordTrace_append hprefix tailTrace_191628
  have hstable : (prefixWord ++ tailWord_191628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191628).length < 2 ^ (prefixWord ++ tailWord_191628).sum := by decide
  have hdescent : baseEnd_191628 < baseStart_191628 := by decide
  rcases family_descends (prefixWord ++ tailWord_191628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191630 : List Nat := [4, 1, 1, 3, 2, 2, 9]
def baseStart_191630 : Nat := 118140960795 + 191630 * 2 ^ 59
def prefixEnd_191630 : Nat := 4983230072969 + 3 ^ 40 * 191630 * 2
def baseEnd_191630 : Nat := 2429587600523221739351

theorem tailTrace_191630 : CollatzResearch.WordTrace tailWord_191630 prefixEnd_191630 2429587600523221739351 := by
  unfold tailWord_191630
  simp only [CollatzResearch.WordTrace]
  refine ⟨873665036970589080439543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4659546863843141762344229 873665036970589080439543)
  ·
    refine ⟨1310497555455883620659315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873665036970589080439543 1310497555455883620659315)
    ·
      refine ⟨1965746333183825430988973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310497555455883620659315 1965746333183825430988973)
      ·
        refine ⟨737154874943934536620865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1965746333183825430988973 737154874943934536620865)
        ·
          refine ⟨552866156207950902465649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737154874943934536620865 552866156207950902465649)
          ·
            refine ⟨414649617155963176849237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552866156207950902465649 414649617155963176849237)
            ·
              refine ⟨2429587600523221739351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 414649617155963176849237 2429587600523221739351)
              ·
                rfl

theorem cell22_191630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 9].length) (baseStart_191630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191630 prefixEnd_191630 := by exact prefixLift 191630
  have htrace : WordTrace (prefixWord ++ tailWord_191630) baseStart_191630 baseEnd_191630 := by
    simpa [prefixWord, tailWord_191630, baseEnd_191630] using wordTrace_append hprefix tailTrace_191630
  have hstable : (prefixWord ++ tailWord_191630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191630).length < 2 ^ (prefixWord ++ tailWord_191630).sum := by decide
  have hdescent : baseEnd_191630 < baseStart_191630 := by decide
  rcases family_descends (prefixWord ++ tailWord_191630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191634 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_191634 : Nat := 118140960795 + 191634 * 2 ^ 59
def prefixEnd_191634 : Nat := 4983230072969 + 3 ^ 40 * 191634 * 2
def baseEnd_191634 : Nat := 65600234495872309862465

theorem tailTrace_191634 : CollatzResearch.WordTrace tailWord_191634 prefixEnd_191634 65600234495872309862465 := by
  unfold tailWord_191634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747366546937555331665489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4659644125166814217774637 1747366546937555331665489)
  ·
    refine ⟨1310524910203166498749117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1747366546937555331665489 1310524910203166498749117)
    ·
      refine ⟨491446841326187437030919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1310524910203166498749117 491446841326187437030919)
      ·
        refine ⟨737170261989281155546379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491446841326187437030919 737170261989281155546379)
        ·
          refine ⟨1105755392983921733319569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737170261989281155546379 1105755392983921733319569)
          ·
            refine ⟨829316544737941299989677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105755392983921733319569 829316544737941299989677)
            ·
              refine ⟨310993704276727987496129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829316544737941299989677 310993704276727987496129)
              ·
                refine ⟨233245278207545990622097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310993704276727987496129 233245278207545990622097)
                ·
                  refine ⟨174933958655659492966573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233245278207545990622097 174933958655659492966573)
                  ·
                    refine ⟨65600234495872309862465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174933958655659492966573 65600234495872309862465)
                    ·
                      rfl

theorem cell22_191634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_191634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191634 prefixEnd_191634 := by exact prefixLift 191634
  have htrace : WordTrace (prefixWord ++ tailWord_191634) baseStart_191634 baseEnd_191634 := by
    simpa [prefixWord, tailWord_191634, baseEnd_191634] using wordTrace_append hprefix tailTrace_191634
  have hstable : (prefixWord ++ tailWord_191634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191634).length < 2 ^ (prefixWord ++ tailWord_191634).sum := by decide
  have hdescent : baseEnd_191634 < baseStart_191634 := by decide
  rcases family_descends (prefixWord ++ tailWord_191634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191670 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_191670 : Nat := 118140960795 + 191670 * 2 ^ 59
def prefixEnd_191670 : Nat := 4983230072969 + 3 ^ 40 * 191670 * 2
def baseEnd_191670 : Nat := 21870852677193405320785

theorem tailTrace_191670 : CollatzResearch.WordTrace tailWord_191670 prefixEnd_191670 21870852677193405320785 := by
  unfold tailWord_191670
  simp only [CollatzResearch.WordTrace]
  refine ⟨436923700976237467185779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4660519477079866316648309 436923700976237467185779)
  ·
    refine ⟨655385551464356200778669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436923700976237467185779 655385551464356200778669)
    ·
      refine ⟨245769581799133575292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 655385551464356200778669 245769581799133575292001)
      ·
        refine ⟨184327186349350181469001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245769581799133575292001 184327186349350181469001)
        ·
          refine ⟨138245389762012636101751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184327186349350181469001 138245389762012636101751)
          ·
            refine ⟨207368084643018954152627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138245389762012636101751 207368084643018954152627)
            ·
              refine ⟨311052126964528431228941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207368084643018954152627 311052126964528431228941)
              ·
                refine ⟨116644547611698161710853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311052126964528431228941 116644547611698161710853)
                ·
                  refine ⟨21870852677193405320785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116644547611698161710853 21870852677193405320785)
                  ·
                    rfl

theorem cell22_191670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_191670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191670 prefixEnd_191670 := by exact prefixLift 191670
  have htrace : WordTrace (prefixWord ++ tailWord_191670) baseStart_191670 baseEnd_191670 := by
    simpa [prefixWord, tailWord_191670, baseEnd_191670] using wordTrace_append hprefix tailTrace_191670
  have hstable : (prefixWord ++ tailWord_191670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191670).length < 2 ^ (prefixWord ++ tailWord_191670).sum := by decide
  have hdescent : baseEnd_191670 < baseStart_191670 := by decide
  rcases family_descends (prefixWord ++ tailWord_191670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191679 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 1, 3]
def baseStart_191679 : Nat := 118140960795 + 191679 * 2 ^ 59
def prefixEnd_191679 : Nat := 4983230072969 + 3 ^ 40 * 191679 * 2
def baseEnd_191679 : Nat := 65615638915507192487327

theorem tailTrace_191679 : CollatzResearch.WordTrace tailWord_191679 prefixEnd_191679 65615638915507192487327 := by
  unfold tailWord_191679
  simp only [CollatzResearch.WordTrace]
  refine ⟨6991107472587194012050091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4660738315058129341366727 6991107472587194012050091)
  ·
    refine ⟨10486661208880791018075137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6991107472587194012050091 10486661208880791018075137)
    ·
      refine ⟨7864995906660593263556353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10486661208880791018075137 7864995906660593263556353)
      ·
        refine ⟨5898746929995444947667265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7864995906660593263556353 5898746929995444947667265)
        ·
          refine ⟨4424060197496583710750449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898746929995444947667265 4424060197496583710750449)
          ·
            refine ⟨3318045148122437783062837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4424060197496583710750449 3318045148122437783062837)
            ·
              refine ⟨311066732636478542162141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3318045148122437783062837 311066732636478542162141)
              ·
                refine ⟨116650024738679453310803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311066732636478542162141 116650024738679453310803)
                ·
                  refine ⟨174975037108019179966205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116650024738679453310803 174975037108019179966205)
                  ·
                    refine ⟨65615638915507192487327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174975037108019179966205 65615638915507192487327)
                    ·
                      rfl

theorem cell22_191679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_191679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191679 prefixEnd_191679 := by exact prefixLift 191679
  have htrace : WordTrace (prefixWord ++ tailWord_191679) baseStart_191679 baseEnd_191679 := by
    simpa [prefixWord, tailWord_191679, baseEnd_191679] using wordTrace_append hprefix tailTrace_191679
  have hstable : (prefixWord ++ tailWord_191679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191679).length < 2 ^ (prefixWord ++ tailWord_191679).sum := by decide
  have hdescent : baseEnd_191679 < baseStart_191679 := by decide
  rcases family_descends (prefixWord ++ tailWord_191679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191705 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_191705 : Nat := 118140960795 + 191705 * 2 ^ 59
def prefixEnd_191705 : Nat := 4983230072969 + 3 ^ 40 * 191705 * 2
def baseEnd_191705 : Nat := 65624539246851791337247

theorem tailTrace_191705 : CollatzResearch.WordTrace tailWord_191705 prefixEnd_191705 65624539246851791337247 := by
  unfold tailWord_191705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992055770493000452496569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4661370513662000301664379 6992055770493000452496569)
  ·
    refine ⟨5244041827869750339372427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6992055770493000452496569 5244041827869750339372427)
    ·
      refine ⟨7866062741804625509058641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244041827869750339372427 7866062741804625509058641)
      ·
        refine ⟨5899547056353469131793981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7866062741804625509058641 5899547056353469131793981)
        ·
          refine ⟨2212330146132550924422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5899547056353469131793981 2212330146132550924422743)
          ·
            refine ⟨3318495219198826386634115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212330146132550924422743 3318495219198826386634115)
            ·
              refine ⟨4977742828798239579951173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318495219198826386634115 4977742828798239579951173)
              ·
                refine ⟨933326780399669921240845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4977742828798239579951173 933326780399669921240845)
                ·
                  refine ⟨349997542649876220465317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933326780399669921240845 349997542649876220465317)
                  ·
                    refine ⟨65624539246851791337247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349997542649876220465317 65624539246851791337247)
                    ·
                      rfl

theorem cell22_191705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_191705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191705 prefixEnd_191705 := by exact prefixLift 191705
  have htrace : WordTrace (prefixWord ++ tailWord_191705) baseStart_191705 baseEnd_191705 := by
    simpa [prefixWord, tailWord_191705, baseEnd_191705] using wordTrace_append hprefix tailTrace_191705
  have hstable : (prefixWord ++ tailWord_191705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191705).length < 2 ^ (prefixWord ++ tailWord_191705).sum := by decide
  have hdescent : baseEnd_191705 < baseStart_191705 := by decide
  rcases family_descends (prefixWord ++ tailWord_191705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191709 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 5]
def baseStart_191709 : Nat := 118140960795 + 191709 * 2 ^ 59
def prefixEnd_191709 : Nat := 4983230072969 + 3 ^ 40 * 191709 * 2
def baseEnd_191709 : Nat := 21875302842865704745745

theorem tailTrace_191709 : CollatzResearch.WordTrace tailWord_191709 prefixEnd_191709 21875302842865704745745 := by
  unfold tailWord_191709
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992201662478509135642181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4661467774985672757094787 6992201662478509135642181)
  ·
    refine ⟨1311037811714720462932909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6992201662478509135642181 1311037811714720462932909)
    ·
      refine ⟨491639179393020173599841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1311037811714720462932909 491639179393020173599841)
      ·
        refine ⟨368729384544765130199881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491639179393020173599841 368729384544765130199881)
        ·
          refine ⟨276547038408573847649911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368729384544765130199881 276547038408573847649911)
          ·
            refine ⟨414820557612860771474867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276547038408573847649911 414820557612860771474867)
            ·
              refine ⟨622230836419291157212301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414820557612860771474867 622230836419291157212301)
              ·
                refine ⟨233336563657234183954613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622230836419291157212301 233336563657234183954613)
                ·
                  refine ⟨21875302842865704745745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233336563657234183954613 21875302842865704745745)
                  ·
                    rfl

theorem cell22_191709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_191709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191709 prefixEnd_191709 := by exact prefixLift 191709
  have htrace : WordTrace (prefixWord ++ tailWord_191709) baseStart_191709 baseEnd_191709 := by
    simpa [prefixWord, tailWord_191709, baseEnd_191709] using wordTrace_append hprefix tailTrace_191709
  have hstable : (prefixWord ++ tailWord_191709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191709).length < 2 ^ (prefixWord ++ tailWord_191709).sum := by decide
  have hdescent : baseEnd_191709 < baseStart_191709 := by decide
  rcases family_descends (prefixWord ++ tailWord_191709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191720 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_191720 : Nat := 118140960795 + 191720 * 2 ^ 59
def prefixEnd_191720 : Nat := 4983230072969 + 3 ^ 40 * 191720 * 2
def baseEnd_191720 : Nat := 21876558017798917404067

theorem tailTrace_191720 : CollatzResearch.WordTrace tailWord_191720 prefixEnd_191720 21876558017798917404067 := by
  unfold tailWord_191720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496301432719329007146307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4661735243625772009528409 3496301432719329007146307)
  ·
    refine ⟨5244452149078993510719461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3496301432719329007146307 5244452149078993510719461)
    ·
      refine ⟨983334777952311283259899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5244452149078993510719461 983334777952311283259899)
      ·
        refine ⟨1475002166928466924889849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983334777952311283259899 1475002166928466924889849)
        ·
          refine ⟨1106251625196350193667387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1475002166928466924889849 1106251625196350193667387)
          ·
            refine ⟨1659377437794525290501081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106251625196350193667387 1659377437794525290501081)
            ·
              refine ⟨1244533078345893967875811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659377437794525290501081 1244533078345893967875811)
              ·
                refine ⟨1866799617518840951813717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244533078345893967875811 1866799617518840951813717)
                ·
                  refine ⟨21876558017798917404067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1866799617518840951813717 21876558017798917404067)
                  ·
                    rfl

theorem cell22_191720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_191720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191720 prefixEnd_191720 := by exact prefixLift 191720
  have htrace : WordTrace (prefixWord ++ tailWord_191720) baseStart_191720 baseEnd_191720 := by
    simpa [prefixWord, tailWord_191720, baseEnd_191720] using wordTrace_append hprefix tailTrace_191720
  have hstable : (prefixWord ++ tailWord_191720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191720).length < 2 ^ (prefixWord ++ tailWord_191720).sum := by decide
  have hdescent : baseEnd_191720 < baseStart_191720 := by decide
  rcases family_descends (prefixWord ++ tailWord_191720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191722 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_191722 : Nat := 118140960795 + 191722 * 2 ^ 59
def prefixEnd_191722 : Nat := 4983230072969 + 3 ^ 40 * 191722 * 2
def baseEnd_191722 : Nat := 65630358694269413662195

theorem tailTrace_191722 : CollatzResearch.WordTrace tailWord_191722 prefixEnd_191722 65630358694269413662195 := by
  unfold tailWord_191722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748168952857853088966355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4661783874287608237243613 1748168952857853088966355)
  ·
    refine ⟨2622253429286779633449533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748168952857853088966355 2622253429286779633449533)
    ·
      refine ⟨983345035982542362543575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2622253429286779633449533 983345035982542362543575)
      ·
        refine ⟨1475017553973813543815363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983345035982542362543575 1475017553973813543815363)
        ·
          refine ⟨2212526330960720315723045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475017553973813543815363 2212526330960720315723045)
          ·
            refine ⟨414848687055135059198071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2212526330960720315723045 414848687055135059198071)
            ·
              refine ⟨622273030582702588797107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414848687055135059198071 622273030582702588797107)
              ·
                refine ⟨933409545874053883195661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622273030582702588797107 933409545874053883195661)
                ·
                  refine ⟨350028579702770206198373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933409545874053883195661 350028579702770206198373)
                  ·
                    refine ⟨65630358694269413662195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350028579702770206198373 65630358694269413662195)
                    ·
                      rfl

theorem cell22_191722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_191722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191722 prefixEnd_191722 := by exact prefixLift 191722
  have htrace : WordTrace (prefixWord ++ tailWord_191722) baseStart_191722 baseEnd_191722 := by
    simpa [prefixWord, tailWord_191722, baseEnd_191722] using wordTrace_append hprefix tailTrace_191722
  have hstable : (prefixWord ++ tailWord_191722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191722).length < 2 ^ (prefixWord ++ tailWord_191722).sum := by decide
  have hdescent : baseEnd_191722 < baseStart_191722 := by decide
  rcases family_descends (prefixWord ++ tailWord_191722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191735 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_191735 : Nat := 118140960795 + 191735 * 2 ^ 59
def prefixEnd_191735 : Nat := 4983230072969 + 3 ^ 40 * 191735 * 2
def baseEnd_191735 : Nat := 65634808859941713087155

theorem tailTrace_191735 : CollatzResearch.WordTrace tailWord_191735 prefixEnd_191735 65634808859941713087155 := by
  unfold tailWord_191735
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993149960384315576088659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4662099973589543717392439 6993149960384315576088659)
  ·
    refine ⟨10489724940576473364132989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993149960384315576088659 10489724940576473364132989)
    ·
      refine ⟨3933646852716177511549871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10489724940576473364132989 3933646852716177511549871)
      ·
        refine ⟨5900470279074266267324807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933646852716177511549871 5900470279074266267324807)
        ·
          refine ⟨8850705418611399400987211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900470279074266267324807 8850705418611399400987211)
          ·
            refine ⟨13276058127917099101480817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850705418611399400987211 13276058127917099101480817)
            ·
              refine ⟨9957043595937824326110613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13276058127917099101480817 9957043595937824326110613)
              ·
                refine ⟨466736418559585515286435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9957043595937824326110613 466736418559585515286435)
                ·
                  refine ⟨700104627839378272929653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466736418559585515286435 700104627839378272929653)
                  ·
                    refine ⟨65634808859941713087155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 700104627839378272929653 65634808859941713087155)
                    ·
                      rfl

theorem cell22_191735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_191735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191735 prefixEnd_191735 := by exact prefixLift 191735
  have htrace : WordTrace (prefixWord ++ tailWord_191735) baseStart_191735 baseEnd_191735 := by
    simpa [prefixWord, tailWord_191735, baseEnd_191735] using wordTrace_append hprefix tailTrace_191735
  have hstable : (prefixWord ++ tailWord_191735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191735).length < 2 ^ (prefixWord ++ tailWord_191735).sum := by decide
  have hdescent : baseEnd_191735 < baseStart_191735 := by decide
  rcases family_descends (prefixWord ++ tailWord_191735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191737 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 4]
def baseStart_191737 : Nat := 118140960795 + 191737 * 2 ^ 59
def prefixEnd_191737 : Nat := 4983230072969 + 3 ^ 40 * 191737 * 2
def baseEnd_191737 : Nat := 21878497833604791512383

theorem tailTrace_191737 : CollatzResearch.WordTrace tailWord_191737 prefixEnd_191737 21878497833604791512383 := by
  unfold tailWord_191737
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993222906377069917661465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4662148604251379945107643 6993222906377069917661465)
  ·
    refine ⟨5244917179782802438246099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6993222906377069917661465 5244917179782802438246099)
    ·
      refine ⟨7867375769674203657369149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244917179782802438246099 7867375769674203657369149)
      ·
        refine ⟨2950265913627826371513431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7867375769674203657369149 2950265913627826371513431)
        ·
          refine ⟨4425398870441739557270147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950265913627826371513431 4425398870441739557270147)
          ·
            refine ⟨6638098305662609335905221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425398870441739557270147 6638098305662609335905221)
            ·
              refine ⟨1244643432311739250482229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6638098305662609335905221 1244643432311739250482229)
              ·
                refine ⟨116685321779225554732709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1244643432311739250482229 116685321779225554732709)
                ·
                  refine ⟨21878497833604791512383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116685321779225554732709 21878497833604791512383)
                  ·
                    rfl

theorem cell22_191737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_191737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191737 prefixEnd_191737 := by exact prefixLift 191737
  have htrace : WordTrace (prefixWord ++ tailWord_191737) baseStart_191737 baseEnd_191737 := by
    simpa [prefixWord, tailWord_191737, baseEnd_191737] using wordTrace_append hprefix tailTrace_191737
  have hstable : (prefixWord ++ tailWord_191737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191737).length < 2 ^ (prefixWord ++ tailWord_191737).sum := by decide
  have hdescent : baseEnd_191737 < baseStart_191737 := by decide
  rcases family_descends (prefixWord ++ tailWord_191737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191784 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_191784 : Nat := 118140960795 + 191784 * 2 ^ 59
def prefixEnd_191784 : Nat := 4983230072969 + 3 ^ 40 * 191784 * 2
def baseEnd_191784 : Nat := 65651582561321918612005

theorem tailTrace_191784 : CollatzResearch.WordTrace tailWord_191784 prefixEnd_191784 65651582561321918612005 := by
  unfold tailWord_191784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497468568603398472311203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4663291424804531296414937 3497468568603398472311203)
  ·
    refine ⟨5246202852905097708466805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497468568603398472311203 5246202852905097708466805)
    ·
      refine ⟨491831517459852910168763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5246202852905097708466805 491831517459852910168763)
      ·
        refine ⟨737747276189779365253145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491831517459852910168763 737747276189779365253145)
        ·
          refine ⟨553310457142334523939859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737747276189779365253145 553310457142334523939859)
          ·
            refine ⟨829965685713501785909789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553310457142334523939859 829965685713501785909789)
            ·
              refine ⟨311237132142563169716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829965685713501785909789 311237132142563169716171)
              ·
                refine ⟨466855698213844754574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311237132142563169716171 466855698213844754574257)
                ·
                  refine ⟨350141773660383565930693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466855698213844754574257 350141773660383565930693)
                  ·
                    refine ⟨65651582561321918612005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350141773660383565930693 65651582561321918612005)
                    ·
                      rfl

theorem cell22_191784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_191784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191784 prefixEnd_191784 := by exact prefixLift 191784
  have htrace : WordTrace (prefixWord ++ tailWord_191784) baseStart_191784 baseEnd_191784 := by
    simpa [prefixWord, tailWord_191784, baseEnd_191784] using wordTrace_append hprefix tailTrace_191784
  have hstable : (prefixWord ++ tailWord_191784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191784).length < 2 ^ (prefixWord ++ tailWord_191784).sum := by decide
  have hdescent : baseEnd_191784 < baseStart_191784 := by decide
  rcases family_descends (prefixWord ++ tailWord_191784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191921 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_191921 : Nat := 118140960795 + 191921 * 2 ^ 59
def prefixEnd_191921 : Nat := 4983230072969 + 3 ^ 40 * 191921 * 2
def baseEnd_191921 : Nat := 65698480461099227936585

theorem tailTrace_191921 : CollatzResearch.WordTrace tailWord_191921 prefixEnd_191921 65698480461099227936585 := by
  unfold tailWord_191921
  simp only [CollatzResearch.WordTrace]
  refine ⟨6999933937710469342359617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4666622625140312894906411 6999933937710469342359617)
  ·
    refine ⟨5249950453282852006769713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6999933937710469342359617 5249950453282852006769713)
    ·
      refine ⟨3937462839962139005077285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5249950453282852006769713 3937462839962139005077285)
      ·
        refine ⟨738274282492901063451991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3937462839962139005077285 738274282492901063451991)
        ·
          refine ⟨1107411423739351595177987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738274282492901063451991 1107411423739351595177987)
          ·
            refine ⟨1661117135609027392766981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107411423739351595177987 1661117135609027392766981)
            ·
              refine ⟨311459462926692636143809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1661117135609027392766981 311459462926692636143809)
              ·
                refine ⟨233594597195019477107857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311459462926692636143809 233594597195019477107857)
                ·
                  refine ⟨175195947896264607830893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233594597195019477107857 175195947896264607830893)
                  ·
                    refine ⟨65698480461099227936585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175195947896264607830893 65698480461099227936585)
                    ·
                      rfl

theorem cell22_191921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_191921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_191921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_191921 prefixEnd_191921 := by exact prefixLift 191921
  have htrace : WordTrace (prefixWord ++ tailWord_191921) baseStart_191921 baseEnd_191921 := by
    simpa [prefixWord, tailWord_191921, baseEnd_191921] using wordTrace_append hprefix tailTrace_191921
  have hstable : (prefixWord ++ tailWord_191921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191921).length < 2 ^ (prefixWord ++ tailWord_191921).sum := by decide
  have hdescent : baseEnd_191921 < baseStart_191921 := by decide
  rcases family_descends (prefixWord ++ tailWord_191921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192060 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_192060 : Nat := 118140960795 + 192060 * 2 ^ 59
def prefixEnd_192060 : Nat := 4983230072969 + 3 ^ 40 * 192060 * 2
def baseEnd_192060 : Nat := 65746063001749198711159

theorem tailTrace_192060 : CollatzResearch.WordTrace tailWord_192060 prefixEnd_192060 65746063001749198711159 := by
  unfold tailWord_192060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502501842103448040834817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4670002456137930721113089 3502501842103448040834817)
  ·
    refine ⟨2626876381577586030626113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3502501842103448040834817 2626876381577586030626113)
    ·
      refine ⟨1970157286183189522969585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2626876381577586030626113 1970157286183189522969585)
      ·
        refine ⟨1477617964637392142227189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970157286183189522969585 1477617964637392142227189)
        ·
          refine ⟨138526684184755513333799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1477617964637392142227189 138526684184755513333799)
          ·
            refine ⟨207790026277133270000699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138526684184755513333799 207790026277133270000699)
            ·
              refine ⟨311685039415699905001049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207790026277133270000699 311685039415699905001049)
              ·
                refine ⟨233763779561774928750787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311685039415699905001049 233763779561774928750787)
                ·
                  refine ⟨350645669342662393126181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233763779561774928750787 350645669342662393126181)
                  ·
                    refine ⟨65746063001749198711159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350645669342662393126181 65746063001749198711159)
                    ·
                      rfl

theorem cell22_192060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_192060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192060 prefixEnd_192060 := by exact prefixLift 192060
  have htrace : WordTrace (prefixWord ++ tailWord_192060) baseStart_192060 baseEnd_192060 := by
    simpa [prefixWord, tailWord_192060, baseEnd_192060] using wordTrace_append hprefix tailTrace_192060
  have hstable : (prefixWord ++ tailWord_192060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192060).length < 2 ^ (prefixWord ++ tailWord_192060).sum := by decide
  have hdescent : baseEnd_192060 < baseStart_192060 := by decide
  rcases family_descends (prefixWord ++ tailWord_192060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192099 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_192099 : Nat := 118140960795 + 192099 * 2 ^ 59
def prefixEnd_192099 : Nat := 4983230072969 + 3 ^ 40 * 192099 * 2
def baseEnd_192099 : Nat := 65759413498766096986039

theorem tailTrace_192099 : CollatzResearch.WordTrace tailWord_192099 prefixEnd_192099 65759413498766096986039 := by
  unfold tailWord_192099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006426131065605742339351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4670950754043737161559567 7006426131065605742339351)
  ·
    refine ⟨10509639196598408613509027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7006426131065605742339351 10509639196598408613509027)
    ·
      refine ⟨15764458794897612920263541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10509639196598408613509027 15764458794897612920263541)
      ·
        refine ⟨1477918012021651211274707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15764458794897612920263541 1477918012021651211274707)
        ·
          refine ⟨2216877018032476816912061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477918012021651211274707 2216877018032476816912061)
          ·
            refine ⟨831328881762178806342023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216877018032476816912061 831328881762178806342023)
            ·
              refine ⟨1246993322643268209513035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831328881762178806342023 1246993322643268209513035)
              ·
                refine ⟨1870489983964902314269553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246993322643268209513035 1870489983964902314269553)
                ·
                  refine ⟨1402867487973676735702165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1870489983964902314269553 1402867487973676735702165)
                  ·
                    refine ⟨65759413498766096986039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1402867487973676735702165 65759413498766096986039)
                    ·
                      rfl

theorem cell22_192099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_192099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192099 prefixEnd_192099 := by exact prefixLift 192099
  have htrace : WordTrace (prefixWord ++ tailWord_192099) baseStart_192099 baseEnd_192099 := by
    simpa [prefixWord, tailWord_192099, baseEnd_192099] using wordTrace_append hprefix tailTrace_192099
  have hstable : (prefixWord ++ tailWord_192099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192099).length < 2 ^ (prefixWord ++ tailWord_192099).sum := by decide
  have hdescent : baseEnd_192099 < baseStart_192099 := by decide
  rcases family_descends (prefixWord ++ tailWord_192099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192118 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_192118 : Nat := 118140960795 + 192118 * 2 ^ 59
def prefixEnd_192118 : Nat := 4983230072969 + 3 ^ 40 * 192118 * 2
def baseEnd_192118 : Nat := 65765917587056380760981

theorem tailTrace_192118 : CollatzResearch.WordTrace tailWord_192118 prefixEnd_192118 65765917587056380760981 := by
  unfold tailWord_192118
  simp only [CollatzResearch.WordTrace]
  refine ⟨437944944874798249205063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4671412745331181324854005 437944944874798249205063)
  ·
    refine ⟨656917417312197373807595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437944944874798249205063 656917417312197373807595)
    ·
      refine ⟨985376125968296060711393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656917417312197373807595 985376125968296060711393)
      ·
        refine ⟨739032094476222045533545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985376125968296060711393 739032094476222045533545)
        ·
          refine ⟨554274070857166534150159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739032094476222045533545 554274070857166534150159)
          ·
            refine ⟨831411106285749801225239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554274070857166534150159 831411106285749801225239)
            ·
              refine ⟨1247116659428624701837859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831411106285749801225239 1247116659428624701837859)
              ·
                refine ⟨1870674989142937052756789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247116659428624701837859 1870674989142937052756789)
                ·
                  refine ⟨175375780232150348695949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870674989142937052756789 175375780232150348695949)
                  ·
                    refine ⟨65765917587056380760981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175375780232150348695949 65765917587056380760981)
                    ·
                      rfl

theorem cell22_192118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_192118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192118 prefixEnd_192118 := by exact prefixLift 192118
  have htrace : WordTrace (prefixWord ++ tailWord_192118) baseStart_192118 baseEnd_192118 := by
    simpa [prefixWord, tailWord_192118, baseEnd_192118] using wordTrace_append hprefix tailTrace_192118
  have hstable : (prefixWord ++ tailWord_192118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192118).length < 2 ^ (prefixWord ++ tailWord_192118).sum := by decide
  have hdescent : baseEnd_192118 < baseStart_192118 := by decide
  rcases family_descends (prefixWord ++ tailWord_192118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192135 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 1, 3]
def baseStart_192135 : Nat := 118140960795 + 192135 * 2 ^ 59
def prefixEnd_192135 : Nat := 4983230072969 + 3 ^ 40 * 192135 * 2
def baseEnd_192135 : Nat := 65771737034474003085929

theorem tailTrace_192135 : CollatzResearch.WordTrace tailWord_192135 prefixEnd_192135 65771737034474003085929 := by
  unfold tailWord_192135
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007739158935183890649859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4671826105956789260433239 7007739158935183890649859)
  ·
    refine ⟨10511608738402775835974789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7007739158935183890649859 10511608738402775835974789)
    ·
      refine ⟨1970926638450520469245273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10511608738402775835974789 1970926638450520469245273)
      ·
        refine ⟨1478194978837890351933955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970926638450520469245273 1478194978837890351933955)
        ·
          refine ⟨2217292468256835527900933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478194978837890351933955 2217292468256835527900933)
          ·
            refine ⟨415742337798156661481425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2217292468256835527900933 415742337798156661481425)
            ·
              refine ⟨311806753348617496111069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415742337798156661481425 311806753348617496111069)
              ·
                refine ⟨116927532505731561041651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311806753348617496111069 116927532505731561041651)
                ·
                  refine ⟨175391298758597341562477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116927532505731561041651 175391298758597341562477)
                  ·
                    refine ⟨65771737034474003085929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175391298758597341562477 65771737034474003085929)
                    ·
                      rfl

theorem cell22_192135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_192135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192135 prefixEnd_192135 := by exact prefixLift 192135
  have htrace : WordTrace (prefixWord ++ tailWord_192135) baseStart_192135 baseEnd_192135 := by
    simpa [prefixWord, tailWord_192135, baseEnd_192135] using wordTrace_append hprefix tailTrace_192135
  have hstable : (prefixWord ++ tailWord_192135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192135).length < 2 ^ (prefixWord ++ tailWord_192135).sum := by decide
  have hdescent : baseEnd_192135 < baseStart_192135 := by decide
  rcases family_descends (prefixWord ++ tailWord_192135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192148 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_192148 : Nat := 118140960795 + 192148 * 2 ^ 59
def prefixEnd_192148 : Nat := 4983230072969 + 3 ^ 40 * 192148 * 2
def baseEnd_192148 : Nat := 21925395733382100836963

theorem tailTrace_192148 : CollatzResearch.WordTrace tailWord_192148 prefixEnd_192148 21925395733382100836963 := by
  unfold tailWord_192148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504106653944043555436549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4672142205258724740582065 3504106653944043555436549)
  ·
    refine ⟨657019997614508166644353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3504106653944043555436549 657019997614508166644353)
    ·
      refine ⟨492764998210881124983265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 657019997614508166644353 492764998210881124983265)
      ·
        refine ⟨369573748658160843737449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492764998210881124983265 369573748658160843737449)
        ·
          refine ⟨277180311493620632803087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369573748658160843737449 277180311493620632803087)
          ·
            refine ⟨415770467240430949204631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277180311493620632803087 415770467240430949204631)
            ·
              refine ⟨623655700860646423806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415770467240430949204631 623655700860646423806947)
              ·
                refine ⟨935483551290969635710421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623655700860646423806947 935483551290969635710421)
                ·
                  refine ⟨21925395733382100836963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 935483551290969635710421 21925395733382100836963)
                  ·
                    rfl

theorem cell22_192148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_192148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192148 prefixEnd_192148 := by exact prefixLift 192148
  have htrace : WordTrace (prefixWord ++ tailWord_192148) baseStart_192148 baseEnd_192148 := by
    simpa [prefixWord, tailWord_192148, baseEnd_192148] using wordTrace_append hprefix tailTrace_192148
  have hstable : (prefixWord ++ tailWord_192148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192148).length < 2 ^ (prefixWord ++ tailWord_192148).sum := by decide
  have hdescent : baseEnd_192148 < baseStart_192148 := by decide
  rcases family_descends (prefixWord ++ tailWord_192148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192191 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 6, 3]
def baseStart_192191 : Nat := 118140960795 + 192191 * 2 ^ 59
def prefixEnd_192191 : Nat := 4983230072969 + 3 ^ 40 * 192191 * 2
def baseEnd_192191 : Nat := 65790906978908523685757

theorem tailTrace_192191 : CollatzResearch.WordTrace tailWord_192191 prefixEnd_192191 65790906978908523685757 := by
  unfold tailWord_192191
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009781646732305454688427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4673187764488203636458951 7009781646732305454688427)
  ·
    refine ⟨10514672470098458182032641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7009781646732305454688427 10514672470098458182032641)
    ·
      refine ⟨7886004352573843636524481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10514672470098458182032641 7886004352573843636524481)
      ·
        refine ⟨5914503264430382727393361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7886004352573843636524481 5914503264430382727393361)
        ·
          refine ⟨4435877448322787045545021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5914503264430382727393361 4435877448322787045545021)
          ·
            refine ⟨1663454043121045142079383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4435877448322787045545021 1663454043121045142079383)
            ·
              refine ⟨2495181064681567713119075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663454043121045142079383 2495181064681567713119075)
              ·
                refine ⟨3742771597022351569678613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495181064681567713119075 3742771597022351569678613)
                ·
                  refine ⟨175442418610422729828685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3742771597022351569678613 175442418610422729828685)
                  ·
                    refine ⟨65790906978908523685757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175442418610422729828685 65790906978908523685757)
                    ·
                      rfl

theorem cell22_192191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_192191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192191 prefixEnd_192191 := by exact prefixLift 192191
  have htrace : WordTrace (prefixWord ++ tailWord_192191) baseStart_192191 baseEnd_192191 := by
    simpa [prefixWord, tailWord_192191, baseEnd_192191] using wordTrace_append hprefix tailTrace_192191
  have hstable : (prefixWord ++ tailWord_192191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192191).length < 2 ^ (prefixWord ++ tailWord_192191).sum := by decide
  have hdescent : baseEnd_192191 < baseStart_192191 := by decide
  rcases family_descends (prefixWord ++ tailWord_192191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192225 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_192225 : Nat := 118140960795 + 192225 * 2 ^ 59
def prefixEnd_192225 : Nat := 4983230072969 + 3 ^ 40 * 192225 * 2
def baseEnd_192225 : Nat := 65802545873743768335653

theorem tailTrace_192225 : CollatzResearch.WordTrace tailWord_192225 prefixEnd_192225 65802545873743768335653 := by
  unfold tailWord_192225
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011021728609129261426129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4674014485739419507617419 7011021728609129261426129)
  ·
    refine ⟨5258266296456846946069597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7011021728609129261426129 5258266296456846946069597)
    ·
      refine ⟨1971849861171317604776099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5258266296456846946069597 1971849861171317604776099)
      ·
        refine ⟨2957774791756976407164149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971849861171317604776099 2957774791756976407164149)
        ·
          refine ⟨277291386727216538171639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2957774791756976407164149 277291386727216538171639)
          ·
            refine ⟨415937080090824807257459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277291386727216538171639 415937080090824807257459)
            ·
              refine ⟨623905620136237210886189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415937080090824807257459 623905620136237210886189)
              ·
                refine ⟨233964607551088954082321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623905620136237210886189 233964607551088954082321)
                ·
                  refine ⟨175473455663316715561741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233964607551088954082321 175473455663316715561741)
                  ·
                    refine ⟨65802545873743768335653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175473455663316715561741 65802545873743768335653)
                    ·
                      rfl

theorem cell22_192225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_192225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192225 prefixEnd_192225 := by exact prefixLift 192225
  have htrace : WordTrace (prefixWord ++ tailWord_192225) baseStart_192225 baseEnd_192225 := by
    simpa [prefixWord, tailWord_192225, baseEnd_192225] using wordTrace_append hprefix tailTrace_192225
  have hstable : (prefixWord ++ tailWord_192225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192225).length < 2 ^ (prefixWord ++ tailWord_192225).sum := by decide
  have hdescent : baseEnd_192225 < baseStart_192225 := by decide
  rcases family_descends (prefixWord ++ tailWord_192225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192328 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_192328 : Nat := 118140960795 + 192328 * 2 ^ 59
def prefixEnd_192328 : Nat := 4983230072969 + 3 ^ 40 * 192328 * 2
def baseEnd_192328 : Nat := 21945934959561944336779

theorem tailTrace_192328 : CollatzResearch.WordTrace tailWord_192328 prefixEnd_192328 21945934959561944336779 := by
  unfold tailWord_192328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507389223617988926212819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4676518964823985234950425 3507389223617988926212819)
  ·
    refine ⟨5261083835426983389319229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3507389223617988926212819 5261083835426983389319229)
    ·
      refine ⟨1972906438285118770994711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5261083835426983389319229 1972906438285118770994711)
      ·
        refine ⟨2959359657427678156492067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972906438285118770994711 2959359657427678156492067)
        ·
          refine ⟨4439039486141517234738101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959359657427678156492067 4439039486141517234738101)
          ·
            refine ⟨416159951825767240756697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4439039486141517234738101 416159951825767240756697)
            ·
              refine ⟨312119963869325430567523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416159951825767240756697 312119963869325430567523)
              ·
                refine ⟨468179945803988145851285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312119963869325430567523 468179945803988145851285)
                ·
                  refine ⟨21945934959561944336779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 468179945803988145851285 21945934959561944336779)
                  ·
                    rfl

theorem cell22_192328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_192328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192328 prefixEnd_192328 := by exact prefixLift 192328
  have htrace : WordTrace (prefixWord ++ tailWord_192328) baseStart_192328 baseEnd_192328 := by
    simpa [prefixWord, tailWord_192328, baseEnd_192328] using wordTrace_append hprefix tailTrace_192328
  have hstable : (prefixWord ++ tailWord_192328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192328).length < 2 ^ (prefixWord ++ tailWord_192328).sum := by decide
  have hdescent : baseEnd_192328 < baseStart_192328 := by decide
  rcases family_descends (prefixWord ++ tailWord_192328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192430 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_192430 : Nat := 118140960795 + 192430 * 2 ^ 59
def prefixEnd_192430 : Nat := 4983230072969 + 3 ^ 40 * 192430 * 2
def baseEnd_192430 : Nat := 21957573854397188986675

theorem tailTrace_192430 : CollatzResearch.WordTrace tailWord_192430 prefixEnd_192430 21957573854397188986675 := by
  unfold tailWord_192430
  simp only [CollatzResearch.WordTrace]
  refine ⟨877312336608306159079843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4678999128577632848425829 877312336608306159079843)
  ·
    refine ⟨1315968504912459238619765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 877312336608306159079843 1315968504912459238619765)
    ·
      refine ⟨123372047335543053620603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1315968504912459238619765 123372047335543053620603)
      ·
        refine ⟨185058071003314580430905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123372047335543053620603 185058071003314580430905)
        ·
          refine ⟨138793553252485935323179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185058071003314580430905 138793553252485935323179)
          ·
            refine ⟨208190329878728902984769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138793553252485935323179 208190329878728902984769)
            ·
              refine ⟨156142747409046677238577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208190329878728902984769 156142747409046677238577)
              ·
                refine ⟨117107060556785007928933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156142747409046677238577 117107060556785007928933)
                ·
                  refine ⟨21957573854397188986675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117107060556785007928933 21957573854397188986675)
                  ·
                    rfl

theorem cell22_192430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_192430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192430 prefixEnd_192430 := by exact prefixLift 192430
  have htrace : WordTrace (prefixWord ++ tailWord_192430) baseStart_192430 baseEnd_192430 := by
    simpa [prefixWord, tailWord_192430, baseEnd_192430] using wordTrace_append hprefix tailTrace_192430
  have hstable : (prefixWord ++ tailWord_192430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192430).length < 2 ^ (prefixWord ++ tailWord_192430).sum := by decide
  have hdescent : baseEnd_192430 < baseStart_192430 := by decide
  rcases family_descends (prefixWord ++ tailWord_192430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192448 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_192448 : Nat := 118140960795 + 192448 * 2 ^ 59
def prefixEnd_192448 : Nat := 4983230072969 + 3 ^ 40 * 192448 * 2
def baseEnd_192448 : Nat := 65878883331045520009969

theorem tailTrace_192448 : CollatzResearch.WordTrace tailWord_192448 prefixEnd_192448 65878883331045520009969 := by
  unfold tailWord_192448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509577603400619173396999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4679436804534158897862665 3509577603400619173396999)
  ·
    refine ⟨5264366405100928760095499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509577603400619173396999 5264366405100928760095499)
    ·
      refine ⟨7896549607651393140143249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264366405100928760095499 7896549607651393140143249)
      ·
        refine ⟨5922412205738544855107437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7896549607651393140143249 5922412205738544855107437)
        ·
          refine ⟨2220904577151954320665289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5922412205738544855107437 2220904577151954320665289)
          ·
            refine ⟨1665678432863965740498967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2220904577151954320665289 1665678432863965740498967)
            ·
              refine ⟨2498517649295948610748451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665678432863965740498967 2498517649295948610748451)
              ·
                refine ⟨3747776473943922916122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498517649295948610748451 3747776473943922916122677)
                ·
                  refine ⟨351354044432242773386501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3747776473943922916122677 351354044432242773386501)
                  ·
                    refine ⟨65878883331045520009969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 351354044432242773386501 65878883331045520009969)
                    ·
                      rfl

theorem cell22_192448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_192448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192448 prefixEnd_192448 := by exact prefixLift 192448
  have htrace : WordTrace (prefixWord ++ tailWord_192448) baseStart_192448 baseEnd_192448 := by
    simpa [prefixWord, tailWord_192448, baseEnd_192448] using wordTrace_append hprefix tailTrace_192448
  have hstable : (prefixWord ++ tailWord_192448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192448).length < 2 ^ (prefixWord ++ tailWord_192448).sum := by decide
  have hdescent : baseEnd_192448 < baseStart_192448 := by decide
  rcases family_descends (prefixWord ++ tailWord_192448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192463 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 6]
def baseStart_192463 : Nat := 118140960795 + 192463 * 2 ^ 59
def prefixEnd_192463 : Nat := 4983230072969 + 3 ^ 40 * 192463 * 2
def baseEnd_192463 : Nat := 21961339379196826961641

theorem tailTrace_192463 : CollatzResearch.WordTrace tailWord_192463 prefixEnd_192463 21961339379196826961641 := by
  unfold tailWord_192463
  simp only [CollatzResearch.WordTrace]
  refine ⟨7019702301746895908590043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4679801534497930605726695 7019702301746895908590043)
  ·
    refine ⟨10529553452620343862885065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7019702301746895908590043 10529553452620343862885065)
    ·
      refine ⟨7897165089465257897163799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10529553452620343862885065 7897165089465257897163799)
      ·
        refine ⟨11845747634197886845745699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7897165089465257897163799 11845747634197886845745699)
        ·
          refine ⟨17768621451296830268618549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845747634197886845745699 17768621451296830268618549)
          ·
            refine ⟨1665808261059077837682989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17768621451296830268618549 1665808261059077837682989)
            ·
              refine ⟨624678097897154189131121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1665808261059077837682989 624678097897154189131121)
              ·
                refine ⟨468508573422865641848341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624678097897154189131121 468508573422865641848341)
                ·
                  refine ⟨21961339379196826961641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 468508573422865641848341 21961339379196826961641)
                  ·
                    rfl

theorem cell22_192463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_192463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192463 prefixEnd_192463 := by exact prefixLift 192463
  have htrace : WordTrace (prefixWord ++ tailWord_192463) baseStart_192463 baseEnd_192463 := by
    simpa [prefixWord, tailWord_192463, baseEnd_192463] using wordTrace_append hprefix tailTrace_192463
  have hstable : (prefixWord ++ tailWord_192463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192463).length < 2 ^ (prefixWord ++ tailWord_192463).sum := by decide
  have hdescent : baseEnd_192463 < baseStart_192463 := by decide
  rcases family_descends (prefixWord ++ tailWord_192463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192495 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 4, 3]
def baseStart_192495 : Nat := 118140960795 + 192495 * 2 ^ 59
def prefixEnd_192495 : Nat := 4983230072969 + 3 ^ 40 * 192495 * 2
def baseEnd_192495 : Nat := 65894972391553064084825

theorem tailTrace_192495 : CollatzResearch.WordTrace tailWord_192495 prefixEnd_192495 65894972391553064084825 := by
  unfold tailWord_192495
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020869437630965373754939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4680579625087310249169959 7020869437630965373754939)
  ·
    refine ⟨10531304156446448060632409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7020869437630965373754939 10531304156446448060632409)
    ·
      refine ⟨7898478117334836045474307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10531304156446448060632409 7898478117334836045474307)
      ·
        refine ⟨11847717176002254068211461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7898478117334836045474307 11847717176002254068211461)
        ·
          refine ⟨2221446970500422637789649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11847717176002254068211461 2221446970500422637789649)
          ·
            refine ⟨1666085227875316978342237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221446970500422637789649 1666085227875316978342237)
            ·
              refine ⟨624781960453243866878339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666085227875316978342237 624781960453243866878339)
              ·
                refine ⟨937172940679865800317509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624781960453243866878339 937172940679865800317509)
                ·
                  refine ⟨175719926377474837559533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937172940679865800317509 175719926377474837559533)
                  ·
                    refine ⟨65894972391553064084825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175719926377474837559533 65894972391553064084825)
                    ·
                      rfl

theorem cell22_192495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_192495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192495 prefixEnd_192495 := by exact prefixLift 192495
  have htrace : WordTrace (prefixWord ++ tailWord_192495) baseStart_192495 baseEnd_192495 := by
    simpa [prefixWord, tailWord_192495, baseEnd_192495] using wordTrace_append hprefix tailTrace_192495
  have hstable : (prefixWord ++ tailWord_192495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192495).length < 2 ^ (prefixWord ++ tailWord_192495).sum := by decide
  have hdescent : baseEnd_192495 < baseStart_192495 := by decide
  rcases family_descends (prefixWord ++ tailWord_192495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192508 : List Nat := [2, 2, 2, 1, 2, 2, 2, 9]
def baseStart_192508 : Nat := 118140960795 + 192508 * 2 ^ 59
def prefixEnd_192508 : Nat := 4983230072969 + 3 ^ 40 * 192508 * 2
def baseEnd_192508 : Nat := 7322158061913929278865

theorem tailTrace_192508 : CollatzResearch.WordTrace tailWord_192508 prefixEnd_192508 7322158061913929278865 := by
  unfold tailWord_192508
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510671793291934296989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4680895724389245729318785 3510671793291934296989089)
  ·
    refine ⟨2633003844968950722741817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3510671793291934296989089 2633003844968950722741817)
    ·
      refine ⟨1974752883726713042056363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2633003844968950722741817 1974752883726713042056363)
      ·
        refine ⟨2962129325590069563084545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974752883726713042056363 2962129325590069563084545)
        ·
          refine ⟨2221596994192552172313409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962129325590069563084545 2221596994192552172313409)
          ·
            refine ⟨1666197745644414129235057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221596994192552172313409 1666197745644414129235057)
            ·
              refine ⟨1249648309233310596926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666197745644414129235057 1249648309233310596926293)
              ·
                refine ⟨7322158061913929278865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1249648309233310596926293 7322158061913929278865)
                ·
                  rfl

theorem cell22_192508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_192508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192508 prefixEnd_192508 := by exact prefixLift 192508
  have htrace : WordTrace (prefixWord ++ tailWord_192508) baseStart_192508 baseEnd_192508 := by
    simpa [prefixWord, tailWord_192508, baseEnd_192508] using wordTrace_append hprefix tailTrace_192508
  have hstable : (prefixWord ++ tailWord_192508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192508).length < 2 ^ (prefixWord ++ tailWord_192508).sum := by decide
  have hdescent : baseEnd_192508 < baseStart_192508 := by decide
  rcases family_descends (prefixWord ++ tailWord_192508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192523 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_192523 : Nat := 118140960795 + 192523 * 2 ^ 59
def prefixEnd_192523 : Nat := 4983230072969 + 3 ^ 40 * 192523 * 2
def baseEnd_192523 : Nat := 65904557363770324384739

theorem tailTrace_192523 : CollatzResearch.WordTrace tailWord_192523 prefixEnd_192523 65904557363770324384739 := by
  unfold tailWord_192523
  simp only [CollatzResearch.WordTrace]
  refine ⟨7021890681529526155774223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4681260454353017437182815 7021890681529526155774223)
  ·
    refine ⟨10532836022294289233661335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7021890681529526155774223 10532836022294289233661335)
    ·
      refine ⟨15799254033441433850492003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10532836022294289233661335 15799254033441433850492003)
      ·
        refine ⟨23698881050162150775738005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15799254033441433850492003 23698881050162150775738005)
        ·
          refine ⟨1110885049226350817612719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23698881050162150775738005 1110885049226350817612719)
          ·
            refine ⟨1666327573839526226419079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110885049226350817612719 1666327573839526226419079)
            ·
              refine ⟨2499491360759289339628619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666327573839526226419079 2499491360759289339628619)
              ·
                refine ⟨3749237041138934009442929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499491360759289339628619 3749237041138934009442929)
                ·
                  refine ⟨2811927780854200507082197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3749237041138934009442929 2811927780854200507082197)
                  ·
                    refine ⟨65904557363770324384739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2811927780854200507082197 65904557363770324384739)
                    ·
                      rfl

theorem cell22_192523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_192523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192523 prefixEnd_192523 := by exact prefixLift 192523
  have htrace : WordTrace (prefixWord ++ tailWord_192523) baseStart_192523 baseEnd_192523 := by
    simpa [prefixWord, tailWord_192523, baseEnd_192523] using wordTrace_append hprefix tailTrace_192523
  have hstable : (prefixWord ++ tailWord_192523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192523).length < 2 ^ (prefixWord ++ tailWord_192523).sum := by decide
  have hdescent : baseEnd_192523 < baseStart_192523 := by decide
  rcases family_descends (prefixWord ++ tailWord_192523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192615 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 6]
def baseStart_192615 : Nat := 118140960795 + 192615 * 2 ^ 59
def prefixEnd_192615 : Nat := 4983230072969 + 3 ^ 40 * 192615 * 2
def baseEnd_192615 : Nat := 21978683614637583694819

theorem tailTrace_192615 : CollatzResearch.WordTrace tailWord_192615 prefixEnd_192615 21978683614637583694819 := by
  unfold tailWord_192615
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025246197196225868123299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4683497464797483912082199 7025246197196225868123299)
  ·
    refine ⟨10537869295794338802184949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7025246197196225868123299 10537869295794338802184949)
    ·
      refine ⟨987925246480719262704839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10537869295794338802184949 987925246480719262704839)
      ·
        refine ⟨1481887869721078894057259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987925246480719262704839 1481887869721078894057259)
        ·
          refine ⟨2222831804581618341085889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481887869721078894057259 2222831804581618341085889)
          ·
            refine ⟨1667123853436213755814417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222831804581618341085889 1667123853436213755814417)
            ·
              refine ⟨1250342890077160316860813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667123853436213755814417 1250342890077160316860813)
              ·
                refine ⟨468878583778935118822805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250342890077160316860813 468878583778935118822805)
                ·
                  refine ⟨21978683614637583694819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 468878583778935118822805 21978683614637583694819)
                  ·
                    rfl

theorem cell22_192615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_192615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192615 prefixEnd_192615 := by exact prefixLift 192615
  have htrace : WordTrace (prefixWord ++ tailWord_192615) baseStart_192615 baseEnd_192615 := by
    simpa [prefixWord, tailWord_192615, baseEnd_192615] using wordTrace_append hprefix tailTrace_192615
  have hstable : (prefixWord ++ tailWord_192615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192615).length < 2 ^ (prefixWord ++ tailWord_192615).sum := by decide
  have hdescent : baseEnd_192615 < baseStart_192615 := by decide
  rcases family_descends (prefixWord ++ tailWord_192615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192664 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_192664 : Nat := 118140960795 + 192664 * 2 ^ 59
def prefixEnd_192664 : Nat := 4983230072969 + 3 ^ 40 * 192664 * 2
def baseEnd_192664 : Nat := 65952824545292956609307

theorem tailTrace_192664 : CollatzResearch.WordTrace tailWord_192664 prefixEnd_192664 65952824545292956609307 := by
  unfold tailWord_192664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513516687009353618328523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4684688916012471491104697 3513516687009353618328523)
  ·
    refine ⟨5270275030514030427492785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3513516687009353618328523 5270275030514030427492785)
    ·
      refine ⟨3952706272885522820619589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5270275030514030427492785 3952706272885522820619589)
      ·
        refine ⟨741132426166035528866173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3952706272885522820619589 741132426166035528866173)
        ·
          refine ⟨277924659812263323324815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 741132426166035528866173 277924659812263323324815)
          ·
            refine ⟨416886989718394984987223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277924659812263323324815 416886989718394984987223)
            ·
              refine ⟨625330484577592477480835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416886989718394984987223 625330484577592477480835)
              ·
                refine ⟨937995726866388716221253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625330484577592477480835 937995726866388716221253)
                ·
                  refine ⟨175874198787447884291485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937995726866388716221253 175874198787447884291485)
                  ·
                    refine ⟨65952824545292956609307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175874198787447884291485 65952824545292956609307)
                    ·
                      rfl

theorem cell22_192664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_192664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192664 prefixEnd_192664 := by exact prefixLift 192664
  have htrace : WordTrace (prefixWord ++ tailWord_192664) baseStart_192664 baseEnd_192664 := by
    simpa [prefixWord, tailWord_192664, baseEnd_192664] using wordTrace_append hprefix tailTrace_192664
  have hstable : (prefixWord ++ tailWord_192664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192664).length < 2 ^ (prefixWord ++ tailWord_192664).sum := by decide
  have hdescent : baseEnd_192664 < baseStart_192664 := by decide
  rcases family_descends (prefixWord ++ tailWord_192664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192722 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_192722 : Nat := 118140960795 + 192722 * 2 ^ 59
def prefixEnd_192722 : Nat := 4983230072969 + 3 ^ 40 * 192722 * 2
def baseEnd_192722 : Nat := 21990893043533379553043

theorem tailTrace_192722 : CollatzResearch.WordTrace tailWord_192722 prefixEnd_192722 21990893043533379553043 := by
  unfold tailWord_192722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757287201952145785567105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4686099205205722094845613 1757287201952145785567105)
  ·
    refine ⟨1317965401464109339175329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757287201952145785567105 1317965401464109339175329)
    ·
      refine ⟨988474051098082004381497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1317965401464109339175329 988474051098082004381497)
      ·
        refine ⟨741355538323561503286123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988474051098082004381497 741355538323561503286123)
        ·
          refine ⟨1112033307485342254929185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741355538323561503286123 1112033307485342254929185)
          ·
            refine ⟨834024980614006691196889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112033307485342254929185 834024980614006691196889)
            ·
              refine ⟨625518735460505018397667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834024980614006691196889 625518735460505018397667)
              ·
                refine ⟨938278103190757527596501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625518735460505018397667 938278103190757527596501)
                ·
                  refine ⟨21990893043533379553043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 938278103190757527596501 21990893043533379553043)
                  ·
                    rfl

theorem cell22_192722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_192722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192722 prefixEnd_192722 := by exact prefixLift 192722
  have htrace : WordTrace (prefixWord ++ tailWord_192722) baseStart_192722 baseEnd_192722 := by
    simpa [prefixWord, tailWord_192722, baseEnd_192722] using wordTrace_append hprefix tailTrace_192722
  have hstable : (prefixWord ++ tailWord_192722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192722).length < 2 ^ (prefixWord ++ tailWord_192722).sum := by decide
  have hdescent : baseEnd_192722 < baseStart_192722 := by decide
  rcases family_descends (prefixWord ++ tailWord_192722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192732 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_192732 : Nat := 118140960795 + 192732 * 2 ^ 59
def prefixEnd_192732 : Nat := 4983230072969 + 3 ^ 40 * 192732 * 2
def baseEnd_192732 : Nat := 65976102334963445909099

theorem tailTrace_192732 : CollatzResearch.WordTrace tailWord_192732 prefixEnd_192732 65976102334963445909099 := by
  unfold tailWord_192732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514756768886177425066225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4686342358514903233421633 3514756768886177425066225)
  ·
    refine ⟨2636067576664633068799669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3514756768886177425066225 2636067576664633068799669)
    ·
      refine ⟨247131335312309350199969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2636067576664633068799669 247131335312309350199969)
      ·
        refine ⟨185348501484232012649977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247131335312309350199969 185348501484232012649977)
        ·
          refine ⟨139011376113174009487483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185348501484232012649977 139011376113174009487483)
          ·
            refine ⟨208517064169761014231225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139011376113174009487483 208517064169761014231225)
            ·
              refine ⟨156387798127320760673419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208517064169761014231225 156387798127320760673419)
              ·
                refine ⟨234581697190981141010129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156387798127320760673419 234581697190981141010129)
                ·
                  refine ⟨175936272893235855757597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234581697190981141010129 175936272893235855757597)
                  ·
                    refine ⟨65976102334963445909099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 175936272893235855757597 65976102334963445909099)
                    ·
                      rfl

theorem cell22_192732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_192732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192732 prefixEnd_192732 := by exact prefixLift 192732
  have htrace : WordTrace (prefixWord ++ tailWord_192732) baseStart_192732 baseEnd_192732 := by
    simpa [prefixWord, tailWord_192732, baseEnd_192732] using wordTrace_append hprefix tailTrace_192732
  have hstable : (prefixWord ++ tailWord_192732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192732).length < 2 ^ (prefixWord ++ tailWord_192732).sum := by decide
  have hdescent : baseEnd_192732 < baseStart_192732 := by decide
  rcases family_descends (prefixWord ++ tailWord_192732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192735 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_192735 : Nat := 118140960795 + 192735 * 2 ^ 59
def prefixEnd_192735 : Nat := 4983230072969 + 3 ^ 40 * 192735 * 2
def baseEnd_192735 : Nat := 65977129296272438084089

theorem tailTrace_192735 : CollatzResearch.WordTrace tailWord_192735 prefixEnd_192735 65977129296272438084089 := by
  unfold tailWord_192735
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029622956761486362491659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4686415304507657574994439 7029622956761486362491659)
  ·
    refine ⟨10544434435142229543737489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7029622956761486362491659 10544434435142229543737489)
    ·
      refine ⟨7908325826356672157803117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10544434435142229543737489 7908325826356672157803117)
      ·
        refine ⟨2965622184883752059176169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7908325826356672157803117 2965622184883752059176169)
        ·
          refine ⟨2224216638662814044382127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2965622184883752059176169 2224216638662814044382127)
          ·
            refine ⟨3336324957994221066573191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224216638662814044382127 3336324957994221066573191)
            ·
              refine ⟨5004487436991331599859787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336324957994221066573191 5004487436991331599859787)
              ·
                refine ⟨7506731155486997399789681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004487436991331599859787 7506731155486997399789681)
                ·
                  refine ⟨5630048366615248049842261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7506731155486997399789681 5630048366615248049842261)
                  ·
                    refine ⟨65977129296272438084089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5630048366615248049842261 65977129296272438084089)
                    ·
                      rfl

theorem cell22_192735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_192735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192735 prefixEnd_192735 := by exact prefixLift 192735
  have htrace : WordTrace (prefixWord ++ tailWord_192735) baseStart_192735 baseEnd_192735 := by
    simpa [prefixWord, tailWord_192735, baseEnd_192735] using wordTrace_append hprefix tailTrace_192735
  have hstable : (prefixWord ++ tailWord_192735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192735).length < 2 ^ (prefixWord ++ tailWord_192735).sum := by decide
  have hdescent : baseEnd_192735 < baseStart_192735 := by decide
  rcases family_descends (prefixWord ++ tailWord_192735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192782 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_192782 : Nat := 118140960795 + 192782 * 2 ^ 59
def prefixEnd_192782 : Nat := 4983230072969 + 3 ^ 40 * 192782 * 2
def baseEnd_192782 : Nat := 65993218356779982158945

theorem tailTrace_192782 : CollatzResearch.WordTrace tailWord_192782 prefixEnd_192782 65993218356779982158945 := by
  unfold tailWord_192782
  simp only [CollatzResearch.WordTrace]
  refine ⟨878917148448901673681575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4687558125060808926301733 878917148448901673681575)
  ·
    refine ⟨1318375722673352510522363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 878917148448901673681575 1318375722673352510522363)
    ·
      refine ⟨1977563584010028765783545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318375722673352510522363 1977563584010028765783545)
      ·
        refine ⟨1483172688007521574337659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1977563584010028765783545 1483172688007521574337659)
        ·
          refine ⟨2224759032011282361506489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483172688007521574337659 2224759032011282361506489)
          ·
            refine ⟨1668569274008461771129867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224759032011282361506489 1668569274008461771129867)
            ·
              refine ⟨2502853911012692656694801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668569274008461771129867 2502853911012692656694801)
              ·
                refine ⟨1877140433259519492521101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502853911012692656694801 1877140433259519492521101)
                ·
                  refine ⟨703927662472319809695413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1877140433259519492521101 703927662472319809695413)
                  ·
                    refine ⟨65993218356779982158945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 703927662472319809695413 65993218356779982158945)
                    ·
                      rfl

theorem cell22_192782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_192782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192782 prefixEnd_192782 := by exact prefixLift 192782
  have htrace : WordTrace (prefixWord ++ tailWord_192782) baseStart_192782 baseEnd_192782 := by
    simpa [prefixWord, tailWord_192782, baseEnd_192782] using wordTrace_append hprefix tailTrace_192782
  have hstable : (prefixWord ++ tailWord_192782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192782).length < 2 ^ (prefixWord ++ tailWord_192782).sum := by decide
  have hdescent : baseEnd_192782 < baseStart_192782 := by decide
  rcases family_descends (prefixWord ++ tailWord_192782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192799 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 1, 5]
def baseStart_192799 : Nat := 118140960795 + 192799 * 2 ^ 59
def prefixEnd_192799 : Nat := 4983230072969 + 3 ^ 40 * 192799 * 2
def baseEnd_192799 : Nat := 65999037804197604483893

theorem tailTrace_192799 : CollatzResearch.WordTrace tailWord_192799 prefixEnd_192799 65999037804197604483893 := by
  unfold tailWord_192799
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031957228529625292821451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4687971485686416861880967 7031957228529625292821451)
  ·
    refine ⟨10547935842794437939232177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031957228529625292821451 10547935842794437939232177)
    ·
      refine ⟨7910951882095828454424133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10547935842794437939232177 7910951882095828454424133)
      ·
        refine ⟨1483303477892967835204525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7910951882095828454424133 1483303477892967835204525)
        ·
          refine ⟨556238804209862938201697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483303477892967835204525 556238804209862938201697)
          ·
            refine ⟨417179103157397203651273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556238804209862938201697 417179103157397203651273)
            ·
              refine ⟨312884327368047902738455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417179103157397203651273 312884327368047902738455)
              ·
                refine ⟨469326491052071854107683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312884327368047902738455 469326491052071854107683)
                ·
                  refine ⟨703989736578107781161525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469326491052071854107683 703989736578107781161525)
                  ·
                    refine ⟨65999037804197604483893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 703989736578107781161525 65999037804197604483893)
                    ·
                      rfl

theorem cell22_192799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_192799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192799 prefixEnd_192799 := by exact prefixLift 192799
  have htrace : WordTrace (prefixWord ++ tailWord_192799) baseStart_192799 baseEnd_192799 := by
    simpa [prefixWord, tailWord_192799, baseEnd_192799] using wordTrace_append hprefix tailTrace_192799
  have hstable : (prefixWord ++ tailWord_192799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192799).length < 2 ^ (prefixWord ++ tailWord_192799).sum := by decide
  have hdescent : baseEnd_192799 < baseStart_192799 := by decide
  rcases family_descends (prefixWord ++ tailWord_192799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192874 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_192874 : Nat := 118140960795 + 192874 * 2 ^ 59
def prefixEnd_192874 : Nat := 4983230072969 + 3 ^ 40 * 192874 * 2
def baseEnd_192874 : Nat := 22008237278974136286221

theorem tailTrace_192874 : CollatzResearch.WordTrace tailWord_192874 prefixEnd_192874 22008237278974136286221 := by
  unfold tailWord_192874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758673175814478275450419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4689795135505275401201117 1758673175814478275450419)
  ·
    refine ⟨2638009763721717413175629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758673175814478275450419 2638009763721717413175629)
    ·
      refine ⟨989253661395644029940861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2638009763721717413175629 989253661395644029940861)
      ·
        refine ⟨370970123023366511227823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 989253661395644029940861 370970123023366511227823)
        ·
          refine ⟨556455184535049766841735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370970123023366511227823 556455184535049766841735)
          ·
            refine ⟨834682776802574650262603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556455184535049766841735 834682776802574650262603)
            ·
              refine ⟨1252024165203861975393905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834682776802574650262603 1252024165203861975393905)
              ·
                refine ⟨939018123902896481545429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252024165203861975393905 939018123902896481545429)
                ·
                  refine ⟨22008237278974136286221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 939018123902896481545429 22008237278974136286221)
                  ·
                    rfl

theorem cell22_192874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_192874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192874 prefixEnd_192874 := by exact prefixLift 192874
  have htrace : WordTrace (prefixWord ++ tailWord_192874) baseStart_192874 baseEnd_192874 := by
    simpa [prefixWord, tailWord_192874, baseEnd_192874] using wordTrace_append hprefix tailTrace_192874
  have hstable : (prefixWord ++ tailWord_192874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192874).length < 2 ^ (prefixWord ++ tailWord_192874).sum := by decide
  have hdescent : baseEnd_192874 < baseStart_192874 := by decide
  rcases family_descends (prefixWord ++ tailWord_192874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192904 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_192904 : Nat := 118140960795 + 192904 * 2 ^ 59
def prefixEnd_192904 : Nat := 4983230072969 + 3 ^ 40 * 192904 * 2
def baseEnd_192904 : Nat := 66034981450012330608571

theorem tailTrace_192904 : CollatzResearch.WordTrace tailWord_192904 prefixEnd_192904 66034981450012330608571 := by
  unfold tailWord_192904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517893446574614112696883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4690524595432818816929177 3517893446574614112696883)
  ·
    refine ⟨5276840169861921169045325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517893446574614112696883 5276840169861921169045325)
    ·
      refine ⟨1978815063698220438391997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5276840169861921169045325 1978815063698220438391997)
      ·
        refine ⟨742055648886832664396999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1978815063698220438391997 742055648886832664396999)
        ·
          refine ⟨1113083473330248996595499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742055648886832664396999 1113083473330248996595499)
          ·
            refine ⟨1669625209995373494893249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113083473330248996595499 1669625209995373494893249)
            ·
              refine ⟨1252218907496530121169937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669625209995373494893249 1252218907496530121169937)
              ·
                refine ⟨939164180622397590877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252218907496530121169937 939164180622397590877453)
                ·
                  refine ⟨352186567733399096579045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939164180622397590877453 352186567733399096579045)
                  ·
                    refine ⟨66034981450012330608571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352186567733399096579045 66034981450012330608571)
                    ·
                      rfl

theorem cell22_192904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_192904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192904 prefixEnd_192904 := by exact prefixLift 192904
  have htrace : WordTrace (prefixWord ++ tailWord_192904) baseStart_192904 baseEnd_192904 := by
    simpa [prefixWord, tailWord_192904, baseEnd_192904] using wordTrace_append hprefix tailTrace_192904
  have hstable : (prefixWord ++ tailWord_192904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192904).length < 2 ^ (prefixWord ++ tailWord_192904).sum := by decide
  have hdescent : baseEnd_192904 < baseStart_192904 := by decide
  rcases family_descends (prefixWord ++ tailWord_192904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192951 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 2, 3]
def baseStart_192951 : Nat := 118140960795 + 192951 * 2 ^ 59
def prefixEnd_192951 : Nat := 4983230072969 + 3 ^ 40 * 192951 * 2
def baseEnd_192951 : Nat := 66051070510519874683427

theorem tailTrace_192951 : CollatzResearch.WordTrace tailWord_192951 prefixEnd_192951 66051070510519874683427 := by
  unfold tailWord_192951
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037501123978955252354707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4691667415985970168236471 7037501123978955252354707)
  ·
    refine ⟨10556251685968432878532061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7037501123978955252354707 10556251685968432878532061)
    ·
      refine ⟨3958594382238162329449523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10556251685968432878532061 3958594382238162329449523)
      ·
        refine ⟨5937891573357243494174285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958594382238162329449523 5937891573357243494174285)
        ·
          refine ⟨2226709340008966310315357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5937891573357243494174285 2226709340008966310315357)
          ·
            refine ⟨835016002503362366368259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2226709340008966310315357 835016002503362366368259)
            ·
              refine ⟨1252524003755043549552389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835016002503362366368259 1252524003755043549552389)
              ·
                refine ⟨234848250704070665541073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1252524003755043549552389 234848250704070665541073)
                ·
                  refine ⟨176136188028052999155805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234848250704070665541073 176136188028052999155805)
                  ·
                    refine ⟨66051070510519874683427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 176136188028052999155805 66051070510519874683427)
                    ·
                      rfl

theorem cell22_192951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_192951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192951 prefixEnd_192951 := by exact prefixLift 192951
  have htrace : WordTrace (prefixWord ++ tailWord_192951) baseStart_192951 baseEnd_192951 := by
    simpa [prefixWord, tailWord_192951, baseEnd_192951] using wordTrace_append hprefix tailTrace_192951
  have hstable : (prefixWord ++ tailWord_192951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192951).length < 2 ^ (prefixWord ++ tailWord_192951).sum := by decide
  have hdescent : baseEnd_192951 < baseStart_192951 := by decide
  rcases family_descends (prefixWord ++ tailWord_192951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192953 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 4]
def baseStart_192953 : Nat := 118140960795 + 192953 * 2 ^ 59
def prefixEnd_192953 : Nat := 4983230072969 + 3 ^ 40 * 192953 * 2
def baseEnd_192953 : Nat := 22017251717130845377807

theorem tailTrace_192953 : CollatzResearch.WordTrace tailWord_192953 prefixEnd_192953 22017251717130845377807 := by
  unfold tailWord_192953
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037574069971709593927513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4691716046647806395951675 7037574069971709593927513)
  ·
    refine ⟨5278180552478782195445635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7037574069971709593927513 5278180552478782195445635)
    ·
      refine ⟨7917270828718173293168453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278180552478782195445635 7917270828718173293168453)
      ·
        refine ⟨1484488280384657492469085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7917270828718173293168453 1484488280384657492469085)
        ·
          refine ⟨556683105144246559675907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1484488280384657492469085 556683105144246559675907)
          ·
            refine ⟨835024657716369839513861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556683105144246559675907 835024657716369839513861)
            ·
              refine ⟨156567123321819344908849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 835024657716369839513861 156567123321819344908849)
              ·
                refine ⟨117425342491364508681637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156567123321819344908849 117425342491364508681637)
                ·
                  refine ⟨22017251717130845377807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117425342491364508681637 22017251717130845377807)
                  ·
                    rfl

theorem cell22_192953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_192953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192953 prefixEnd_192953 := by exact prefixLift 192953
  have htrace : WordTrace (prefixWord ++ tailWord_192953) baseStart_192953 baseEnd_192953 := by
    simpa [prefixWord, tailWord_192953, baseEnd_192953] using wordTrace_append hprefix tailTrace_192953
  have hstable : (prefixWord ++ tailWord_192953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192953).length < 2 ^ (prefixWord ++ tailWord_192953).sum := by decide
  have hdescent : baseEnd_192953 < baseStart_192953 := by decide
  rcases family_descends (prefixWord ++ tailWord_192953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192981 : List Nat := [1, 3, 2, 3, 1, 3, 3, 6]
def baseStart_192981 : Nat := 118140960795 + 192981 * 2 ^ 59
def prefixEnd_192981 : Nat := 4983230072969 + 3 ^ 40 * 192981 * 2
def baseEnd_192981 : Nat := 7340148902623310714815

theorem tailTrace_192981 : CollatzResearch.WordTrace tailWord_192981 prefixEnd_192981 7340148902623310714815 := by
  unfold tailWord_192981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7038595313870270375946797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4692396875913513583964531 7038595313870270375946797)
  ·
    refine ⟨2639473242701351390980049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7038595313870270375946797 2639473242701351390980049)
    ·
      refine ⟨1979604932026013543235037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2639473242701351390980049 1979604932026013543235037)
      ·
        refine ⟨742351849509755078713139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1979604932026013543235037 742351849509755078713139)
        ·
          refine ⟨1113527774264632618069709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742351849509755078713139 1113527774264632618069709)
          ·
            refine ⟨417572915349237231776141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1113527774264632618069709 417572915349237231776141)
            ·
              refine ⟨156589843255963961916053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417572915349237231776141 156589843255963961916053)
              ·
                refine ⟨7340148902623310714815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156589843255963961916053 7340148902623310714815)
                ·
                  rfl

theorem cell22_192981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 6].length) (baseStart_192981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_192981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_192981 prefixEnd_192981 := by exact prefixLift 192981
  have htrace : WordTrace (prefixWord ++ tailWord_192981) baseStart_192981 baseEnd_192981 := by
    simpa [prefixWord, tailWord_192981, baseEnd_192981] using wordTrace_append hprefix tailTrace_192981
  have hstable : (prefixWord ++ tailWord_192981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192981).length < 2 ^ (prefixWord ++ tailWord_192981).sum := by decide
  have hdescent : baseEnd_192981 < baseStart_192981 := by decide
  rcases family_descends (prefixWord ++ tailWord_192981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193009 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 7]
def baseStart_193009 : Nat := 118140960795 + 193009 * 2 ^ 59
def prefixEnd_193009 : Nat := 4983230072969 + 3 ^ 40 * 193009 * 2
def baseEnd_193009 : Nat := 22023641698609018911083

theorem tailTrace_193009 : CollatzResearch.WordTrace tailWord_193009 prefixEnd_193009 22023641698609018911083 := by
  unfold tailWord_193009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7039616557768831157966081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4693077705179220771977387 7039616557768831157966081)
  ·
    refine ⟨5279712418326623368474561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7039616557768831157966081 5279712418326623368474561)
    ·
      refine ⟨3959784313744967526355921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5279712418326623368474561 3959784313744967526355921)
      ·
        refine ⟨2969838235308725644766941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3959784313744967526355921 2969838235308725644766941)
        ·
          refine ⟨1113689338240772116787603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2969838235308725644766941 1113689338240772116787603)
          ·
            refine ⟨1670534007361158175181405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113689338240772116787603 1670534007361158175181405)
            ·
              refine ⟨626450252760434315693027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670534007361158175181405 626450252760434315693027)
              ·
                refine ⟨939675379140651473539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626450252760434315693027 939675379140651473539541)
                ·
                  refine ⟨22023641698609018911083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 939675379140651473539541 22023641698609018911083)
                  ·
                    rfl

theorem cell22_193009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_193009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193009 prefixEnd_193009 := by exact prefixLift 193009
  have htrace : WordTrace (prefixWord ++ tailWord_193009) baseStart_193009 baseEnd_193009 := by
    simpa [prefixWord, tailWord_193009, baseEnd_193009] using wordTrace_append hprefix tailTrace_193009
  have hstable : (prefixWord ++ tailWord_193009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193009).length < 2 ^ (prefixWord ++ tailWord_193009).sum := by decide
  have hdescent : baseEnd_193009 < baseStart_193009 := by decide
  rcases family_descends (prefixWord ++ tailWord_193009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193099 : List Nat := [1, 1, 1, 1, 3, 1, 6, 8]
def baseStart_193099 : Nat := 118140960795 + 193099 * 2 ^ 59
def prefixEnd_193099 : Nat := 4983230072969 + 3 ^ 40 * 193099 * 2
def baseEnd_193099 : Nat := 7344637103899646886997

theorem tailTrace_193099 : CollatzResearch.WordTrace tailWord_193099 prefixEnd_193099 7344637103899646886997 := by
  unfold tailWord_193099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042899127442776528742351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4695266084961851019161567 7042899127442776528742351)
  ·
    refine ⟨10564348691164164793113527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7042899127442776528742351 10564348691164164793113527)
    ·
      refine ⟨15846523036746247189670291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10564348691164164793113527 15846523036746247189670291)
      ·
        refine ⟨23769784555119370784505437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846523036746247189670291 23769784555119370784505437)
        ·
          refine ⟨8913669208169764044189539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23769784555119370784505437 8913669208169764044189539)
          ·
            refine ⟨13370503812254646066284309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913669208169764044189539 13370503812254646066284309)
            ·
              refine ⟨626742366199436534357077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13370503812254646066284309 626742366199436534357077)
              ·
                refine ⟨7344637103899646886997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 626742366199436534357077 7344637103899646886997)
                ·
                  rfl

theorem cell22_193099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 8].length) (baseStart_193099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193099 prefixEnd_193099 := by exact prefixLift 193099
  have htrace : WordTrace (prefixWord ++ tailWord_193099) baseStart_193099 baseEnd_193099 := by
    simpa [prefixWord, tailWord_193099, baseEnd_193099] using wordTrace_append hprefix tailTrace_193099
  have hstable : (prefixWord ++ tailWord_193099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193099).length < 2 ^ (prefixWord ++ tailWord_193099).sum := by decide
  have hdescent : baseEnd_193099 < baseStart_193099 := by decide
  rcases family_descends (prefixWord ++ tailWord_193099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193116 : List Nat := [2, 2, 4, 1, 3, 10]
def baseStart_193116 : Nat := 118140960795 + 193116 * 2 ^ 59
def prefixEnd_193116 : Nat := 4983230072969 + 3 ^ 40 * 193116 * 2
def baseEnd_193116 : Nat := 816142634352030176641

theorem tailTrace_193116 : CollatzResearch.WordTrace tailWord_193116 prefixEnd_193116 816142634352030176641 := by
  unfold tailWord_193116
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521759584190594216055601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4695679445587458954740801 3521759584190594216055601)
  ·
    refine ⟨2641319688142945662041701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3521759584190594216055601 2641319688142945662041701)
    ·
      refine ⟨495247441526802311632819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2641319688142945662041701 495247441526802311632819)
      ·
        refine ⟨742871162290203467449229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495247441526802311632819 742871162290203467449229)
        ·
          refine ⟨278576685858826300293461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742871162290203467449229 278576685858826300293461)
          ·
            refine ⟨816142634352030176641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 278576685858826300293461 816142634352030176641)
            ·
              rfl

theorem cell22_193116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 10].length) (baseStart_193116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193116 prefixEnd_193116 := by exact prefixLift 193116
  have htrace : WordTrace (prefixWord ++ tailWord_193116) baseStart_193116 baseEnd_193116 := by
    simpa [prefixWord, tailWord_193116, baseEnd_193116] using wordTrace_append hprefix tailTrace_193116
  have hstable : (prefixWord ++ tailWord_193116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193116).length < 2 ^ (prefixWord ++ tailWord_193116).sum := by decide
  have hdescent : baseEnd_193116 < baseStart_193116 := by decide
  rcases family_descends (prefixWord ++ tailWord_193116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193122 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_193122 : Nat := 118140960795 + 193122 * 2 ^ 59
def prefixEnd_193122 : Nat := 4983230072969 + 3 ^ 40 * 193122 * 2
def baseEnd_193122 : Nat := 22036535768377476219301

theorem tailTrace_193122 : CollatzResearch.WordTrace tailWord_193122 prefixEnd_193122 22036535768377476219301 := by
  unfold tailWord_193122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760934501589862864207405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4695825337572967637886413 1760934501589862864207405)
  ·
    refine ⟨660350438096198574077777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1760934501589862864207405 660350438096198574077777)
    ·
      refine ⟨495262828572148930558333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660350438096198574077777 495262828572148930558333)
      ·
        refine ⟨185723560714555848959375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495262828572148930558333 185723560714555848959375)
        ·
          refine ⟨278585341071833773439063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185723560714555848959375 278585341071833773439063)
          ·
            refine ⟨417878011607750660158595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278585341071833773439063 417878011607750660158595)
            ·
              refine ⟨626817017411625990237893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417878011607750660158595 626817017411625990237893)
              ·
                refine ⟨117528190764679873169605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626817017411625990237893 117528190764679873169605)
                ·
                  refine ⟨22036535768377476219301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117528190764679873169605 22036535768377476219301)
                  ·
                    rfl

theorem cell22_193122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_193122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193122 prefixEnd_193122 := by exact prefixLift 193122
  have htrace : WordTrace (prefixWord ++ tailWord_193122) baseStart_193122 baseEnd_193122 := by
    simpa [prefixWord, tailWord_193122, baseEnd_193122] using wordTrace_append hprefix tailTrace_193122
  have hstable : (prefixWord ++ tailWord_193122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193122).length < 2 ^ (prefixWord ++ tailWord_193122).sum := by decide
  have hdescent : baseEnd_193122 < baseStart_193122 := by decide
  rcases family_descends (prefixWord ++ tailWord_193122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193133 : List Nat := [1, 5, 1, 1, 3, 3, 1, 7]
def baseStart_193133 : Nat := 118140960795 + 193133 * 2 ^ 59
def prefixEnd_193133 : Nat := 4983230072969 + 3 ^ 40 * 193133 * 2
def baseEnd_193133 : Nat := 7345930314436896292541

theorem tailTrace_193133 : CollatzResearch.WordTrace tailWord_193133 prefixEnd_193133 7345930314436896292541 := by
  unfold tailWord_193133
  simp only [CollatzResearch.WordTrace]
  refine ⟨7044139209319600335480053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4696092806213066890320035 7044139209319600335480053)
  ·
    refine ⟨660388050873712531451255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7044139209319600335480053 660388050873712531451255)
    ·
      refine ⟨990582076310568797176883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660388050873712531451255 990582076310568797176883)
      ·
        refine ⟨1485873114465853195765325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990582076310568797176883 1485873114465853195765325)
        ·
          refine ⟨557202417924694948411997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1485873114465853195765325 557202417924694948411997)
          ·
            refine ⟨208950906721760605654499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557202417924694948411997 208950906721760605654499)
            ·
              refine ⟨313426360082640908481749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208950906721760605654499 313426360082640908481749)
              ·
                refine ⟨7345930314436896292541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 313426360082640908481749 7345930314436896292541)
                ·
                  rfl

theorem cell22_193133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 7].length) (baseStart_193133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193133 prefixEnd_193133 := by exact prefixLift 193133
  have htrace : WordTrace (prefixWord ++ tailWord_193133) baseStart_193133 baseEnd_193133 := by
    simpa [prefixWord, tailWord_193133, baseEnd_193133] using wordTrace_append hprefix tailTrace_193133
  have hstable : (prefixWord ++ tailWord_193133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193133).length < 2 ^ (prefixWord ++ tailWord_193133).sum := by decide
  have hdescent : baseEnd_193133 < baseStart_193133 := by decide
  rcases family_descends (prefixWord ++ tailWord_193133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193176 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_193176 : Nat := 118140960795 + 193176 * 2 ^ 59
def prefixEnd_193176 : Nat := 4983230072969 + 3 ^ 40 * 193176 * 2
def baseEnd_193176 : Nat := 66128092608694287807737

theorem tailTrace_193176 : CollatzResearch.WordTrace tailWord_193176 prefixEnd_193176 66128092608694287807737 := by
  unfold tailWord_193176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522853774081909339647691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4697138365442545786196921 3522853774081909339647691)
  ·
    refine ⟨5284280661122864009471537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3522853774081909339647691 5284280661122864009471537)
    ·
      refine ⟨3963210495842148007103653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5284280661122864009471537 3963210495842148007103653)
      ·
        refine ⟨743101967970402751331935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3963210495842148007103653 743101967970402751331935)
        ·
          refine ⟨1114652951955604126997903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743101967970402751331935 1114652951955604126997903)
          ·
            refine ⟨1671979427933406190496855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114652951955604126997903 1671979427933406190496855)
            ·
              refine ⟨2507969141900109285745283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671979427933406190496855 2507969141900109285745283)
              ·
                refine ⟨3761953712850163928617925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507969141900109285745283 3761953712850163928617925)
                ·
                  refine ⟨705366321159405736615861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3761953712850163928617925 705366321159405736615861)
                  ·
                    refine ⟨66128092608694287807737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 705366321159405736615861 66128092608694287807737)
                    ·
                      rfl

theorem cell22_193176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_193176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193176 prefixEnd_193176 := by exact prefixLift 193176
  have htrace : WordTrace (prefixWord ++ tailWord_193176) baseStart_193176 baseEnd_193176 := by
    simpa [prefixWord, tailWord_193176, baseEnd_193176] using wordTrace_append hprefix tailTrace_193176
  have hstable : (prefixWord ++ tailWord_193176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193176).length < 2 ^ (prefixWord ++ tailWord_193176).sum := by decide
  have hdescent : baseEnd_193176 < baseStart_193176 := by decide
  rcases family_descends (prefixWord ++ tailWord_193176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193182 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_193182 : Nat := 118140960795 + 193182 * 2 ^ 59
def prefixEnd_193182 : Nat := 4983230072969 + 3 ^ 40 * 193182 * 2
def baseEnd_193182 : Nat := 66130146531312272157719

theorem tailTrace_193182 : CollatzResearch.WordTrace tailWord_193182 prefixEnd_193182 66130146531312272157719 := by
  unfold tailWord_193182
  simp only [CollatzResearch.WordTrace]
  refine ⟨880740798267760213001725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4697284257428054469342533 880740798267760213001725)
  ·
    refine ⟨330277799350410079875647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 880740798267760213001725 330277799350410079875647)
    ·
      refine ⟨495416699025615119813471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330277799350410079875647 495416699025615119813471)
      ·
        refine ⟨743125048538422679720207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495416699025615119813471 743125048538422679720207)
        ·
          refine ⟨1114687572807634019580311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743125048538422679720207 1114687572807634019580311)
          ·
            refine ⟨1672031359211451029370467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114687572807634019580311 1672031359211451029370467)
            ·
              refine ⟨2508047038817176544055701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672031359211451029370467 2508047038817176544055701)
              ·
                refine ⟨117564704944555150502611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2508047038817176544055701 117564704944555150502611)
                ·
                  refine ⟨176347057416832725753917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117564704944555150502611 176347057416832725753917)
                  ·
                    refine ⟨66130146531312272157719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 176347057416832725753917 66130146531312272157719)
                    ·
                      rfl

theorem cell22_193182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_193182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193182 prefixEnd_193182 := by exact prefixLift 193182
  have htrace : WordTrace (prefixWord ++ tailWord_193182) baseStart_193182 baseEnd_193182 := by
    simpa [prefixWord, tailWord_193182, baseEnd_193182] using wordTrace_append hprefix tailTrace_193182
  have hstable : (prefixWord ++ tailWord_193182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193182).length < 2 ^ (prefixWord ++ tailWord_193182).sum := by decide
  have hdescent : baseEnd_193182 < baseStart_193182 := by decide
  rcases family_descends (prefixWord ++ tailWord_193182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193223 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 4]
def baseStart_193223 : Nat := 118140960795 + 193223 * 2 ^ 59
def prefixEnd_193223 : Nat := 4983230072969 + 3 ^ 40 * 193223 * 2
def baseEnd_193223 : Nat := 22048060556400610627531

theorem tailTrace_193223 : CollatzResearch.WordTrace tailWord_193223 prefixEnd_193223 22048060556400610627531 := by
  unfold tailWord_193223
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047421778993545706256323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4698281185995697137504215 7047421778993545706256323)
  ·
    refine ⟨10571132668490318559384485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047421778993545706256323 10571132668490318559384485)
    ·
      refine ⟨1982087375341934729884591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10571132668490318559384485 1982087375341934729884591)
      ·
        refine ⟨2973131063012902094826887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982087375341934729884591 2973131063012902094826887)
        ·
          refine ⟨4459696594519353142240331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973131063012902094826887 4459696594519353142240331)
          ·
            refine ⟨6689544891779029713360497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459696594519353142240331 6689544891779029713360497)
            ·
              refine ⟨5017158668834272285020373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689544891779029713360497 5017158668834272285020373)
              ·
                refine ⟨117589656300803256680165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5017158668834272285020373 117589656300803256680165)
                ·
                  refine ⟨22048060556400610627531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117589656300803256680165 22048060556400610627531)
                  ·
                    rfl

theorem cell22_193223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 4].length) (baseStart_193223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193223 prefixEnd_193223 := by exact prefixLift 193223
  have htrace : WordTrace (prefixWord ++ tailWord_193223) baseStart_193223 baseEnd_193223 := by
    simpa [prefixWord, tailWord_193223, baseEnd_193223] using wordTrace_append hprefix tailTrace_193223
  have hstable : (prefixWord ++ tailWord_193223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193223).length < 2 ^ (prefixWord ++ tailWord_193223).sum := by decide
  have hdescent : baseEnd_193223 < baseStart_193223 := by decide
  rcases family_descends (prefixWord ++ tailWord_193223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193270 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_193270 : Nat := 118140960795 + 193270 * 2 ^ 59
def prefixEnd_193270 : Nat := 4983230072969 + 3 ^ 40 * 193270 * 2
def baseEnd_193270 : Nat := 66160270729709375957449

theorem tailTrace_193270 : CollatzResearch.WordTrace tailWord_193270 prefixEnd_193270 66160270729709375957449 := by
  unfold tailWord_193270
  simp only [CollatzResearch.WordTrace]
  refine ⟨440571000613954545826079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4699424006548848488811509 440571000613954545826079)
  ·
    refine ⟨660856500920931818739119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440571000613954545826079 660856500920931818739119)
    ·
      refine ⟨991284751381397728108679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660856500920931818739119 991284751381397728108679)
      ·
        refine ⟨1486927127072096592163019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991284751381397728108679 1486927127072096592163019)
        ·
          refine ⟨2230390690608144888244529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486927127072096592163019 2230390690608144888244529)
          ·
            refine ⟨1672793017956108666183397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230390690608144888244529 1672793017956108666183397)
            ·
              refine ⟨313648690866770374909387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1672793017956108666183397 313648690866770374909387)
              ·
                refine ⟨470473036300155562364081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313648690866770374909387 470473036300155562364081)
                ·
                  refine ⟨352854777225116671773061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470473036300155562364081 352854777225116671773061)
                  ·
                    refine ⟨66160270729709375957449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352854777225116671773061 66160270729709375957449)
                    ·
                      rfl

theorem cell22_193270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_193270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193270 prefixEnd_193270 := by exact prefixLift 193270
  have htrace : WordTrace (prefixWord ++ tailWord_193270) baseStart_193270 baseEnd_193270 := by
    simpa [prefixWord, tailWord_193270, baseEnd_193270] using wordTrace_append hprefix tailTrace_193270
  have hstable : (prefixWord ++ tailWord_193270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193270).length < 2 ^ (prefixWord ++ tailWord_193270).sum := by decide
  have hdescent : baseEnd_193270 < baseStart_193270 := by decide
  rcases family_descends (prefixWord ++ tailWord_193270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193313 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 5]
def baseStart_193313 : Nat := 118140960795 + 193313 * 2 ^ 59
def prefixEnd_193313 : Nat := 4983230072969 + 3 ^ 40 * 193313 * 2
def baseEnd_193313 : Nat := 22058330169490532377439

theorem tailTrace_193313 : CollatzResearch.WordTrace tailWord_193313 prefixEnd_193313 22058330169490532377439 := by
  unfold tailWord_193313
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050704348667491077032593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700469565778327384688395 7050704348667491077032593)
  ·
    refine ⟨5288028261500618307774445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7050704348667491077032593 5288028261500618307774445)
    ·
      refine ⟨1983010598062731865415417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5288028261500618307774445 1983010598062731865415417)
      ·
        refine ⟨1487257948547048899061563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983010598062731865415417 1487257948547048899061563)
        ·
          refine ⟨2230886922820573348592345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487257948547048899061563 2230886922820573348592345)
          ·
            refine ⟨1673165192115430011444259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230886922820573348592345 1673165192115430011444259)
            ·
              refine ⟨2509747788173145017166389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673165192115430011444259 2509747788173145017166389)
              ·
                refine ⟨235288855141232345359349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2509747788173145017166389 235288855141232345359349)
                ·
                  refine ⟨22058330169490532377439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235288855141232345359349 22058330169490532377439)
                  ·
                    rfl

theorem cell22_193313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_193313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193313 prefixEnd_193313 := by exact prefixLift 193313
  have htrace : WordTrace (prefixWord ++ tailWord_193313) baseStart_193313 baseEnd_193313 := by
    simpa [prefixWord, tailWord_193313, baseEnd_193313] using wordTrace_append hprefix tailTrace_193313
  have hstable : (prefixWord ++ tailWord_193313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193313).length < 2 ^ (prefixWord ++ tailWord_193313).sum := by decide
  have hdescent : baseEnd_193313 < baseStart_193313 := by decide
  rcases family_descends (prefixWord ++ tailWord_193313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193388 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_193388 : Nat := 118140960795 + 193388 * 2 ^ 59
def prefixEnd_193388 : Nat := 4983230072969 + 3 ^ 40 * 193388 * 2
def baseEnd_193388 : Nat := 66200664541196401507087

theorem tailTrace_193388 : CollatzResearch.WordTrace tailWord_193388 prefixEnd_193388 66200664541196401507087 := by
  unfold tailWord_193388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526719911697889443006409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4702293215597185924008545 3526719911697889443006409)
  ·
    refine ⟨2645039933773417082254807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3526719911697889443006409 2645039933773417082254807)
    ·
      refine ⟨3967559900660125623382211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645039933773417082254807 3967559900660125623382211)
      ·
        refine ⟨5951339850990188435073317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3967559900660125623382211 5951339850990188435073317)
        ·
          refine ⟨1115876222060660331576247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5951339850990188435073317 1115876222060660331576247)
          ·
            refine ⟨1673814333090990497364371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115876222060660331576247 1673814333090990497364371)
            ·
              refine ⟨2510721499636485746046557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673814333090990497364371 2510721499636485746046557)
              ·
                refine ⟨941520562363682154767459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510721499636485746046557 941520562363682154767459)
                ·
                  refine ⟨1412280843545523232151189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941520562363682154767459 1412280843545523232151189)
                  ·
                    refine ⟨66200664541196401507087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1412280843545523232151189 66200664541196401507087)
                    ·
                      rfl

theorem cell22_193388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_193388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193388 prefixEnd_193388 := by exact prefixLift 193388
  have htrace : WordTrace (prefixWord ++ tailWord_193388) baseStart_193388 baseEnd_193388 := by
    simpa [prefixWord, tailWord_193388, baseEnd_193388] using wordTrace_append hprefix tailTrace_193388
  have hstable : (prefixWord ++ tailWord_193388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193388).length < 2 ^ (prefixWord ++ tailWord_193388).sum := by decide
  have hdescent : baseEnd_193388 < baseStart_193388 := by decide
  rcases family_descends (prefixWord ++ tailWord_193388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193465 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 5]
def baseStart_193465 : Nat := 118140960795 + 193465 * 2 ^ 59
def prefixEnd_193465 : Nat := 4983230072969 + 3 ^ 40 * 193465 * 2
def baseEnd_193465 : Nat := 22075674404931289110617

theorem tailTrace_193465 : CollatzResearch.WordTrace tailWord_193465 prefixEnd_193465 22075674404931289110617 := by
  unfold tailWord_193465
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056248244116821036565849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4704165496077880691043899 7056248244116821036565849)
  ·
    refine ⟨5292186183087615777424387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7056248244116821036565849 5292186183087615777424387)
    ·
      refine ⟨7938279274631423666136581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292186183087615777424387 7938279274631423666136581)
      ·
        refine ⟨1488427363993391937400609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7938279274631423666136581 1488427363993391937400609)
        ·
          refine ⟨1116320522995043953050457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488427363993391937400609 1116320522995043953050457)
          ·
            refine ⟨837240392246282964787843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116320522995043953050457 837240392246282964787843)
            ·
              refine ⟨1255860588369424447181765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837240392246282964787843 1255860588369424447181765)
              ·
                refine ⟨235473860319267083846581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1255860588369424447181765 235473860319267083846581)
                ·
                  refine ⟨22075674404931289110617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235473860319267083846581 22075674404931289110617)
                  ·
                    rfl

theorem cell22_193465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_193465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193465 prefixEnd_193465 := by exact prefixLift 193465
  have htrace : WordTrace (prefixWord ++ tailWord_193465) baseStart_193465 baseEnd_193465 := by
    simpa [prefixWord, tailWord_193465, baseEnd_193465] using wordTrace_append hprefix tailTrace_193465
  have hstable : (prefixWord ++ tailWord_193465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193465).length < 2 ^ (prefixWord ++ tailWord_193465).sum := by decide
  have hdescent : baseEnd_193465 < baseStart_193465 := by decide
  rcases family_descends (prefixWord ++ tailWord_193465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193572 : List Nat := [2, 3, 1, 4, 1, 3, 8]
def baseStart_193572 : Nat := 118140960795 + 193572 * 2 ^ 59
def prefixEnd_193572 : Nat := 4983230072969 + 3 ^ 40 * 193572 * 2
def baseEnd_193572 : Nat := 2454209314869676107649

theorem tailTrace_193572 : CollatzResearch.WordTrace tailWord_193572 prefixEnd_193572 2454209314869676107649 := by
  unfold tailWord_193572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530075427364589155355485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4706767236486118873807313 3530075427364589155355485)
  ·
    refine ⟨1323778285261720933258307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3530075427364589155355485 1323778285261720933258307)
    ·
      refine ⟨1985667427892581399887461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323778285261720933258307 1985667427892581399887461)
      ·
        refine ⟨372312642729859012478899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1985667427892581399887461 372312642729859012478899)
        ·
          refine ⟨558468964094788518718349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372312642729859012478899 558468964094788518718349)
          ·
            refine ⟨209425861535545694519381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 558468964094788518718349 209425861535545694519381)
            ·
              refine ⟨2454209314869676107649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 209425861535545694519381 2454209314869676107649)
              ·
                rfl

theorem cell22_193572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 8].length) (baseStart_193572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193572 prefixEnd_193572 := by exact prefixLift 193572
  have htrace : WordTrace (prefixWord ++ tailWord_193572) baseStart_193572 baseEnd_193572 := by
    simpa [prefixWord, tailWord_193572, baseEnd_193572] using wordTrace_append hprefix tailTrace_193572
  have hstable : (prefixWord ++ tailWord_193572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193572).length < 2 ^ (prefixWord ++ tailWord_193572).sum := by decide
  have hdescent : baseEnd_193572 < baseStart_193572 := by decide
  rcases family_descends (prefixWord ++ tailWord_193572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193585 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_193585 : Nat := 118140960795 + 193585 * 2 ^ 59
def prefixEnd_193585 : Nat := 4983230072969 + 3 ^ 40 * 193585 * 2
def baseEnd_193585 : Nat := 66268101667153554331483

theorem tailTrace_193585 : CollatzResearch.WordTrace tailWord_193585 prefixEnd_193585 66268101667153554331483 := by
  unfold tailWord_193585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7060625003682081530934209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4707083335788054353956139 7060625003682081530934209)
  ·
    refine ⟨5295468752761561148200657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7060625003682081530934209 5295468752761561148200657)
    ·
      refine ⟨3971601564571170861150493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5295468752761561148200657 3971601564571170861150493)
      ·
        refine ⟨1489350586714189072931435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3971601564571170861150493 1489350586714189072931435)
        ·
          refine ⟨2234025880071283609397153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489350586714189072931435 2234025880071283609397153)
          ·
            refine ⟨1675519410053462707047865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234025880071283609397153 1675519410053462707047865)
            ·
              refine ⟨1256639557540097030285899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675519410053462707047865 1256639557540097030285899)
              ·
                refine ⟨1884959336310145545428849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256639557540097030285899 1884959336310145545428849)
                ·
                  refine ⟨1413719502232609159071637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884959336310145545428849 1413719502232609159071637)
                  ·
                    refine ⟨66268101667153554331483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1413719502232609159071637 66268101667153554331483)
                    ·
                      rfl

theorem cell22_193585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_193585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193585 prefixEnd_193585 := by exact prefixLift 193585
  have htrace : WordTrace (prefixWord ++ tailWord_193585) baseStart_193585 baseEnd_193585 := by
    simpa [prefixWord, tailWord_193585, baseEnd_193585] using wordTrace_append hprefix tailTrace_193585
  have hstable : (prefixWord ++ tailWord_193585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193585).length < 2 ^ (prefixWord ++ tailWord_193585).sum := by decide
  have hdescent : baseEnd_193585 < baseStart_193585 := by decide
  rcases family_descends (prefixWord ++ tailWord_193585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193634 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_193634 : Nat := 118140960795 + 193634 * 2 ^ 59
def prefixEnd_193634 : Nat := 4983230072969 + 3 ^ 40 * 193634 * 2
def baseEnd_193634 : Nat := 22094958456177919952111

theorem tailTrace_193634 : CollatzResearch.WordTrace tailWord_193634 prefixEnd_193634 22094958456177919952111 := by
  unfold tailWord_193634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765603045126140724866989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4708274787003041932978637 1765603045126140724866989)
  ·
    refine ⟨662101141922302771825121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1765603045126140724866989 662101141922302771825121)
    ·
      refine ⟨496575856441727078868841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 662101141922302771825121 496575856441727078868841)
      ·
        refine ⟨372431892331295309151631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496575856441727078868841 372431892331295309151631)
        ·
          refine ⟨558647838496942963727447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372431892331295309151631 558647838496942963727447)
          ·
            refine ⟨837971757745414445591171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558647838496942963727447 837971757745414445591171)
            ·
              refine ⟨1256957636618121668386757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837971757745414445591171 1256957636618121668386757)
              ·
                refine ⟨235679556865897812822517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1256957636618121668386757 235679556865897812822517)
                ·
                  refine ⟨22094958456177919952111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 235679556865897812822517 22094958456177919952111)
                  ·
                    rfl

theorem cell22_193634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_193634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193634 prefixEnd_193634 := by exact prefixLift 193634
  have htrace : WordTrace (prefixWord ++ tailWord_193634) baseStart_193634 baseEnd_193634 := by
    simpa [prefixWord, tailWord_193634, baseEnd_193634] using wordTrace_append hprefix tailTrace_193634
  have hstable : (prefixWord ++ tailWord_193634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193634).length < 2 ^ (prefixWord ++ tailWord_193634).sum := by decide
  have hdescent : baseEnd_193634 < baseStart_193634 := by decide
  rcases family_descends (prefixWord ++ tailWord_193634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193724 : List Nat := [2, 2, 2, 3, 2, 1, 4, 6]
def baseStart_193724 : Nat := 118140960795 + 193724 * 2 ^ 59
def prefixEnd_193724 : Nat := 4983230072969 + 3 ^ 40 * 193724 * 2
def baseEnd_193724 : Nat := 7368409356422613900673

theorem tailTrace_193724 : CollatzResearch.WordTrace tailWord_193724 prefixEnd_193724 7368409356422613900673 := by
  unfold tailWord_193724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532847375089254135122113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4710463166785672180162817 3532847375089254135122113)
  ·
    refine ⟨2649635531316940601341585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3532847375089254135122113 2649635531316940601341585)
    ·
      refine ⟨1987226648487705451006189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2649635531316940601341585 1987226648487705451006189)
      ·
        refine ⟨745209993182889544127321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1987226648487705451006189 745209993182889544127321)
        ·
          refine ⟨558907494887167158095491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745209993182889544127321 558907494887167158095491)
          ·
            refine ⟨838361242330750737143237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558907494887167158095491 838361242330750737143237)
            ·
              refine ⟨157192732937015763214357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 838361242330750737143237 157192732937015763214357)
              ·
                refine ⟨7368409356422613900673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157192732937015763214357 7368409356422613900673)
                ·
                  rfl

theorem cell22_193724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_193724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193724 prefixEnd_193724 := by exact prefixLift 193724
  have htrace : WordTrace (prefixWord ++ tailWord_193724) baseStart_193724 baseEnd_193724 := by
    simpa [prefixWord, tailWord_193724, baseEnd_193724] using wordTrace_append hprefix tailTrace_193724
  have hstable : (prefixWord ++ tailWord_193724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193724).length < 2 ^ (prefixWord ++ tailWord_193724).sum := by decide
  have hdescent : baseEnd_193724 < baseStart_193724 := by decide
  rcases family_descends (prefixWord ++ tailWord_193724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193829 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_193829 : Nat := 118140960795 + 193829 * 2 ^ 59
def prefixEnd_193829 : Nat := 4983230072969 + 3 ^ 40 * 193829 * 2
def baseEnd_193829 : Nat := 66351627853618251230735

theorem tailTrace_193829 : CollatzResearch.WordTrace tailWord_193829 prefixEnd_193829 66351627853618251230735 := by
  unfold tailWord_193829
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069524414798111202816541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4713016276532074135211027 7069524414798111202816541)
  ·
    refine ⟨2651071655549291701056203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7069524414798111202816541 2651071655549291701056203)
    ·
      refine ⟨3976607483323937551584305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651071655549291701056203 3976607483323937551584305)
      ·
        refine ⟨2982455612492953163688229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3976607483323937551584305 2982455612492953163688229)
        ·
          refine ⟨559210427342428718191543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2982455612492953163688229 559210427342428718191543)
          ·
            refine ⟨838815641013643077287315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559210427342428718191543 838815641013643077287315)
            ·
              refine ⟨1258223461520464615930973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838815641013643077287315 1258223461520464615930973)
              ·
                refine ⟨471833798070174230974115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258223461520464615930973 471833798070174230974115)
                ·
                  refine ⟨707750697105261346461173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471833798070174230974115 707750697105261346461173)
                  ·
                    refine ⟨66351627853618251230735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 707750697105261346461173 66351627853618251230735)
                    ·
                      rfl

theorem cell22_193829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_193829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193829 prefixEnd_193829 := by exact prefixLift 193829
  have htrace : WordTrace (prefixWord ++ tailWord_193829) baseStart_193829 baseEnd_193829 := by
    simpa [prefixWord, tailWord_193829, baseEnd_193829] using wordTrace_append hprefix tailTrace_193829
  have hstable : (prefixWord ++ tailWord_193829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193829).length < 2 ^ (prefixWord ++ tailWord_193829).sum := by decide
  have hdescent : baseEnd_193829 < baseStart_193829 := by decide
  rcases family_descends (prefixWord ++ tailWord_193829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193863 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 2, 3]
def baseStart_193863 : Nat := 118140960795 + 193863 * 2 ^ 59
def prefixEnd_193863 : Nat := 4983230072969 + 3 ^ 40 * 193863 * 2
def baseEnd_193863 : Nat := 66363266748453495880631

theorem tailTrace_193863 : CollatzResearch.WordTrace tailWord_193863 prefixEnd_193863 66363266748453495880631 := by
  unfold tailWord_193863
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070764496674935009554243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4713842997783290006369495 7070764496674935009554243)
  ·
    refine ⟨10606146745012402514331365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070764496674935009554243 10606146745012402514331365)
    ·
      refine ⟨1988652514689825471437131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10606146745012402514331365 1988652514689825471437131)
      ·
        refine ⟨2982978772034738207155697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988652514689825471437131 2982978772034738207155697)
        ·
          refine ⟨2237234079026053655366773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982978772034738207155697 2237234079026053655366773)
          ·
            refine ⟨209740694908692530190635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2237234079026053655366773 209740694908692530190635)
            ·
              refine ⟨314611042363038795285953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209740694908692530190635 314611042363038795285953)
              ·
                refine ⟨235958281772279096464465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314611042363038795285953 235958281772279096464465)
                ·
                  refine ⟨176968711329209322348349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235958281772279096464465 176968711329209322348349)
                  ·
                    refine ⟨66363266748453495880631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 176968711329209322348349 66363266748453495880631)
                    ·
                      rfl

theorem cell22_193863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_193863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193863 prefixEnd_193863 := by exact prefixLift 193863
  have htrace : WordTrace (prefixWord ++ tailWord_193863) baseStart_193863 baseEnd_193863 := by
    simpa [prefixWord, tailWord_193863, baseEnd_193863] using wordTrace_append hprefix tailTrace_193863
  have hstable : (prefixWord ++ tailWord_193863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193863).length < 2 ^ (prefixWord ++ tailWord_193863).sum := by decide
  have hdescent : baseEnd_193863 < baseStart_193863 := by decide
  rcases family_descends (prefixWord ++ tailWord_193863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193891 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 3, 3]
def baseStart_193891 : Nat := 118140960795 + 193891 * 2 ^ 59
def prefixEnd_193891 : Nat := 4983230072969 + 3 ^ 40 * 193891 * 2
def baseEnd_193891 : Nat := 66372851720670756180545

theorem tailTrace_193891 : CollatzResearch.WordTrace tailWord_193891 prefixEnd_193891 66372851720670756180545 := by
  unfold tailWord_193891
  simp only [CollatzResearch.WordTrace]
  refine ⟨7071785740573495791573527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4714523827048997194382351 7071785740573495791573527)
  ·
    refine ⟨10607678610860243687360291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7071785740573495791573527 10607678610860243687360291)
    ·
      refine ⟨15911517916290365531040437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10607678610860243687360291 15911517916290365531040437)
      ·
        refine ⟨1491704804652221768535041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15911517916290365531040437 1491704804652221768535041)
        ·
          refine ⟨1118778603489166326401281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491704804652221768535041 1118778603489166326401281)
          ·
            refine ⟨839083952616874744800961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118778603489166326401281 839083952616874744800961)
            ·
              refine ⟨629312964462656058600721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839083952616874744800961 629312964462656058600721)
              ·
                refine ⟨471984723346992043950541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629312964462656058600721 471984723346992043950541)
                ·
                  refine ⟨176994271255122016481453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471984723346992043950541 176994271255122016481453)
                  ·
                    refine ⟨66372851720670756180545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 176994271255122016481453 66372851720670756180545)
                    ·
                      rfl

theorem cell22_193891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3].length) (baseStart_193891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193891 prefixEnd_193891 := by exact prefixLift 193891
  have htrace : WordTrace (prefixWord ++ tailWord_193891) baseStart_193891 baseEnd_193891 := by
    simpa [prefixWord, tailWord_193891, baseEnd_193891] using wordTrace_append hprefix tailTrace_193891
  have hstable : (prefixWord ++ tailWord_193891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193891).length < 2 ^ (prefixWord ++ tailWord_193891).sum := by decide
  have hdescent : baseEnd_193891 < baseStart_193891 := by decide
  rcases family_descends (prefixWord ++ tailWord_193891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193951 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_193951 : Nat := 118140960795 + 193951 * 2 ^ 59
def prefixEnd_193951 : Nat := 4983230072969 + 3 ^ 40 * 193951 * 2
def baseEnd_193951 : Nat := 66393390946850599680361

theorem tailTrace_193951 : CollatzResearch.WordTrace tailWord_193951 prefixEnd_193951 66393390946850599680361 := by
  unfold tailWord_193951
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073974120356126038757707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4715982746904084025838471 7073974120356126038757707)
  ·
    refine ⟨10610961180534189058136561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7073974120356126038757707 10610961180534189058136561)
    ·
      refine ⟨7958220885400641793602421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10610961180534189058136561 7958220885400641793602421)
      ·
        refine ⟨746083208006310168150227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7958220885400641793602421 746083208006310168150227)
        ·
          refine ⟨1119124812009465252225341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746083208006310168150227 1119124812009465252225341)
          ·
            refine ⟨419671804503549469584503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1119124812009465252225341 419671804503549469584503)
            ·
              refine ⟨629507706755324204376755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419671804503549469584503 629507706755324204376755)
              ·
                refine ⟨944261560132986306565133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629507706755324204376755 944261560132986306565133)
                ·
                  refine ⟨354098085049869864961925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944261560132986306565133 354098085049869864961925)
                  ·
                    refine ⟨66393390946850599680361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354098085049869864961925 66393390946850599680361)
                    ·
                      rfl

theorem cell22_193951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_193951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193951 prefixEnd_193951 := by exact prefixLift 193951
  have htrace : WordTrace (prefixWord ++ tailWord_193951) baseStart_193951 baseEnd_193951 := by
    simpa [prefixWord, tailWord_193951, baseEnd_193951] using wordTrace_append hprefix tailTrace_193951
  have hstable : (prefixWord ++ tailWord_193951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193951).length < 2 ^ (prefixWord ++ tailWord_193951).sum := by decide
  have hdescent : baseEnd_193951 < baseStart_193951 := by decide
  rcases family_descends (prefixWord ++ tailWord_193951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193964 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_193964 : Nat := 118140960795 + 193964 * 2 ^ 59
def prefixEnd_193964 : Nat := 4983230072969 + 3 ^ 40 * 193964 * 2
def baseEnd_193964 : Nat := 66397841112522899105321

theorem tailTrace_193964 : CollatzResearch.WordTrace tailWord_193964 prefixEnd_193964 66397841112522899105321 := by
  unfold tailWord_193964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537224134654514629490473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4716298846206019505987297 3537224134654514629490473)
  ·
    refine ⟨2652918100990885972117855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3537224134654514629490473 2652918100990885972117855)
    ·
      refine ⟨3979377151486328958176783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652918100990885972117855 3979377151486328958176783)
      ·
        refine ⟨5969065727229493437265175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3979377151486328958176783 5969065727229493437265175)
        ·
          refine ⟨8953598590844240155897763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969065727229493437265175 8953598590844240155897763)
          ·
            refine ⟨13430397886266360233846645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8953598590844240155897763 13430397886266360233846645)
            ·
              refine ⟨1259099801837471271923123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13430397886266360233846645 1259099801837471271923123)
              ·
                refine ⟨1888649702756206907884685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259099801837471271923123 1888649702756206907884685)
                ·
                  refine ⟨708243638533577590456757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1888649702756206907884685 708243638533577590456757)
                  ·
                    refine ⟨66397841112522899105321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 708243638533577590456757 66397841112522899105321)
                    ·
                      rfl

theorem cell22_193964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_193964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193964 prefixEnd_193964 := by exact prefixLift 193964
  have htrace : WordTrace (prefixWord ++ tailWord_193964) baseStart_193964 baseEnd_193964 := by
    simpa [prefixWord, tailWord_193964, baseEnd_193964] using wordTrace_append hprefix tailTrace_193964
  have hstable : (prefixWord ++ tailWord_193964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193964).length < 2 ^ (prefixWord ++ tailWord_193964).sum := by decide
  have hdescent : baseEnd_193964 < baseStart_193964 := by decide
  rcases family_descends (prefixWord ++ tailWord_193964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193998 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_193998 : Nat := 118140960795 + 193998 * 2 ^ 59
def prefixEnd_193998 : Nat := 4983230072969 + 3 ^ 40 * 193998 * 2
def baseEnd_193998 : Nat := 66409480007358143755217

theorem tailTrace_193998 : CollatzResearch.WordTrace tailWord_193998 prefixEnd_193998 66409480007358143755217 := by
  unfold tailWord_193998
  simp only [CollatzResearch.WordTrace]
  refine ⟨884461043898231633214831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4717125567457235377145765 884461043898231633214831)
  ·
    refine ⟨1326691565847347449822247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884461043898231633214831 1326691565847347449822247)
    ·
      refine ⟨1990037348771021174733371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326691565847347449822247 1990037348771021174733371)
      ·
        refine ⟨2985056023156531762100057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990037348771021174733371 2985056023156531762100057)
        ·
          refine ⟨2238792017367398821575043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985056023156531762100057 2238792017367398821575043)
          ·
            refine ⟨3358188026051098232362565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238792017367398821575043 3358188026051098232362565)
            ·
              refine ⟨629660254884580918567981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3358188026051098232362565 629660254884580918567981)
              ·
                refine ⟨236122595581717844462993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629660254884580918567981 236122595581717844462993)
                ·
                  refine ⟨177091946686288383347245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236122595581717844462993 177091946686288383347245)
                  ·
                    refine ⟨66409480007358143755217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177091946686288383347245 66409480007358143755217)
                    ·
                      rfl

theorem cell22_193998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_193998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_193998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_193998 prefixEnd_193998 := by exact prefixLift 193998
  have htrace : WordTrace (prefixWord ++ tailWord_193998) baseStart_193998 baseEnd_193998 := by
    simpa [prefixWord, tailWord_193998, baseEnd_193998] using wordTrace_append hprefix tailTrace_193998
  have hstable : (prefixWord ++ tailWord_193998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193998).length < 2 ^ (prefixWord ++ tailWord_193998).sum := by decide
  have hdescent : baseEnd_193998 < baseStart_193998 := by decide
  rcases family_descends (prefixWord ++ tailWord_193998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194013 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_194013 : Nat := 118140960795 + 194013 * 2 ^ 59
def prefixEnd_194013 : Nat := 4983230072969 + 3 ^ 40 * 194013 * 2
def baseEnd_194013 : Nat := 66414614813903104630171

theorem tailTrace_194013 : CollatzResearch.WordTrace tailWord_194013 prefixEnd_194013 66414614813903104630171 := by
  unfold tailWord_194013
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076235446131510627514693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717490297421007085009795 7076235446131510627514693)
  ·
    refine ⟨1326794146149658242659005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7076235446131510627514693 1326794146149658242659005)
    ·
      refine ⟨497547804806121840997127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1326794146149658242659005 497547804806121840997127)
      ·
        refine ⟨746321707209182761495691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497547804806121840997127 746321707209182761495691)
        ·
          refine ⟨1119482560813774142243537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746321707209182761495691 1119482560813774142243537)
          ·
            refine ⟨839611920610330606682653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119482560813774142243537 839611920610330606682653)
            ·
              refine ⟨314854470228873977505995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839611920610330606682653 314854470228873977505995)
              ·
                refine ⟨472281705343310966258993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314854470228873977505995 472281705343310966258993)
                ·
                  refine ⟨354211279007483224694245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472281705343310966258993 354211279007483224694245)
                  ·
                    refine ⟨66414614813903104630171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354211279007483224694245 66414614813903104630171)
                    ·
                      rfl

theorem cell22_194013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_194013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194013 prefixEnd_194013 := by exact prefixLift 194013
  have htrace : WordTrace (prefixWord ++ tailWord_194013) baseStart_194013 baseEnd_194013 := by
    simpa [prefixWord, tailWord_194013, baseEnd_194013] using wordTrace_append hprefix tailTrace_194013
  have hstable : (prefixWord ++ tailWord_194013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194013).length < 2 ^ (prefixWord ++ tailWord_194013).sum := by decide
  have hdescent : baseEnd_194013 < baseStart_194013 := by decide
  rcases family_descends (prefixWord ++ tailWord_194013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194056 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_194056 : Nat := 118140960795 + 194056 * 2 ^ 59
def prefixEnd_194056 : Nat := 4983230072969 + 3 ^ 40 * 194056 * 2
def baseEnd_194056 : Nat := 22143111530888441935013

theorem tailTrace_194056 : CollatzResearch.WordTrace tailWord_194056 prefixEnd_194056 22143111530888441935013 := by
  unfold tailWord_194056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538901892487864485665011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4718535856650485980886681 3538901892487864485665011)
  ·
    refine ⟨5308352838731796728497517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538901892487864485665011 5308352838731796728497517)
    ·
      refine ⟨1990632314524423773186569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5308352838731796728497517 1990632314524423773186569)
      ·
        refine ⟨1492974235893317829889927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990632314524423773186569 1492974235893317829889927)
        ·
          refine ⟨2239461353839976744834891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492974235893317829889927 2239461353839976744834891)
          ·
            refine ⟨3359192030759965117252337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239461353839976744834891 3359192030759965117252337)
            ·
              refine ⟨2519394023069973837939253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359192030759965117252337 2519394023069973837939253)
              ·
                refine ⟨236193189662810047306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2519394023069973837939253 236193189662810047306805)
                ·
                  refine ⟨22143111530888441935013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236193189662810047306805 22143111530888441935013)
                  ·
                    rfl

theorem cell22_194056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_194056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194056 prefixEnd_194056 := by exact prefixLift 194056
  have htrace : WordTrace (prefixWord ++ tailWord_194056) baseStart_194056 baseEnd_194056 := by
    simpa [prefixWord, tailWord_194056, baseEnd_194056] using wordTrace_append hprefix tailTrace_194056
  have hstable : (prefixWord ++ tailWord_194056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194056).length < 2 ^ (prefixWord ++ tailWord_194056).sum := by decide
  have hdescent : baseEnd_194056 < baseStart_194056 := by decide
  rcases family_descends (prefixWord ++ tailWord_194056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194094 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_194094 : Nat := 118140960795 + 194094 * 2 ^ 59
def prefixEnd_194094 : Nat := 4983230072969 + 3 ^ 40 * 194094 * 2
def baseEnd_194094 : Nat := 66442342769245893354923

theorem tailTrace_194094 : CollatzResearch.WordTrace tailWord_194094 prefixEnd_194094 66442342769245893354923 := by
  unfold tailWord_194094
  simp only [CollatzResearch.WordTrace]
  refine ⟨884898719854757682651667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4719459839225374307475557 884898719854757682651667)
  ·
    refine ⟨1327348079782136523977501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884898719854757682651667 1327348079782136523977501)
    ·
      refine ⟨497755529918301196491563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1327348079782136523977501 497755529918301196491563)
      ·
        refine ⟨746633294877451794737345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497755529918301196491563 746633294877451794737345)
        ·
          refine ⟨559974971158088846053009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746633294877451794737345 559974971158088846053009)
          ·
            refine ⟨419981228368566634539757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559974971158088846053009 419981228368566634539757)
            ·
              refine ⟨157492960638212487952409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419981228368566634539757 157492960638212487952409)
              ·
                refine ⟨118119720478659365964307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157492960638212487952409 118119720478659365964307)
                ·
                  refine ⟨177179580717989048946461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118119720478659365964307 177179580717989048946461)
                  ·
                    refine ⟨66442342769245893354923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177179580717989048946461 66442342769245893354923)
                    ·
                      rfl

theorem cell22_194094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_194094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194094 prefixEnd_194094 := by exact prefixLift 194094
  have htrace : WordTrace (prefixWord ++ tailWord_194094) baseStart_194094 baseEnd_194094 := by
    simpa [prefixWord, tailWord_194094, baseEnd_194094] using wordTrace_append hprefix tailTrace_194094
  have hstable : (prefixWord ++ tailWord_194094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194094).length < 2 ^ (prefixWord ++ tailWord_194094).sum := by decide
  have hdescent : baseEnd_194094 < baseStart_194094 := by decide
  rcases family_descends (prefixWord ++ tailWord_194094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194146 : List Nat := [3, 3, 2, 14]
def baseStart_194146 : Nat := 118140960795 + 194146 * 2 ^ 59
def prefixEnd_194146 : Nat := 4983230072969 + 3 ^ 40 * 194146 * 2
def baseEnd_194146 : Nat := 91166177547236064547

theorem tailTrace_194146 : CollatzResearch.WordTrace tailWord_194146 prefixEnd_194146 91166177547236064547 := by
  unfold tailWord_194146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770271588662418585526573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4720724236433116228070861 1770271588662418585526573)
  ·
    refine ⟨663851845748406969572465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1770271588662418585526573 663851845748406969572465)
    ·
      refine ⟨497888884311305227179349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 663851845748406969572465 497888884311305227179349)
      ·
        refine ⟨91166177547236064547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 497888884311305227179349 91166177547236064547)
        ·
          rfl

theorem cell22_194146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 14].length) (baseStart_194146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194146 prefixEnd_194146 := by exact prefixLift 194146
  have htrace : WordTrace (prefixWord ++ tailWord_194146) baseStart_194146 baseEnd_194146 := by
    simpa [prefixWord, tailWord_194146, baseEnd_194146] using wordTrace_append hprefix tailTrace_194146
  have hstable : (prefixWord ++ tailWord_194146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194146).length < 2 ^ (prefixWord ++ tailWord_194146).sum := by decide
  have hdescent : baseEnd_194146 < baseStart_194146 := by decide
  rcases family_descends (prefixWord ++ tailWord_194146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194148 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_194148 : Nat := 118140960795 + 194148 * 2 ^ 59
def prefixEnd_194148 : Nat := 4983230072969 + 3 ^ 40 * 194148 * 2
def baseEnd_194148 : Nat := 66460828072807752504757

theorem tailTrace_194148 : CollatzResearch.WordTrace tailWord_194148 prefixEnd_194148 66460828072807752504757 := by
  unfold tailWord_194148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540579650321214341839549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4720772867094952455786065 3540579650321214341839549)
  ·
    refine ⟨1327717368870455378189831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3540579650321214341839549 1327717368870455378189831)
    ·
      refine ⟨1991576053305683067284747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327717368870455378189831 1991576053305683067284747)
      ·
        refine ⟨2987364079958524600927121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991576053305683067284747 2987364079958524600927121)
        ·
          refine ⟨2240523059968893450695341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2987364079958524600927121 2240523059968893450695341)
          ·
            refine ⟨840196147488335044010753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2240523059968893450695341 840196147488335044010753)
            ·
              refine ⟨630147110616251283008065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840196147488335044010753 630147110616251283008065)
              ·
                refine ⟨472610332962188462256049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630147110616251283008065 472610332962188462256049)
                ·
                  refine ⟨354457749721641346692037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472610332962188462256049 354457749721641346692037)
                  ·
                    refine ⟨66460828072807752504757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354457749721641346692037 66460828072807752504757)
                    ·
                      rfl

theorem cell22_194148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_194148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194148 prefixEnd_194148 := by exact prefixLift 194148
  have htrace : WordTrace (prefixWord ++ tailWord_194148) baseStart_194148 baseEnd_194148 := by
    simpa [prefixWord, tailWord_194148, baseEnd_194148] using wordTrace_append hprefix tailTrace_194148
  have hstable : (prefixWord ++ tailWord_194148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194148).length < 2 ^ (prefixWord ++ tailWord_194148).sum := by decide
  have hdescent : baseEnd_194148 < baseStart_194148 := by decide
  rcases family_descends (prefixWord ++ tailWord_194148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194152 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_194152 : Nat := 118140960795 + 194152 * 2 ^ 59
def prefixEnd_194152 : Nat := 4983230072969 + 3 ^ 40 * 194152 * 2
def baseEnd_194152 : Nat := 22154065784851025134915

theorem tailTrace_194152 : CollatzResearch.WordTrace tailWord_194152 prefixEnd_194152 22154065784851025134915 := by
  unfold tailWord_194152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540652596313968683412355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4720870128418624911216473 3540652596313968683412355)
  ·
    refine ⟨5310978894470953025118533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3540652596313968683412355 5310978894470953025118533)
    ·
      refine ⟨995808542713303692209725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5310978894470953025118533 995808542713303692209725)
      ·
        refine ⟨373428203517488884578647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 995808542713303692209725 373428203517488884578647)
        ·
          refine ⟨560142305276233326867971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373428203517488884578647 560142305276233326867971)
          ·
            refine ⟨840213457914349990301957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560142305276233326867971 840213457914349990301957)
            ·
              refine ⟨157540023358940623181617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 840213457914349990301957 157540023358940623181617)
              ·
                refine ⟨118155017519205467386213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157540023358940623181617 118155017519205467386213)
                ·
                  refine ⟨22154065784851025134915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118155017519205467386213 22154065784851025134915)
                  ·
                    rfl

theorem cell22_194152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_194152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194152 prefixEnd_194152 := by exact prefixLift 194152
  have htrace : WordTrace (prefixWord ++ tailWord_194152) baseStart_194152 baseEnd_194152 := by
    simpa [prefixWord, tailWord_194152, baseEnd_194152] using wordTrace_append hprefix tailTrace_194152
  have hstable : (prefixWord ++ tailWord_194152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194152).length < 2 ^ (prefixWord ++ tailWord_194152).sum := by decide
  have hdescent : baseEnd_194152 < baseStart_194152 := by decide
  rcases family_descends (prefixWord ++ tailWord_194152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194176 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_194176 : Nat := 118140960795 + 194176 * 2 ^ 59
def prefixEnd_194176 : Nat := 4983230072969 + 3 ^ 40 * 194176 * 2
def baseEnd_194176 : Nat := 66470413045025012804671

theorem tailTrace_194176 : CollatzResearch.WordTrace tailWord_194176 prefixEnd_194176 66470413045025012804671 := by
  unfold tailWord_194176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541090272270494732849191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4721453696360659643798921 3541090272270494732849191)
  ·
    refine ⟨5311635408405742099273787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3541090272270494732849191 5311635408405742099273787)
    ·
      refine ⟨7967453112608613148910681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311635408405742099273787 7967453112608613148910681)
      ·
        refine ⟨5975589834456459861683011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7967453112608613148910681 5975589834456459861683011)
        ·
          refine ⟨8963384751684689792524517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975589834456459861683011 8963384751684689792524517)
          ·
            refine ⟨1680634640940879336098347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8963384751684689792524517 1680634640940879336098347)
            ·
              refine ⟨2520951961411319004147521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680634640940879336098347 2520951961411319004147521)
              ·
                refine ⟨1890713971058489253110641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520951961411319004147521 1890713971058489253110641)
                ·
                  refine ⟨1418035478293866939832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890713971058489253110641 1418035478293866939832981)
                  ·
                    refine ⟨66470413045025012804671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1418035478293866939832981 66470413045025012804671)
                    ·
                      rfl

theorem cell22_194176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_194176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194176 prefixEnd_194176 := by exact prefixLift 194176
  have htrace : WordTrace (prefixWord ++ tailWord_194176) baseStart_194176 baseEnd_194176 := by
    simpa [prefixWord, tailWord_194176, baseEnd_194176] using wordTrace_append hprefix tailTrace_194176
  have hstable : (prefixWord ++ tailWord_194176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194176).length < 2 ^ (prefixWord ++ tailWord_194176).sum := by decide
  have hdescent : baseEnd_194176 < baseStart_194176 := by decide
  rcases family_descends (prefixWord ++ tailWord_194176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194180 : List Nat := [2, 3, 2, 1, 4, 1, 3, 6]
def baseStart_194180 : Nat := 118140960795 + 194180 * 2 ^ 59
def prefixEnd_194180 : Nat := 4983230072969 + 3 ^ 40 * 194180 * 2
def baseEnd_194180 : Nat := 7385753591863370633851

theorem tailTrace_194180 : CollatzResearch.WordTrace tailWord_194180 prefixEnd_194180 7385753591863370633851 := by
  unfold tailWord_194180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541163218263249074421997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4721550957684332099229329 3541163218263249074421997)
  ·
    refine ⟨1327936206848718402908249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3541163218263249074421997 1327936206848718402908249)
    ·
      refine ⟨995952155136538802181187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1327936206848718402908249 995952155136538802181187)
      ·
        refine ⟨1493928232704808203271781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995952155136538802181187 1493928232704808203271781)
        ·
          refine ⟨280111543632151538113459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1493928232704808203271781 280111543632151538113459)
          ·
            refine ⟨420167315448227307170189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280111543632151538113459 420167315448227307170189)
            ·
              refine ⟨157562743293085240188821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420167315448227307170189 157562743293085240188821)
              ·
                refine ⟨7385753591863370633851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157562743293085240188821 7385753591863370633851)
                ·
                  rfl

theorem cell22_194180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_194180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194180 prefixEnd_194180 := by exact prefixLift 194180
  have htrace : WordTrace (prefixWord ++ tailWord_194180) baseStart_194180 baseEnd_194180 := by
    simpa [prefixWord, tailWord_194180, baseEnd_194180] using wordTrace_append hprefix tailTrace_194180
  have hstable : (prefixWord ++ tailWord_194180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194180).length < 2 ^ (prefixWord ++ tailWord_194180).sum := by decide
  have hdescent : baseEnd_194180 < baseStart_194180 := by decide
  rcases family_descends (prefixWord ++ tailWord_194180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194208 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_194208 : Nat := 118140960795 + 194208 * 2 ^ 59
def prefixEnd_194208 : Nat := 4983230072969 + 3 ^ 40 * 194208 * 2
def baseEnd_194208 : Nat := 22160455766329198668191

theorem tailTrace_194208 : CollatzResearch.WordTrace tailWord_194208 prefixEnd_194208 22160455766329198668191 := by
  unfold tailWord_194208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541673840212529465431639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4722231786950039287242185 3541673840212529465431639)
  ·
    refine ⟨5312510760318794198147459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3541673840212529465431639 5312510760318794198147459)
    ·
      refine ⟨7968766140478191297221189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5312510760318794198147459 7968766140478191297221189)
      ·
        refine ⟨1494143651339660868228973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7968766140478191297221189 1494143651339660868228973)
        ·
          refine ⟨560303869252372825585865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1494143651339660868228973 560303869252372825585865)
          ·
            refine ⟨420227901939279619189399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560303869252372825585865 420227901939279619189399)
            ·
              refine ⟨630341852908919428784099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420227901939279619189399 630341852908919428784099)
              ·
                refine ⟨945512779363379143176149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630341852908919428784099 945512779363379143176149)
                ·
                  refine ⟨22160455766329198668191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 945512779363379143176149 22160455766329198668191)
                  ·
                    rfl

theorem cell22_194208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_194208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194208 prefixEnd_194208 := by exact prefixLift 194208
  have htrace : WordTrace (prefixWord ++ tailWord_194208) baseStart_194208 baseEnd_194208 := by
    simpa [prefixWord, tailWord_194208, baseEnd_194208] using wordTrace_append hprefix tailTrace_194208
  have hstable : (prefixWord ++ tailWord_194208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194208).length < 2 ^ (prefixWord ++ tailWord_194208).sum := by decide
  have hdescent : baseEnd_194208 < baseStart_194208 := by decide
  rcases family_descends (prefixWord ++ tailWord_194208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194212 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_194212 : Nat := 118140960795 + 194212 * 2 ^ 59
def prefixEnd_194212 : Nat := 4983230072969 + 3 ^ 40 * 194212 * 2
def baseEnd_194212 : Nat := 66482736580732918904561

theorem tailTrace_194212 : CollatzResearch.WordTrace tailWord_194212 prefixEnd_194212 66482736580732918904561 := by
  unfold tailWord_194212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541746786205283807004445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4722329048273711742672593 3541746786205283807004445)
  ·
    refine ⟨1328155044826981427626667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3541746786205283807004445 1328155044826981427626667)
    ·
      refine ⟨1992232567240472141440001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328155044826981427626667 1992232567240472141440001)
      ·
        refine ⟨1494174425430354106080001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1992232567240472141440001 1494174425430354106080001)
        ·
          refine ⟨1120630819072765579560001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494174425430354106080001 1120630819072765579560001)
          ·
            refine ⟨840473114304574184670001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120630819072765579560001 840473114304574184670001)
            ·
              refine ⟨630354835728430638502501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840473114304574184670001 630354835728430638502501)
              ·
                refine ⟨118191531699080744719219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630354835728430638502501 118191531699080744719219)
                ·
                  refine ⟨177287297548621117078829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118191531699080744719219 177287297548621117078829)
                  ·
                    refine ⟨66482736580732918904561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177287297548621117078829 66482736580732918904561)
                    ·
                      rfl

theorem cell22_194212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_194212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194212 prefixEnd_194212 := by exact prefixLift 194212
  have htrace : WordTrace (prefixWord ++ tailWord_194212) baseStart_194212 baseEnd_194212 := by
    simpa [prefixWord, tailWord_194212, baseEnd_194212] using wordTrace_append hprefix tailTrace_194212
  have hstable : (prefixWord ++ tailWord_194212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194212).length < 2 ^ (prefixWord ++ tailWord_194212).sum := by decide
  have hdescent : baseEnd_194212 < baseStart_194212 := by decide
  rcases family_descends (prefixWord ++ tailWord_194212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194300 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_194300 : Nat := 118140960795 + 194300 * 2 ^ 59
def prefixEnd_194300 : Nat := 4983230072969 + 3 ^ 40 * 194300 * 2
def baseEnd_194300 : Nat := 66512860779130022704291

theorem tailTrace_194300 : CollatzResearch.WordTrace tailWord_194300 prefixEnd_194300 66512860779130022704291 := by
  unfold tailWord_194300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543351598045879321606177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4724468797394505762141569 3543351598045879321606177)
  ·
    refine ⟨2657513698534409491204633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3543351598045879321606177 2657513698534409491204633)
    ·
      refine ⟨1993135273900807118403475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657513698534409491204633 1993135273900807118403475)
      ·
        refine ⟨2989702910851210677605213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993135273900807118403475 2989702910851210677605213)
        ·
          refine ⟨1121138591569204004101955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2989702910851210677605213 1121138591569204004101955)
          ·
            refine ⟨1681707887353806006152933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121138591569204004101955 1681707887353806006152933)
            ·
              refine ⟨315320228878838626153675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1681707887353806006152933 315320228878838626153675)
              ·
                refine ⟨472980343318257939230513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315320228878838626153675 472980343318257939230513)
                ·
                  refine ⟨354735257488693454422885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472980343318257939230513 354735257488693454422885)
                  ·
                    refine ⟨66512860779130022704291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354735257488693454422885 66512860779130022704291)
                    ·
                      rfl

theorem cell22_194300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_194300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194300 prefixEnd_194300 := by exact prefixLift 194300
  have htrace : WordTrace (prefixWord ++ tailWord_194300) baseStart_194300 baseEnd_194300 := by
    simpa [prefixWord, tailWord_194300, baseEnd_194300] using wordTrace_append hprefix tailTrace_194300
  have hstable : (prefixWord ++ tailWord_194300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194300).length < 2 ^ (prefixWord ++ tailWord_194300).sum := by decide
  have hdescent : baseEnd_194300 < baseStart_194300 := by decide
  rcases family_descends (prefixWord ++ tailWord_194300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194302 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_194302 : Nat := 118140960795 + 194302 * 2 ^ 59
def prefixEnd_194302 : Nat := 4983230072969 + 3 ^ 40 * 194302 * 2
def baseEnd_194302 : Nat := 66513545420002684154285

theorem tailTrace_194302 : CollatzResearch.WordTrace tailWord_194302 prefixEnd_194302 66513545420002684154285 := by
  unfold tailWord_194302
  simp only [CollatzResearch.WordTrace]
  refine ⟨885847017760564123098145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4724517428056341989856773 885847017760564123098145)
  ·
    refine ⟨664385263320423092323609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 885847017760564123098145 664385263320423092323609)
    ·
      refine ⟨498288947490317319242707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 664385263320423092323609 498288947490317319242707)
      ·
        refine ⟨747433421235475978864061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498288947490317319242707 747433421235475978864061)
        ·
          refine ⟨280287532963303492074023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747433421235475978864061 280287532963303492074023)
          ·
            refine ⟨420431299444955238111035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280287532963303492074023 420431299444955238111035)
            ·
              refine ⟨630646949167432857166553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420431299444955238111035 630646949167432857166553)
              ·
                refine ⟨472985211875574642874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630646949167432857166553 472985211875574642874915)
                ·
                  refine ⟨709477817813361964312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472985211875574642874915 709477817813361964312373)
                  ·
                    refine ⟨66513545420002684154285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 709477817813361964312373 66513545420002684154285)
                    ·
                      rfl

theorem cell22_194302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_194302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194302 prefixEnd_194302 := by exact prefixLift 194302
  have htrace : WordTrace (prefixWord ++ tailWord_194302) baseStart_194302 baseEnd_194302 := by
    simpa [prefixWord, tailWord_194302, baseEnd_194302] using wordTrace_append hprefix tailTrace_194302
  have hstable : (prefixWord ++ tailWord_194302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194302).length < 2 ^ (prefixWord ++ tailWord_194302).sum := by decide
  have hdescent : baseEnd_194302 < baseStart_194302 := by decide
  rcases family_descends (prefixWord ++ tailWord_194302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194328 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_194328 : Nat := 118140960795 + 194328 * 2 ^ 59
def prefixEnd_194328 : Nat := 4983230072969 + 3 ^ 40 * 194328 * 2
def baseEnd_194328 : Nat := 66522445751347283004205

theorem tailTrace_194328 : CollatzResearch.WordTrace tailWord_194328 prefixEnd_194328 66522445751347283004205 := by
  unfold tailWord_194328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543862219995159712615819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4725149626660212950154425 3543862219995159712615819)
  ·
    refine ⟨5315793329992739568923729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543862219995159712615819 5315793329992739568923729)
    ·
      refine ⟨3986844997494554676692797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5315793329992739568923729 3986844997494554676692797)
      ·
        refine ⟨1495066874060458003759799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3986844997494554676692797 1495066874060458003759799)
        ·
          refine ⟨2242600311090687005639699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495066874060458003759799 2242600311090687005639699)
          ·
            refine ⟨3363900466636030508459549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242600311090687005639699 3363900466636030508459549)
            ·
              refine ⟨1261462674988511440672331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3363900466636030508459549 1261462674988511440672331)
              ·
                refine ⟨1892194012482767161008497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261462674988511440672331 1892194012482767161008497)
                ·
                  refine ⟨1419145509362075370756373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892194012482767161008497 1419145509362075370756373)
                  ·
                    refine ⟨66522445751347283004205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1419145509362075370756373 66522445751347283004205)
                    ·
                      rfl

theorem cell22_194328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_194328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194328 prefixEnd_194328 := by exact prefixLift 194328
  have htrace : WordTrace (prefixWord ++ tailWord_194328) baseStart_194328 baseEnd_194328 := by
    simpa [prefixWord, tailWord_194328, baseEnd_194328] using wordTrace_append hprefix tailTrace_194328
  have hstable : (prefixWord ++ tailWord_194328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194328).length < 2 ^ (prefixWord ++ tailWord_194328).sum := by decide
  have hdescent : baseEnd_194328 < baseStart_194328 := by decide
  rcases family_descends (prefixWord ++ tailWord_194328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194381 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_194381 : Nat := 118140960795 + 194381 * 2 ^ 59
def prefixEnd_194381 : Nat := 4983230072969 + 3 ^ 40 * 194381 * 2
def baseEnd_194381 : Nat := 66540588734472811429043

theorem tailTrace_194381 : CollatzResearch.WordTrace tailWord_194381 prefixEnd_194381 66540588734472811429043 := by
  unfold tailWord_194381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7089657508798309476910997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4726438339198872984607331 7089657508798309476910997)
  ·
    refine ⟨332327695724920756730203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7089657508798309476910997 332327695724920756730203)
    ·
      refine ⟨498491543587381135095305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332327695724920756730203 498491543587381135095305)
      ·
        refine ⟨373868657690535851321479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498491543587381135095305 373868657690535851321479)
        ·
          refine ⟨560802986535803776982219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373868657690535851321479 560802986535803776982219)
          ·
            refine ⟨841204479803705665473329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560802986535803776982219 841204479803705665473329)
            ·
              refine ⟨630903359852779249104997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841204479803705665473329 630903359852779249104997)
              ·
                refine ⟨118294379972396109207187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630903359852779249104997 118294379972396109207187)
                ·
                  refine ⟨177441569958594163810781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118294379972396109207187 177441569958594163810781)
                  ·
                    refine ⟨66540588734472811429043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177441569958594163810781 66540588734472811429043)
                    ·
                      rfl

theorem cell22_194381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_194381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194381 prefixEnd_194381 := by exact prefixLift 194381
  have htrace : WordTrace (prefixWord ++ tailWord_194381) baseStart_194381 baseEnd_194381 := by
    simpa [prefixWord, tailWord_194381, baseEnd_194381] using wordTrace_append hprefix tailTrace_194381
  have hstable : (prefixWord ++ tailWord_194381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194381).length < 2 ^ (prefixWord ++ tailWord_194381).sum := by decide
  have hdescent : baseEnd_194381 < baseStart_194381 := by decide
  rcases family_descends (prefixWord ++ tailWord_194381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194407 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 1, 4]
def baseStart_194407 : Nat := 118140960795 + 194407 * 2 ^ 59
def prefixEnd_194407 : Nat := 4983230072969 + 3 ^ 40 * 194407 * 2
def baseEnd_194407 : Nat := 66549489065817410278963

theorem tailTrace_194407 : CollatzResearch.WordTrace tailWord_194407 prefixEnd_194407 66549489065817410278963 := by
  unfold tailWord_194407
  simp only [CollatzResearch.WordTrace]
  refine ⟨7090605806704115917357475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4727070537802743944904983 7090605806704115917357475)
  ·
    refine ⟨10635908710056173876036213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7090605806704115917357475 10635908710056173876036213)
    ·
      refine ⟨997116441567766300878395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10635908710056173876036213 997116441567766300878395)
      ·
        refine ⟨1495674662351649451317593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997116441567766300878395 1495674662351649451317593)
        ·
          refine ⟨1121755996763737088488195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495674662351649451317593 1121755996763737088488195)
          ·
            refine ⟨1682633995145605632732293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121755996763737088488195 1682633995145605632732293)
            ·
              refine ⟨315493874089801056137305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1682633995145605632732293 315493874089801056137305)
              ·
                refine ⟨236620405567350792102979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315493874089801056137305 236620405567350792102979)
                ·
                  refine ⟨354930608351026188154469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236620405567350792102979 354930608351026188154469)
                  ·
                    refine ⟨66549489065817410278963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354930608351026188154469 66549489065817410278963)
                    ·
                      rfl

theorem cell22_194407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_194407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194407 prefixEnd_194407 := by exact prefixLift 194407
  have htrace : WordTrace (prefixWord ++ tailWord_194407) baseStart_194407 baseEnd_194407 := by
    simpa [prefixWord, tailWord_194407, baseEnd_194407] using wordTrace_append hprefix tailTrace_194407
  have hstable : (prefixWord ++ tailWord_194407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194407).length < 2 ^ (prefixWord ++ tailWord_194407).sum := by decide
  have hdescent : baseEnd_194407 < baseStart_194407 := by decide
  rcases family_descends (prefixWord ++ tailWord_194407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194435 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_194435 : Nat := 118140960795 + 194435 * 2 ^ 59
def prefixEnd_194435 : Nat := 4983230072969 + 3 ^ 40 * 194435 * 2
def baseEnd_194435 : Nat := 66559074038034670578877

theorem tailTrace_194435 : CollatzResearch.WordTrace tailWord_194435 prefixEnd_194435 66559074038034670578877 := by
  unfold tailWord_194435
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091627050602676699376759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4727751367068451132917839 7091627050602676699376759)
  ·
    refine ⟨10637440575904015049065139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7091627050602676699376759 10637440575904015049065139)
    ·
      refine ⟨15956160863856022573597709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10637440575904015049065139 15956160863856022573597709)
      ·
        refine ⟨5983560323946008465099141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15956160863856022573597709 5983560323946008465099141)
        ·
          refine ⟨1121917560739876587206089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5983560323946008465099141 1121917560739876587206089)
          ·
            refine ⟨841438170554907440404567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121917560739876587206089 841438170554907440404567)
            ·
              refine ⟨1262157255832361160606851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841438170554907440404567 1262157255832361160606851)
              ·
                refine ⟨1893235883748541740910277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262157255832361160606851 1893235883748541740910277)
                ·
                  refine ⟨354981728202851576420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1893235883748541740910277 354981728202851576420677)
                  ·
                    refine ⟨66559074038034670578877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354981728202851576420677 66559074038034670578877)
                    ·
                      rfl

theorem cell22_194435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_194435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194435 prefixEnd_194435 := by exact prefixLift 194435
  have htrace : WordTrace (prefixWord ++ tailWord_194435) baseStart_194435 baseEnd_194435 := by
    simpa [prefixWord, tailWord_194435, baseEnd_194435] using wordTrace_append hprefix tailTrace_194435
  have hstable : (prefixWord ++ tailWord_194435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194435).length < 2 ^ (prefixWord ++ tailWord_194435).sum := by decide
  have hdescent : baseEnd_194435 < baseStart_194435 := by decide
  rcases family_descends (prefixWord ++ tailWord_194435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194437 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_194437 : Nat := 118140960795 + 194437 * 2 ^ 59
def prefixEnd_194437 : Nat := 4983230072969 + 3 ^ 40 * 194437 * 2
def baseEnd_194437 : Nat := 66559758678907332028871

theorem tailTrace_194437 : CollatzResearch.WordTrace tailWord_194437 prefixEnd_194437 66559758678907332028871 := by
  unfold tailWord_194437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091699996595431040949565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4727799997730287360633043 7091699996595431040949565)
  ·
    refine ⟨2659387498723286640356087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7091699996595431040949565 2659387498723286640356087)
    ·
      refine ⟨3989081248084929960534131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2659387498723286640356087 3989081248084929960534131)
      ·
        refine ⟨5983621872127394940801197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989081248084929960534131 5983621872127394940801197)
        ·
          refine ⟨2243858202047773102800449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5983621872127394940801197 2243858202047773102800449)
          ·
            refine ⟨1682893651535829827100337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243858202047773102800449 1682893651535829827100337)
            ·
              refine ⟨1262170238651872370325253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682893651535829827100337 1262170238651872370325253)
              ·
                refine ⟨236656919747226069435985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1262170238651872370325253 236656919747226069435985)
                ·
                  refine ⟨177492689810419552076989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236656919747226069435985 177492689810419552076989)
                  ·
                    refine ⟨66559758678907332028871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177492689810419552076989 66559758678907332028871)
                    ·
                      rfl

theorem cell22_194437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_194437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194437 prefixEnd_194437 := by exact prefixLift 194437
  have htrace : WordTrace (prefixWord ++ tailWord_194437) baseStart_194437 baseEnd_194437 := by
    simpa [prefixWord, tailWord_194437, baseEnd_194437] using wordTrace_append hprefix tailTrace_194437
  have hstable : (prefixWord ++ tailWord_194437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194437).length < 2 ^ (prefixWord ++ tailWord_194437).sum := by decide
  have hdescent : baseEnd_194437 < baseStart_194437 := by decide
  rcases family_descends (prefixWord ++ tailWord_194437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194439 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 6]
def baseStart_194439 : Nat := 118140960795 + 194439 * 2 ^ 59
def prefixEnd_194439 : Nat := 4983230072969 + 3 ^ 40 * 194439 * 2
def baseEnd_194439 : Nat := 22186814439926664492955

theorem tailTrace_194439 : CollatzResearch.WordTrace tailWord_194439 prefixEnd_194439 22186814439926664492955 := by
  unfold tailWord_194439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091772942588185382522371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4727848628392123588348247 7091772942588185382522371)
  ·
    refine ⟨10637659413882278073783557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7091772942588185382522371 10637659413882278073783557)
    ·
      refine ⟨1994561140102927138834417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10637659413882278073783557 1994561140102927138834417)
      ·
        refine ⟨1495920855077195354125813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994561140102927138834417 1495920855077195354125813)
        ·
          refine ⟨140242580163487064449295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1495920855077195354125813 140242580163487064449295)
          ·
            refine ⟨210363870245230596673943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140242580163487064449295 210363870245230596673943)
            ·
              refine ⟨315545805367845895010915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210363870245230596673943 315545805367845895010915)
              ·
                refine ⟨473318708051768842516373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315545805367845895010915 473318708051768842516373)
                ·
                  refine ⟨22186814439926664492955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 473318708051768842516373 22186814439926664492955)
                  ·
                    rfl

theorem cell22_194439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 6].length) (baseStart_194439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194439 prefixEnd_194439 := by exact prefixLift 194439
  have htrace : WordTrace (prefixWord ++ tailWord_194439) baseStart_194439 baseEnd_194439 := by
    simpa [prefixWord, tailWord_194439, baseEnd_194439] using wordTrace_append hprefix tailTrace_194439
  have hstable : (prefixWord ++ tailWord_194439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194439).length < 2 ^ (prefixWord ++ tailWord_194439).sum := by decide
  have hdescent : baseEnd_194439 < baseStart_194439 := by decide
  rcases family_descends (prefixWord ++ tailWord_194439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194484 : List Nat := [2, 5, 2, 1, 3, 9]
def baseStart_194484 : Nat := 118140960795 + 194484 * 2 ^ 59
def prefixEnd_194484 : Nat := 4983230072969 + 3 ^ 40 * 194484 * 2
def baseEnd_194484 : Nat := 821924046165615754367

theorem tailTrace_194484 : CollatzResearch.WordTrace tailWord_194484 prefixEnd_194484 821924046165615754367 := by
  unfold tailWord_194484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546707113712579033955253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4728942818283438711940337 3546707113712579033955253)
  ·
    refine ⟨332503791910554284433305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3546707113712579033955253 332503791910554284433305)
    ·
      refine ⟨249377843932915713324979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332503791910554284433305 249377843932915713324979)
      ·
        refine ⟨374066765899373569987469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249377843932915713324979 374066765899373569987469)
        ·
          refine ⟨140275037212265088745301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374066765899373569987469 140275037212265088745301)
          ·
            refine ⟨821924046165615754367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 140275037212265088745301 821924046165615754367)
            ·
              rfl

theorem cell22_194484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 9].length) (baseStart_194484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194484 prefixEnd_194484 := by exact prefixLift 194484
  have htrace : WordTrace (prefixWord ++ tailWord_194484) baseStart_194484 baseEnd_194484 := by
    simpa [prefixWord, tailWord_194484, baseEnd_194484] using wordTrace_append hprefix tailTrace_194484
  have hstable : (prefixWord ++ tailWord_194484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194484).length < 2 ^ (prefixWord ++ tailWord_194484).sum := by decide
  have hdescent : baseEnd_194484 < baseStart_194484 := by decide
  rcases family_descends (prefixWord ++ tailWord_194484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194555 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_194555 : Nat := 118140960795 + 194555 * 2 ^ 59
def prefixEnd_194555 : Nat := 4983230072969 + 3 ^ 40 * 194555 * 2
def baseEnd_194555 : Nat := 66600152490394357578509

theorem tailTrace_194555 : CollatzResearch.WordTrace tailWord_194555 prefixEnd_194555 66600152490394357578509 := by
  unfold tailWord_194555
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096003810167937193745119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4730669206778624795830079 7096003810167937193745119)
  ·
    refine ⟨10644005715251905790617679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096003810167937193745119 10644005715251905790617679)
    ·
      refine ⟨15966008572877858685926519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644005715251905790617679 15966008572877858685926519)
      ·
        refine ⟨23949012859316788028889779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15966008572877858685926519 23949012859316788028889779)
        ·
          refine ⟨35923519288975182043334669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23949012859316788028889779 35923519288975182043334669)
          ·
            refine ⟨13471319733365693266250501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35923519288975182043334669 13471319733365693266250501)
            ·
              refine ⟨2525872450006067487421969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13471319733365693266250501 2525872450006067487421969)
              ·
                refine ⟨1894404337504550615566477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525872450006067487421969 1894404337504550615566477)
                ·
                  refine ⟨710401626564206480837429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1894404337504550615566477 710401626564206480837429)
                  ·
                    refine ⟨66600152490394357578509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 710401626564206480837429 66600152490394357578509)
                    ·
                      rfl

theorem cell22_194555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_194555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194555 prefixEnd_194555 := by exact prefixLift 194555
  have htrace : WordTrace (prefixWord ++ tailWord_194555) baseStart_194555 baseEnd_194555 := by
    simpa [prefixWord, tailWord_194555, baseEnd_194555] using wordTrace_append hprefix tailTrace_194555
  have hstable : (prefixWord ++ tailWord_194555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194555).length < 2 ^ (prefixWord ++ tailWord_194555).sum := by decide
  have hdescent : baseEnd_194555 < baseStart_194555 := by decide
  rcases family_descends (prefixWord ++ tailWord_194555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194589 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_194589 : Nat := 118140960795 + 194589 * 2 ^ 59
def prefixEnd_194589 : Nat := 4983230072969 + 3 ^ 40 * 194589 * 2
def baseEnd_194589 : Nat := 66611791385229602228405

theorem tailTrace_194589 : CollatzResearch.WordTrace tailWord_194589 prefixEnd_194589 66611791385229602228405 := by
  unfold tailWord_194589
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097243892044761000482821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4731495928029840666988547 7097243892044761000482821)
  ·
    refine ⟨1330733229758392687590529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7097243892044761000482821 1330733229758392687590529)
    ·
      refine ⟨998049922318794515692897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1330733229758392687590529 998049922318794515692897)
      ·
        refine ⟨748537441739095886769673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998049922318794515692897 748537441739095886769673)
        ·
          refine ⟨561403081304321915077255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748537441739095886769673 561403081304321915077255)
          ·
            refine ⟨842104621956482872615883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561403081304321915077255 842104621956482872615883)
            ·
              refine ⟨1263156932934724308923825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842104621956482872615883 1263156932934724308923825)
              ·
                refine ⟨947367699701043231692869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263156932934724308923825 947367699701043231692869)
                ·
                  refine ⟨177631443693945605942413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 947367699701043231692869 177631443693945605942413)
                  ·
                    refine ⟨66611791385229602228405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177631443693945605942413 66611791385229602228405)
                    ·
                      rfl

theorem cell22_194589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_194589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194589 prefixEnd_194589 := by exact prefixLift 194589
  have htrace : WordTrace (prefixWord ++ tailWord_194589) baseStart_194589 baseEnd_194589 := by
    simpa [prefixWord, tailWord_194589, baseEnd_194589] using wordTrace_append hprefix tailTrace_194589
  have hstable : (prefixWord ++ tailWord_194589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194589).length < 2 ^ (prefixWord ++ tailWord_194589).sum := by decide
  have hdescent : baseEnd_194589 < baseStart_194589 := by decide
  rcases family_descends (prefixWord ++ tailWord_194589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194602 : List Nat := [3, 1, 4, 1, 2, 1, 10]
def baseStart_194602 : Nat := 118140960795 + 194602 * 2 ^ 59
def prefixEnd_194602 : Nat := 4983230072969 + 3 ^ 40 * 194602 * 2
def baseEnd_194602 : Nat := 2467268205588959320495

theorem tailTrace_194602 : CollatzResearch.WordTrace tailWord_194602 prefixEnd_194602 2467268205588959320495 := by
  unfold tailWord_194602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774429510249416055176515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4731812027331776147137373 1774429510249416055176515)
  ·
    refine ⟨2661644265374124082764773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1774429510249416055176515 2661644265374124082764773)
    ·
      refine ⟨499058299757648265518395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2661644265374124082764773 499058299757648265518395)
      ·
        refine ⟨748587449636472398277593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499058299757648265518395 748587449636472398277593)
        ·
          refine ⟨561440587227354298708195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748587449636472398277593 561440587227354298708195)
          ·
            refine ⟨842160880841031448062293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561440587227354298708195 842160880841031448062293)
            ·
              refine ⟨2467268205588959320495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 842160880841031448062293 2467268205588959320495)
              ·
                rfl

theorem cell22_194602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 10].length) (baseStart_194602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194602 prefixEnd_194602 := by exact prefixLift 194602
  have htrace : WordTrace (prefixWord ++ tailWord_194602) baseStart_194602 baseEnd_194602 := by
    simpa [prefixWord, tailWord_194602, baseEnd_194602] using wordTrace_append hprefix tailTrace_194602
  have hstable : (prefixWord ++ tailWord_194602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194602).length < 2 ^ (prefixWord ++ tailWord_194602).sum := by decide
  have hdescent : baseEnd_194602 < baseStart_194602 := by decide
  rcases family_descends (prefixWord ++ tailWord_194602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194668 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_194668 : Nat := 118140960795 + 194668 * 2 ^ 59
def prefixEnd_194668 : Nat := 4983230072969 + 3 ^ 40 * 194668 * 2
def baseEnd_194668 : Nat := 66638834699699729503163

theorem tailTrace_194668 : CollatzResearch.WordTrace tailWord_194668 prefixEnd_194668 66638834699699729503163 := by
  unfold tailWord_194668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3550062629379278746304329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4733416839172371661739105 3550062629379278746304329)
  ·
    refine ⟨2662546972034459059728247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3550062629379278746304329 2662546972034459059728247)
    ·
      refine ⟨3993820458051688589592371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2662546972034459059728247 3993820458051688589592371)
      ·
        refine ⟨5990730687077532884388557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993820458051688589592371 5990730687077532884388557)
        ·
          refine ⟨2246524007654074831645709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5990730687077532884388557 2246524007654074831645709)
          ·
            refine ⟨842446502870278061867141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2246524007654074831645709 842446502870278061867141)
            ·
              refine ⟨157958719288177136600089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 842446502870278061867141 157958719288177136600089)
              ·
                refine ⟨118469039466132852450067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157958719288177136600089 118469039466132852450067)
                ·
                  refine ⟨177703559199199278675101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118469039466132852450067 177703559199199278675101)
                  ·
                    refine ⟨66638834699699729503163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177703559199199278675101 66638834699699729503163)
                    ·
                      rfl

theorem cell22_194668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_194668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194668 prefixEnd_194668 := by exact prefixLift 194668
  have htrace : WordTrace (prefixWord ++ tailWord_194668) baseStart_194668 baseEnd_194668 := by
    simpa [prefixWord, tailWord_194668, baseEnd_194668] using wordTrace_append hprefix tailTrace_194668
  have hstable : (prefixWord ++ tailWord_194668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194668).length < 2 ^ (prefixWord ++ tailWord_194668).sum := by decide
  have hdescent : baseEnd_194668 < baseStart_194668 := by decide
  rcases family_descends (prefixWord ++ tailWord_194668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194711 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 1, 4]
def baseStart_194711 : Nat := 118140960795 + 194711 * 2 ^ 59
def prefixEnd_194711 : Nat := 4983230072969 + 3 ^ 40 * 194711 * 2
def baseEnd_194711 : Nat := 66653554478461950678031

theorem tailTrace_194711 : CollatzResearch.WordTrace tailWord_194711 prefixEnd_194711 66653554478461950678031 := by
  unfold tailWord_194711
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101693597602775836423987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4734462398401850557615991 7101693597602775836423987)
  ·
    refine ⟨10652540396404163754635981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7101693597602775836423987 10652540396404163754635981)
    ·
      refine ⟨3994702648651561407988493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10652540396404163754635981 3994702648651561407988493)
      ·
        refine ⟨1498013493244335527995685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3994702648651561407988493 1498013493244335527995685)
        ·
          refine ⟨280877529983312911499191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1498013493244335527995685 280877529983312911499191)
          ·
            refine ⟨421316294974969367248787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280877529983312911499191 421316294974969367248787)
            ·
              refine ⟨631974442462454050873181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421316294974969367248787 631974442462454050873181)
              ·
                refine ⟨236990415923420269077443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631974442462454050873181 236990415923420269077443)
                ·
                  refine ⟨355485623885130403616165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236990415923420269077443 355485623885130403616165)
                  ·
                    refine ⟨66653554478461950678031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355485623885130403616165 66653554478461950678031)
                    ·
                      rfl

theorem cell22_194711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_194711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194711 prefixEnd_194711 := by exact prefixLift 194711
  have htrace : WordTrace (prefixWord ++ tailWord_194711) baseStart_194711 baseEnd_194711 := by
    simpa [prefixWord, tailWord_194711, baseEnd_194711] using wordTrace_append hprefix tailTrace_194711
  have hstable : (prefixWord ++ tailWord_194711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194711).length < 2 ^ (prefixWord ++ tailWord_194711).sum := by decide
  have hdescent : baseEnd_194711 < baseStart_194711 := by decide
  rcases family_descends (prefixWord ++ tailWord_194711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194769 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_194769 : Nat := 118140960795 + 194769 * 2 ^ 59
def prefixEnd_194769 : Nat := 4983230072969 + 3 ^ 40 * 194769 * 2
def baseEnd_194769 : Nat := 66673409063769132727853

theorem tailTrace_194769 : CollatzResearch.WordTrace tailWord_194769 prefixEnd_194769 66673409063769132727853 := by
  unfold tailWord_194769
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103809031392651742035361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4735872687595101161356907 7103809031392651742035361)
  ·
    refine ⟨5327856773544488806526521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7103809031392651742035361 5327856773544488806526521)
    ·
      refine ⟨3995892580158366604894891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5327856773544488806526521 3995892580158366604894891)
      ·
        refine ⟨5993838870237549907342337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995892580158366604894891 5993838870237549907342337)
        ·
          refine ⟨4495379152678162430506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993838870237549907342337 4495379152678162430506753)
          ·
            refine ⟨3371534364508621822880065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495379152678162430506753 3371534364508621822880065)
            ·
              refine ⟨2528650773381466367160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371534364508621822880065 2528650773381466367160049)
              ·
                refine ⟨1896488080036099775370037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528650773381466367160049 1896488080036099775370037)
                ·
                  refine ⟨177795757503384353940941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1896488080036099775370037 177795757503384353940941)
                  ·
                    refine ⟨66673409063769132727853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177795757503384353940941 66673409063769132727853)
                    ·
                      rfl

theorem cell22_194769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_194769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194769 prefixEnd_194769 := by exact prefixLift 194769
  have htrace : WordTrace (prefixWord ++ tailWord_194769) baseStart_194769 baseEnd_194769 := by
    simpa [prefixWord, tailWord_194769, baseEnd_194769] using wordTrace_append hprefix tailTrace_194769
  have hstable : (prefixWord ++ tailWord_194769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194769).length < 2 ^ (prefixWord ++ tailWord_194769).sum := by decide
  have hdescent : baseEnd_194769 < baseStart_194769 := by decide
  rcases family_descends (prefixWord ++ tailWord_194769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194844 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_194844 : Nat := 118140960795 + 194844 * 2 ^ 59
def prefixEnd_194844 : Nat := 4983230072969 + 3 ^ 40 * 194844 * 2
def baseEnd_194844 : Nat := 22233027698831312367541

theorem tailTrace_194844 : CollatzResearch.WordTrace tailWord_194844 prefixEnd_194844 22233027698831312367541 := by
  unfold tailWord_194844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553272253060469775507793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4737696337413959700677057 3553272253060469775507793)
  ·
    refine ⟨2664954189795352331630845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3553272253060469775507793 2664954189795352331630845)
    ·
      refine ⟨999357821173257124361567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2664954189795352331630845 999357821173257124361567)
      ·
        refine ⟨1499036731759885686542351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999357821173257124361567 1499036731759885686542351)
        ·
          refine ⟨2248555097639828529813527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499036731759885686542351 2248555097639828529813527)
          ·
            refine ⟨3372832646459742794720291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248555097639828529813527 3372832646459742794720291)
            ·
              refine ⟨5059248969689614192080437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372832646459742794720291 5059248969689614192080437)
              ·
                refine ⟨474304590908401330507541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5059248969689614192080437 474304590908401330507541)
                ·
                  refine ⟨22233027698831312367541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 474304590908401330507541 22233027698831312367541)
                  ·
                    rfl

theorem cell22_194844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_194844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194844 prefixEnd_194844 := by exact prefixLift 194844
  have htrace : WordTrace (prefixWord ++ tailWord_194844) baseStart_194844 baseEnd_194844 := by
    simpa [prefixWord, tailWord_194844, baseEnd_194844] using wordTrace_append hprefix tailTrace_194844
  have hstable : (prefixWord ++ tailWord_194844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194844).length < 2 ^ (prefixWord ++ tailWord_194844).sum := by decide
  have hdescent : baseEnd_194844 < baseStart_194844 := by decide
  rcases family_descends (prefixWord ++ tailWord_194844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194876 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_194876 : Nat := 118140960795 + 194876 * 2 ^ 59
def prefixEnd_194876 : Nat := 4983230072969 + 3 ^ 40 * 194876 * 2
def baseEnd_194876 : Nat := 66710037350456520302525

theorem tailTrace_194876 : CollatzResearch.WordTrace tailWord_194876 prefixEnd_194876 66710037350456520302525 := by
  unfold tailWord_194876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553855821002504508090241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4738474428003339344120321 3553855821002504508090241)
  ·
    refine ⟨2665391865751878381067681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3553855821002504508090241 2665391865751878381067681)
    ·
      refine ⟨1999043899313908785800761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2665391865751878381067681 1999043899313908785800761)
      ·
        refine ⟨1499282924485431589350571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1999043899313908785800761 1499282924485431589350571)
        ·
          refine ⟨2248924386728147384025857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499282924485431589350571 2248924386728147384025857)
          ·
            refine ⟨1686693290046110538019393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248924386728147384025857 1686693290046110538019393)
            ·
              refine ⟨1265019967534582903514545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686693290046110538019393 1265019967534582903514545)
              ·
                refine ⟨948764975650937177635909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265019967534582903514545 948764975650937177635909)
                ·
                  refine ⟨177893432934550720806733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 948764975650937177635909 177893432934550720806733)
                  ·
                    refine ⟨66710037350456520302525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177893432934550720806733 66710037350456520302525)
                    ·
                      rfl

theorem cell22_194876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_194876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194876 prefixEnd_194876 := by exact prefixLift 194876
  have htrace : WordTrace (prefixWord ++ tailWord_194876) baseStart_194876 baseEnd_194876 := by
    simpa [prefixWord, tailWord_194876, baseEnd_194876] using wordTrace_append hprefix tailTrace_194876
  have hstable : (prefixWord ++ tailWord_194876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194876).length < 2 ^ (prefixWord ++ tailWord_194876).sum := by decide
  have hdescent : baseEnd_194876 < baseStart_194876 := by decide
  rcases family_descends (prefixWord ++ tailWord_194876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194878 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_194878 : Nat := 118140960795 + 194878 * 2 ^ 59
def prefixEnd_194878 : Nat := 4983230072969 + 3 ^ 40 * 194878 * 2
def baseEnd_194878 : Nat := 22236907330443060584173

theorem tailTrace_194878 : CollatzResearch.WordTrace tailWord_194878 prefixEnd_194878 22236907330443060584173 := by
  unfold tailWord_194878
  simp only [CollatzResearch.WordTrace]
  refine ⟨888473073499720419719161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4738523058665175571835525 888473073499720419719161)
  ·
    refine ⟨666354805124790314789371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 888473073499720419719161 666354805124790314789371)
    ·
      refine ⟨999532207687185472184057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666354805124790314789371 999532207687185472184057)
      ·
        refine ⟨749649155765389104138043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 999532207687185472184057 749649155765389104138043)
        ·
          refine ⟨1124473733648083656207065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749649155765389104138043 1124473733648083656207065)
          ·
            refine ⟨843355300236062742155299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124473733648083656207065 843355300236062742155299)
            ·
              refine ⟨1265032950354094113232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843355300236062742155299 1265032950354094113232949)
              ·
                refine ⟨118596839095696323115589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1265032950354094113232949 118596839095696323115589)
                ·
                  refine ⟨22236907330443060584173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118596839095696323115589 22236907330443060584173)
                  ·
                    rfl

theorem cell22_194878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_194878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194878 prefixEnd_194878 := by exact prefixLift 194878
  have htrace : WordTrace (prefixWord ++ tailWord_194878) baseStart_194878 baseEnd_194878 := by
    simpa [prefixWord, tailWord_194878, baseEnd_194878] using wordTrace_append hprefix tailTrace_194878
  have hstable : (prefixWord ++ tailWord_194878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194878).length < 2 ^ (prefixWord ++ tailWord_194878).sum := by decide
  have hdescent : baseEnd_194878 < baseStart_194878 := by decide
  rcases family_descends (prefixWord ++ tailWord_194878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194921 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_194921 : Nat := 118140960795 + 194921 * 2 ^ 59
def prefixEnd_194921 : Nat := 4983230072969 + 3 ^ 40 * 194921 * 2
def baseEnd_194921 : Nat := 66725441770091402927387

theorem tailTrace_194921 : CollatzResearch.WordTrace tailWord_194921 prefixEnd_194921 66725441770091402927387 := by
  unfold tailWord_194921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109352926841981701568617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4739568617894654467712411 7109352926841981701568617)
  ·
    refine ⟨5332014695131486276176463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7109352926841981701568617 5332014695131486276176463)
    ·
      refine ⟨7998022042697229414264695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5332014695131486276176463 7998022042697229414264695)
      ·
        refine ⟨11997033064045844121397043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7998022042697229414264695 11997033064045844121397043)
        ·
          refine ⟨17995549596068766182095565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997033064045844121397043 17995549596068766182095565)
          ·
            refine ⟨6748331098525787318285837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17995549596068766182095565 6748331098525787318285837)
            ·
              refine ⟨2530624161947170244357189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6748331098525787318285837 2530624161947170244357189)
              ·
                refine ⟨474492030365094420816973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2530624161947170244357189 474492030365094420816973)
                ·
                  refine ⟨177934511386910407806365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474492030365094420816973 177934511386910407806365)
                  ·
                    refine ⟨66725441770091402927387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177934511386910407806365 66725441770091402927387)
                    ·
                      rfl

theorem cell22_194921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_194921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194921 prefixEnd_194921 := by exact prefixLift 194921
  have htrace : WordTrace (prefixWord ++ tailWord_194921) baseStart_194921 baseEnd_194921 := by
    simpa [prefixWord, tailWord_194921, baseEnd_194921] using wordTrace_append hprefix tailTrace_194921
  have hstable : (prefixWord ++ tailWord_194921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194921).length < 2 ^ (prefixWord ++ tailWord_194921).sum := by decide
  have hdescent : baseEnd_194921 < baseStart_194921 := by decide
  rcases family_descends (prefixWord ++ tailWord_194921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194951 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 5]
def baseStart_194951 : Nat := 118140960795 + 194951 * 2 ^ 59
def prefixEnd_194951 : Nat := 4983230072969 + 3 ^ 40 * 194951 * 2
def baseEnd_194951 : Nat := 22245237127727108225765

theorem tailTrace_194951 : CollatzResearch.WordTrace tailWord_194951 prefixEnd_194951 22245237127727108225765 := by
  unfold tailWord_194951
  simp only [CollatzResearch.WordTrace]
  refine ⟨7110447116733296825160707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4740298077822197883440471 7110447116733296825160707)
  ·
    refine ⟨10665670675099945237741061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7110447116733296825160707 10665670675099945237741061)
    ·
      refine ⟨1999813251581239732076449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10665670675099945237741061 1999813251581239732076449)
      ·
        refine ⟨1499859938685929799057337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1999813251581239732076449 1499859938685929799057337)
        ·
          refine ⟨1124894954014447349293003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499859938685929799057337 1124894954014447349293003)
          ·
            refine ⟨1687342431021671023939505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124894954014447349293003 1687342431021671023939505)
            ·
              refine ⟨1265506823266253267954629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687342431021671023939505 1265506823266253267954629)
              ·
                refine ⟨237282529362422487741493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1265506823266253267954629 237282529362422487741493)
                ·
                  refine ⟨22245237127727108225765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237282529362422487741493 22245237127727108225765)
                  ·
                    rfl

theorem cell22_194951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 5].length) (baseStart_194951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194951 prefixEnd_194951 := by exact prefixLift 194951
  have htrace : WordTrace (prefixWord ++ tailWord_194951) baseStart_194951 baseEnd_194951 := by
    simpa [prefixWord, tailWord_194951, baseEnd_194951] using wordTrace_append hprefix tailTrace_194951
  have hstable : (prefixWord ++ tailWord_194951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194951).length < 2 ^ (prefixWord ++ tailWord_194951).sum := by decide
  have hdescent : baseEnd_194951 < baseStart_194951 := by decide
  rcases family_descends (prefixWord ++ tailWord_194951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194968 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_194968 : Nat := 118140960795 + 194968 * 2 ^ 59
def prefixEnd_194968 : Nat := 4983230072969 + 3 ^ 40 * 194968 * 2
def baseEnd_194968 : Nat := 22247176943532982334081

theorem tailTrace_194968 : CollatzResearch.WordTrace tailWord_194968 prefixEnd_194968 22247176943532982334081 := by
  unfold tailWord_194968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555533578835854364264779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4740711438447805819019705 3555533578835854364264779)
  ·
    refine ⟨5333300368253781546397169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3555533578835854364264779 5333300368253781546397169)
    ·
      refine ⟨3999975276190336159797877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5333300368253781546397169 3999975276190336159797877)
      ·
        refine ⟨374997682142844014981051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3999975276190336159797877 374997682142844014981051)
        ·
          refine ⟨562496523214266022471577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374997682142844014981051 562496523214266022471577)
          ·
            refine ⟨421872392410699516853683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562496523214266022471577 421872392410699516853683)
            ·
              refine ⟨632808588616049275280525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421872392410699516853683 632808588616049275280525)
              ·
                refine ⟨237303220731018478230197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632808588616049275280525 237303220731018478230197)
                ·
                  refine ⟨22247176943532982334081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237303220731018478230197 22247176943532982334081)
                  ·
                    rfl

theorem cell22_194968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_194968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194968 prefixEnd_194968 := by exact prefixLift 194968
  have htrace : WordTrace (prefixWord ++ tailWord_194968) baseStart_194968 baseEnd_194968 := by
    simpa [prefixWord, tailWord_194968, baseEnd_194968] using wordTrace_append hprefix tailTrace_194968
  have hstable : (prefixWord ++ tailWord_194968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194968).length < 2 ^ (prefixWord ++ tailWord_194968).sum := by decide
  have hdescent : baseEnd_194968 < baseStart_194968 := by decide
  rcases family_descends (prefixWord ++ tailWord_194968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194981 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_194981 : Nat := 118140960795 + 194981 * 2 ^ 59
def prefixEnd_194981 : Nat := 4983230072969 + 3 ^ 40 * 194981 * 2
def baseEnd_194981 : Nat := 66745980996271246427203

theorem tailTrace_194981 : CollatzResearch.WordTrace tailWord_194981 prefixEnd_194981 66745980996271246427203 := by
  unfold tailWord_194981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111541306624611948752797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4741027537749741299168531 7111541306624611948752797)
  ·
    refine ⟨2666827989984229480782299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7111541306624611948752797 2666827989984229480782299)
    ·
      refine ⟨4000241984976344221173449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2666827989984229480782299 4000241984976344221173449)
      ·
        refine ⟨3000181488732258165880087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000241984976344221173449 3000181488732258165880087)
        ·
          refine ⟨4500272233098387248820131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000181488732258165880087 4500272233098387248820131)
          ·
            refine ⟨6750408349647580873230197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500272233098387248820131 6750408349647580873230197)
            ·
              refine ⟨632850782779460706865331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6750408349647580873230197 632850782779460706865331)
              ·
                refine ⟨949276174169191060297997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632850782779460706865331 949276174169191060297997)
                ·
                  refine ⟨355978565313446647611749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949276174169191060297997 355978565313446647611749)
                  ·
                    refine ⟨66745980996271246427203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355978565313446647611749 66745980996271246427203)
                    ·
                      rfl

theorem cell22_194981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_194981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_194981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_194981 prefixEnd_194981 := by exact prefixLift 194981
  have htrace : WordTrace (prefixWord ++ tailWord_194981) baseStart_194981 baseEnd_194981 := by
    simpa [prefixWord, tailWord_194981, baseEnd_194981] using wordTrace_append hprefix tailTrace_194981
  have hstable : (prefixWord ++ tailWord_194981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194981).length < 2 ^ (prefixWord ++ tailWord_194981).sum := by decide
  have hdescent : baseEnd_194981 < baseStart_194981 := by decide
  rcases family_descends (prefixWord ++ tailWord_194981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195028 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_195028 : Nat := 118140960795 + 195028 * 2 ^ 59
def prefixEnd_195028 : Nat := 4983230072969 + 3 ^ 40 * 195028 * 2
def baseEnd_195028 : Nat := 66762070056778790502059

theorem tailTrace_195028 : CollatzResearch.WordTrace tailWord_195028 prefixEnd_195028 66762070056778790502059 := by
  unfold tailWord_195028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556627768727169487856869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4742170358302892650475825 3556627768727169487856869)
  ·
    refine ⟨666867706636344278973163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3556627768727169487856869 666867706636344278973163)
    ·
      refine ⟨1000301559954516418459745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666867706636344278973163 1000301559954516418459745)
      ·
        refine ⟨750226169965887313844809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1000301559954516418459745 750226169965887313844809)
        ·
          refine ⟨562669627474415485383607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750226169965887313844809 562669627474415485383607)
          ·
            refine ⟨844004441211623228075411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562669627474415485383607 844004441211623228075411)
            ·
              refine ⟨1266006661817434842113117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844004441211623228075411 1266006661817434842113117)
              ·
                refine ⟨474752498181538065792419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266006661817434842113117 474752498181538065792419)
                ·
                  refine ⟨712128747272307098688629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474752498181538065792419 712128747272307098688629)
                  ·
                    refine ⟨66762070056778790502059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 712128747272307098688629 66762070056778790502059)
                    ·
                      rfl

theorem cell22_195028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_195028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195028 prefixEnd_195028 := by exact prefixLift 195028
  have htrace : WordTrace (prefixWord ++ tailWord_195028) baseStart_195028 baseEnd_195028 := by
    simpa [prefixWord, tailWord_195028, baseEnd_195028] using wordTrace_append hprefix tailTrace_195028
  have hstable : (prefixWord ++ tailWord_195028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195028).length < 2 ^ (prefixWord ++ tailWord_195028).sum := by decide
  have hdescent : baseEnd_195028 < baseStart_195028 := by decide
  rcases family_descends (prefixWord ++ tailWord_195028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195043 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 6]
def baseStart_195043 : Nat := 118140960795 + 195043 * 2 ^ 59
def prefixEnd_195043 : Nat := 4983230072969 + 3 ^ 40 * 195043 * 2
def baseEnd_195043 : Nat := 66767204863323751377013

theorem tailTrace_195043 : CollatzResearch.WordTrace tailWord_195043 prefixEnd_195043 66767204863323751377013 := by
  unfold tailWord_195043
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113802632399996537509783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4742535088266664358339855 7113802632399996537509783)
  ·
    refine ⟨10670703948599994806264675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113802632399996537509783 10670703948599994806264675)
    ·
      refine ⟨16006055922899992209397013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10670703948599994806264675 16006055922899992209397013)
      ·
        refine ⟨750283871385937134815485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16006055922899992209397013 750283871385937134815485)
        ·
          refine ⟨281356451769726425555807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750283871385937134815485 281356451769726425555807)
          ·
            refine ⟨422034677654589638333711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281356451769726425555807 422034677654589638333711)
            ·
              refine ⟨633052016481884457500567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422034677654589638333711 633052016481884457500567)
              ·
                refine ⟨949578024722826686250851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633052016481884457500567 949578024722826686250851)
                ·
                  refine ⟨1424367037084240029376277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949578024722826686250851 1424367037084240029376277)
                  ·
                    refine ⟨66767204863323751377013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1424367037084240029376277 66767204863323751377013)
                    ·
                      rfl

theorem cell22_195043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_195043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195043 prefixEnd_195043 := by exact prefixLift 195043
  have htrace : WordTrace (prefixWord ++ tailWord_195043) baseStart_195043 baseEnd_195043 := by
    simpa [prefixWord, tailWord_195043, baseEnd_195043] using wordTrace_append hprefix tailTrace_195043
  have hstable : (prefixWord ++ tailWord_195043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195043).length < 2 ^ (prefixWord ++ tailWord_195043).sum := by decide
  have hdescent : baseEnd_195043 < baseStart_195043 := by decide
  rcases family_descends (prefixWord ++ tailWord_195043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195058 : List Nat := [3, 2, 1, 4, 2, 1, 9]
def baseStart_195058 : Nat := 118140960795 + 195058 * 2 ^ 59
def prefixEnd_195058 : Nat := 4983230072969 + 3 ^ 40 * 195058 * 2
def baseEnd_195058 : Nat := 2473049617402544898221

theorem tailTrace_195058 : CollatzResearch.WordTrace tailWord_195058 prefixEnd_195058 2473049617402544898221 := by
  unfold tailWord_195058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778587431836413524826457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4742899818230436066203885 1778587431836413524826457)
  ·
    refine ⟨1333940573877310143619843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1778587431836413524826457 1333940573877310143619843)
    ·
      refine ⟨2000910860815965215429765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333940573877310143619843 2000910860815965215429765)
      ·
        refine ⟨375170786402993477893081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2000910860815965215429765 375170786402993477893081)
        ·
          refine ⟨281378089802245108419811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375170786402993477893081 281378089802245108419811)
          ·
            refine ⟨422067134703367662629717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281378089802245108419811 422067134703367662629717)
            ·
              refine ⟨2473049617402544898221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 422067134703367662629717 2473049617402544898221)
              ·
                rfl

theorem cell22_195058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 9].length) (baseStart_195058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195058 prefixEnd_195058 := by exact prefixLift 195058
  have htrace : WordTrace (prefixWord ++ tailWord_195058) baseStart_195058 baseEnd_195058 := by
    simpa [prefixWord, tailWord_195058, baseEnd_195058] using wordTrace_append hprefix tailTrace_195058
  have hstable : (prefixWord ++ tailWord_195058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195058).length < 2 ^ (prefixWord ++ tailWord_195058).sum := by decide
  have hdescent : baseEnd_195058 < baseStart_195058 := by decide
  rcases family_descends (prefixWord ++ tailWord_195058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195092 : List Nat := [2, 4, 3, 1, 1, 3, 2, 6]
def baseStart_195092 : Nat := 118140960795 + 195092 * 2 ^ 59
def prefixEnd_195092 : Nat := 4983230072969 + 3 ^ 40 * 195092 * 2
def baseEnd_195092 : Nat := 7420442062744884100207

theorem tailTrace_195092 : CollatzResearch.WordTrace tailWord_195092 prefixEnd_195092 7420442062744884100207 := by
  unfold tailWord_195092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557794904611238953021765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4743726539481651937362353 3557794904611238953021765)
  ·
    refine ⟨667086544614607303691581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3557794904611238953021765 667086544614607303691581)
    ·
      refine ⟨250157454230477738884343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 667086544614607303691581 250157454230477738884343)
      ·
        refine ⟨375236181345716608326515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250157454230477738884343 375236181345716608326515)
        ·
          refine ⟨562854272018574912489773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375236181345716608326515 562854272018574912489773)
          ·
            refine ⟨211070352006965592183665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562854272018574912489773 211070352006965592183665)
            ·
              refine ⟨158302764005224194137749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211070352006965592183665 158302764005224194137749)
              ·
                refine ⟨7420442062744884100207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158302764005224194137749 7420442062744884100207)
                ·
                  rfl

theorem cell22_195092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_195092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195092 prefixEnd_195092 := by exact prefixLift 195092
  have htrace : WordTrace (prefixWord ++ tailWord_195092) baseStart_195092 baseEnd_195092 := by
    simpa [prefixWord, tailWord_195092, baseEnd_195092] using wordTrace_append hprefix tailTrace_195092
  have hstable : (prefixWord ++ tailWord_195092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195092).length < 2 ^ (prefixWord ++ tailWord_195092).sum := by decide
  have hdescent : baseEnd_195092 < baseStart_195092 := by decide
  rcases family_descends (prefixWord ++ tailWord_195092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195107 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 1, 3]
def baseStart_195107 : Nat := 118140960795 + 195107 * 2 ^ 59
def prefixEnd_195107 : Nat := 4983230072969 + 3 ^ 40 * 195107 * 2
def baseEnd_195107 : Nat := 66789113371248917776817

theorem tailTrace_195107 : CollatzResearch.WordTrace tailWord_195107 prefixEnd_195107 66789113371248917776817 := by
  unfold tailWord_195107
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116136904168135467839575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4744091269445423645226383 7116136904168135467839575)
  ·
    refine ⟨10674205356252203201759363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116136904168135467839575 10674205356252203201759363)
    ·
      refine ⟨16011308034378304802639045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10674205356252203201759363 16011308034378304802639045)
      ·
        refine ⟨3002120256445932150494821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16011308034378304802639045 3002120256445932150494821)
        ·
          refine ⟨562897548083612278217779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3002120256445932150494821 562897548083612278217779)
          ·
            refine ⟨844346322125418417326669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562897548083612278217779 844346322125418417326669)
            ·
              refine ⟨316629870797031906497501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844346322125418417326669 316629870797031906497501)
              ·
                refine ⟨118736201548886964936563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316629870797031906497501 118736201548886964936563)
                ·
                  refine ⟨178104302323330447404845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118736201548886964936563 178104302323330447404845)
                  ·
                    refine ⟨66789113371248917776817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178104302323330447404845 66789113371248917776817)
                    ·
                      rfl

theorem cell22_195107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 3].length) (baseStart_195107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195107 prefixEnd_195107 := by exact prefixLift 195107
  have htrace : WordTrace (prefixWord ++ tailWord_195107) baseStart_195107 baseEnd_195107 := by
    simpa [prefixWord, tailWord_195107, baseEnd_195107] using wordTrace_append hprefix tailTrace_195107
  have hstable : (prefixWord ++ tailWord_195107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195107).length < 2 ^ (prefixWord ++ tailWord_195107).sum := by decide
  have hdescent : baseEnd_195107 < baseStart_195107 := by decide
  rcases family_descends (prefixWord ++ tailWord_195107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195137 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 5]
def baseStart_195137 : Nat := 118140960795 + 195137 * 2 ^ 59
def prefixEnd_195137 : Nat := 4983230072969 + 3 ^ 40 * 195137 * 2
def baseEnd_195137 : Nat := 22266460994779613175575

theorem tailTrace_195137 : CollatzResearch.WordTrace tailWord_195137 prefixEnd_195137 22266460994779613175575 := by
  unfold tailWord_195137
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117231094059450591431665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4744820729372967060954443 7117231094059450591431665)
  ·
    refine ⟨5337923320544587943573749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7117231094059450591431665 5337923320544587943573749)
    ·
      refine ⟨500430311301055119710039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5337923320544587943573749 500430311301055119710039)
      ·
        refine ⟨750645466951582679565059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500430311301055119710039 750645466951582679565059)
        ·
          refine ⟨1125968200427374019347589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750645466951582679565059 1125968200427374019347589)
          ·
            refine ⟨211119037580132628627673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1125968200427374019347589 211119037580132628627673)
            ·
              refine ⟨158339278185099471470755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211119037580132628627673 158339278185099471470755)
              ·
                refine ⟨237508917277649207206133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158339278185099471470755 237508917277649207206133)
                ·
                  refine ⟨22266460994779613175575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237508917277649207206133 22266460994779613175575)
                  ·
                    rfl

theorem cell22_195137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_195137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195137 prefixEnd_195137 := by exact prefixLift 195137
  have htrace : WordTrace (prefixWord ++ tailWord_195137) baseStart_195137 baseEnd_195137 := by
    simpa [prefixWord, tailWord_195137, baseEnd_195137] using wordTrace_append hprefix tailTrace_195137
  have hstable : (prefixWord ++ tailWord_195137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195137).length < 2 ^ (prefixWord ++ tailWord_195137).sum := by decide
  have hdescent : baseEnd_195137 < baseStart_195137 := by decide
  rcases family_descends (prefixWord ++ tailWord_195137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195150 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_195150 : Nat := 118140960795 + 195150 * 2 ^ 59
def prefixEnd_195150 : Nat := 4983230072969 + 3 ^ 40 * 195150 * 2
def baseEnd_195150 : Nat := 66803833150011138951685

theorem tailTrace_195150 : CollatzResearch.WordTrace tailWord_195150 prefixEnd_195150 66803833150011138951685 := by
  unfold tailWord_195150
  simp only [CollatzResearch.WordTrace]
  refine ⟨889713155376544226456863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4745136828674902541103269 889713155376544226456863)
  ·
    refine ⟨1334569733064816339685295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889713155376544226456863 1334569733064816339685295)
    ·
      refine ⟨2001854599597224509527943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334569733064816339685295 2001854599597224509527943)
      ·
        refine ⟨3002781899395836764291915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001854599597224509527943 3002781899395836764291915)
        ·
          refine ⟨4504172849093755146437873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002781899395836764291915 4504172849093755146437873)
          ·
            refine ⟨3378129636820316359828405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4504172849093755146437873 3378129636820316359828405)
            ·
              refine ⟨316699653451904658733913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3378129636820316359828405 316699653451904658733913)
              ·
                refine ⟨237524740088928494050435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316699653451904658733913 237524740088928494050435)
                ·
                  refine ⟨356287110133392741075653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237524740088928494050435 356287110133392741075653)
                  ·
                    refine ⟨66803833150011138951685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 356287110133392741075653 66803833150011138951685)
                    ·
                      rfl

theorem cell22_195150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_195150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195150 prefixEnd_195150 := by exact prefixLift 195150
  have htrace : WordTrace (prefixWord ++ tailWord_195150) baseStart_195150 baseEnd_195150 := by
    simpa [prefixWord, tailWord_195150, baseEnd_195150] using wordTrace_append hprefix tailTrace_195150
  have hstable : (prefixWord ++ tailWord_195150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195150).length < 2 ^ (prefixWord ++ tailWord_195150).sum := by decide
  have hdescent : baseEnd_195150 < baseStart_195150 := by decide
  rcases family_descends (prefixWord ++ tailWord_195150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195180 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_195180 : Nat := 118140960795 + 195180 * 2 ^ 59
def prefixEnd_195180 : Nat := 4983230072969 + 3 ^ 40 * 195180 * 2
def baseEnd_195180 : Nat := 66814102763101060701593

theorem tailTrace_195180 : CollatzResearch.WordTrace tailWord_195180 prefixEnd_195180 66814102763101060701593 := by
  unfold tailWord_195180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559399716451834467623497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4745866288602445956831329 3559399716451834467623497)
  ·
    refine ⟨2669549787338875850717623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3559399716451834467623497 2669549787338875850717623)
    ·
      refine ⟨4004324681008313776076435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669549787338875850717623 4004324681008313776076435)
      ·
        refine ⟨6006487021512470664114653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004324681008313776076435 6006487021512470664114653)
        ·
          refine ⟨2252432633067176499042995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6006487021512470664114653 2252432633067176499042995)
          ·
            refine ⟨3378648949600764748564493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252432633067176499042995 3378648949600764748564493)
            ·
              refine ⟨1266993356100286780711685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378648949600764748564493 1266993356100286780711685)
              ·
                refine ⟨237561254268803771383441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1266993356100286780711685 237561254268803771383441)
                ·
                  refine ⟨178170940701602828537581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237561254268803771383441 178170940701602828537581)
                  ·
                    refine ⟨66814102763101060701593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178170940701602828537581 66814102763101060701593)
                    ·
                      rfl

theorem cell22_195180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_195180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195180 prefixEnd_195180 := by exact prefixLift 195180
  have htrace : WordTrace (prefixWord ++ tailWord_195180) baseStart_195180 baseEnd_195180 := by
    simpa [prefixWord, tailWord_195180, baseEnd_195180] using wordTrace_append hprefix tailTrace_195180
  have hstable : (prefixWord ++ tailWord_195180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195180).length < 2 ^ (prefixWord ++ tailWord_195180).sum := by decide
  have hdescent : baseEnd_195180 < baseStart_195180 := by decide
  rcases family_descends (prefixWord ++ tailWord_195180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195182 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_195182 : Nat := 118140960795 + 195182 * 2 ^ 59
def prefixEnd_195182 : Nat := 4983230072969 + 3 ^ 40 * 195182 * 2
def baseEnd_195182 : Nat := 22271595801324574050529

theorem tailTrace_195182 : CollatzResearch.WordTrace tailWord_195182 prefixEnd_195182 22271595801324574050529 := by
  unfold tailWord_195182
  simp only [CollatzResearch.WordTrace]
  refine ⟨889859047362052909602475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4745914919264282184546533 889859047362052909602475)
  ·
    refine ⟨1334788571043079364403713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889859047362052909602475 1334788571043079364403713)
    ·
      refine ⟨1001091428282309523302785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1334788571043079364403713 1001091428282309523302785)
      ·
        refine ⟨750818571211732142477089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001091428282309523302785 750818571211732142477089)
        ·
          refine ⟨563113928408799106857817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750818571211732142477089 563113928408799106857817)
          ·
            refine ⟨422335446306599330143363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563113928408799106857817 422335446306599330143363)
            ·
              refine ⟨633503169459898995215045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422335446306599330143363 633503169459898995215045)
              ·
                refine ⟨118781844273731061602821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633503169459898995215045 118781844273731061602821)
                ·
                  refine ⟨22271595801324574050529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118781844273731061602821 22271595801324574050529)
                  ·
                    rfl

theorem cell22_195182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_195182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195182 prefixEnd_195182 := by exact prefixLift 195182
  have htrace : WordTrace (prefixWord ++ tailWord_195182) baseStart_195182 baseEnd_195182 := by
    simpa [prefixWord, tailWord_195182, baseEnd_195182] using wordTrace_append hprefix tailTrace_195182
  have hstable : (prefixWord ++ tailWord_195182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195182).length < 2 ^ (prefixWord ++ tailWord_195182).sum := by decide
  have hdescent : baseEnd_195182 < baseStart_195182 := by decide
  rcases family_descends (prefixWord ++ tailWord_195182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195193 : List Nat := [1, 2, 1, 3, 3, 2, 3, 7]
def baseStart_195193 : Nat := 118140960795 + 195193 * 2 ^ 59
def prefixEnd_195193 : Nat := 4983230072969 + 3 ^ 40 * 195193 * 2
def baseEnd_195193 : Nat := 7424283658752595569617

theorem tailTrace_195193 : CollatzResearch.WordTrace tailWord_195193 prefixEnd_195193 7424283658752595569617 := by
  unfold tailWord_195193
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119273581856572155470233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4746182387904381436980155 7119273581856572155470233)
  ·
    refine ⟨5339455186392429116602675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7119273581856572155470233 5339455186392429116602675)
    ·
      refine ⟨8009182779588643674904013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5339455186392429116602675 8009182779588643674904013)
      ·
        refine ⟨3003443542345741378089005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8009182779588643674904013 3003443542345741378089005)
        ·
          refine ⟨1126291328379653016783377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3003443542345741378089005 1126291328379653016783377)
          ·
            refine ⟨844718496284739762587533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126291328379653016783377 844718496284739762587533)
            ·
              refine ⟨316769436106777410970325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844718496284739762587533 316769436106777410970325)
              ·
                refine ⟨7424283658752595569617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 316769436106777410970325 7424283658752595569617)
                ·
                  rfl

theorem cell22_195193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 7].length) (baseStart_195193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195193 prefixEnd_195193 := by exact prefixLift 195193
  have htrace : WordTrace (prefixWord ++ tailWord_195193) baseStart_195193 baseEnd_195193 := by
    simpa [prefixWord, tailWord_195193, baseEnd_195193] using wordTrace_append hprefix tailTrace_195193
  have hstable : (prefixWord ++ tailWord_195193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195193).length < 2 ^ (prefixWord ++ tailWord_195193).sum := by decide
  have hdescent : baseEnd_195193 < baseStart_195193 := by decide
  rcases family_descends (prefixWord ++ tailWord_195193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195276 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_195276 : Nat := 118140960795 + 195276 * 2 ^ 59
def prefixEnd_195276 : Nat := 4983230072969 + 3 ^ 40 * 195276 * 2
def baseEnd_195276 : Nat := 66846965524988810301299

theorem tailTrace_195276 : CollatzResearch.WordTrace tailWord_195276 prefixEnd_195276 66846965524988810301299 := by
  unfold tailWord_195276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561150420277938665370841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4748200560370584887161121 3561150420277938665370841)
  ·
    refine ⟨2670862815208453999028131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3561150420277938665370841 2670862815208453999028131)
    ·
      refine ⟨4006294222812680998542197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670862815208453999028131 4006294222812680998542197)
      ·
        refine ⟨375590083388688843613331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4006294222812680998542197 375590083388688843613331)
        ·
          refine ⟨563385125083033265419997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375590083388688843613331 563385125083033265419997)
          ·
            refine ⟨211269421906137474532499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563385125083033265419997 211269421906137474532499)
            ·
              refine ⟨316904132859206211798749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211269421906137474532499 316904132859206211798749)
              ·
                refine ⟨118839049822202329424531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316904132859206211798749 118839049822202329424531)
                ·
                  refine ⟨178258574733303494136797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118839049822202329424531 178258574733303494136797)
                  ·
                    refine ⟨66846965524988810301299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178258574733303494136797 66846965524988810301299)
                    ·
                      rfl

theorem cell22_195276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_195276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195276 prefixEnd_195276 := by exact prefixLift 195276
  have htrace : WordTrace (prefixWord ++ tailWord_195276) baseStart_195276 baseEnd_195276 := by
    simpa [prefixWord, tailWord_195276, baseEnd_195276] using wordTrace_append hprefix tailTrace_195276
  have hstable : (prefixWord ++ tailWord_195276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195276).length < 2 ^ (prefixWord ++ tailWord_195276).sum := by decide
  have hdescent : baseEnd_195276 < baseStart_195276 := by decide
  rcases family_descends (prefixWord ++ tailWord_195276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195300 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_195300 : Nat := 118140960795 + 195300 * 2 ^ 59
def prefixEnd_195300 : Nat := 4983230072969 + 3 ^ 40 * 195300 * 2
def baseEnd_195300 : Nat := 22285060405153582567075

theorem tailTrace_195300 : CollatzResearch.WordTrace tailWord_195300 prefixEnd_195300 22285060405153582567075 := by
  unfold tailWord_195300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561588096234464714807677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4748784128312619619743569 3561588096234464714807677)
  ·
    refine ⟨1335595536087924268052879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3561588096234464714807677 1335595536087924268052879)
    ·
      refine ⟨2003393304131886402079319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335595536087924268052879 2003393304131886402079319)
      ·
        refine ⟨3005089956197829603118979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003393304131886402079319 3005089956197829603118979)
        ·
          refine ⟨4507634934296744404678469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005089956197829603118979 4507634934296744404678469)
          ·
            refine ⟨845181550180639575877213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4507634934296744404678469 845181550180639575877213)
            ·
              refine ⟨316943081317739840953955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845181550180639575877213 316943081317739840953955)
              ·
                refine ⟨475414621976609761430933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316943081317739840953955 475414621976609761430933)
                ·
                  refine ⟨22285060405153582567075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 475414621976609761430933 22285060405153582567075)
                  ·
                    rfl

theorem cell22_195300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_195300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195300 prefixEnd_195300 := by exact prefixLift 195300
  have htrace : WordTrace (prefixWord ++ tailWord_195300) baseStart_195300 baseEnd_195300 := by
    simpa [prefixWord, tailWord_195300, baseEnd_195300] using wordTrace_append hprefix tailTrace_195300
  have hstable : (prefixWord ++ tailWord_195300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195300).length < 2 ^ (prefixWord ++ tailWord_195300).sum := by decide
  have hdescent : baseEnd_195300 < baseStart_195300 := by decide
  rcases family_descends (prefixWord ++ tailWord_195300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195351 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 4]
def baseStart_195351 : Nat := 118140960795 + 195351 * 2 ^ 59
def prefixEnd_195351 : Nat := 4983230072969 + 3 ^ 40 * 195351 * 2
def baseEnd_195351 : Nat := 22290879852571204892023

theorem tailTrace_195351 : CollatzResearch.WordTrace tailWord_195351 prefixEnd_195351 22290879852571204892023 := by
  unfold tailWord_195351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125036315284165139721907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4750024210189443426481271 7125036315284165139721907)
  ·
    refine ⟨10687554472926247709582861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7125036315284165139721907 10687554472926247709582861)
    ·
      refine ⟨4007832927347342891093573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10687554472926247709582861 4007832927347342891093573)
      ·
        refine ⟨751468673877626792080045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4007832927347342891093573 751468673877626792080045)
        ·
          refine ⟨281800752704110047030017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751468673877626792080045 281800752704110047030017)
          ·
            refine ⟨211350564528082535272513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281800752704110047030017 211350564528082535272513)
            ·
              refine ⟨158512923396061901454385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211350564528082535272513 158512923396061901454385)
              ·
                refine ⟨118884692547046426090789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158512923396061901454385 118884692547046426090789)
                ·
                  refine ⟨22290879852571204892023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118884692547046426090789 22290879852571204892023)
                  ·
                    rfl

theorem cell22_195351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 4].length) (baseStart_195351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195351 prefixEnd_195351 := by exact prefixLift 195351
  have htrace : WordTrace (prefixWord ++ tailWord_195351) baseStart_195351 baseEnd_195351 := by
    simpa [prefixWord, tailWord_195351, baseEnd_195351] using wordTrace_append hprefix tailTrace_195351
  have hstable : (prefixWord ++ tailWord_195351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195351).length < 2 ^ (prefixWord ++ tailWord_195351).sum := by decide
  have hdescent : baseEnd_195351 < baseStart_195351 := by decide
  rcases family_descends (prefixWord ++ tailWord_195351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195362 : List Nat := [3, 3, 1, 1, 2, 4, 1, 7]
def baseStart_195362 : Nat := 118140960795 + 195362 * 2 ^ 59
def prefixEnd_195362 : Nat := 4983230072969 + 3 ^ 40 * 195362 * 2
def baseEnd_195362 : Nat := 7430711675834805850115

theorem tailTrace_195362 : CollatzResearch.WordTrace tailWord_195362 prefixEnd_195362 7430711675834805850115 := by
  unfold tailWord_195362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781359379561078504593085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4750291678829542678914893 1781359379561078504593085)
  ·
    refine ⟨668009767335404439222407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1781359379561078504593085 668009767335404439222407)
    ·
      refine ⟨1002014651003106658833611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668009767335404439222407 1002014651003106658833611)
      ·
        refine ⟨1503021976504659988250417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002014651003106658833611 1503021976504659988250417)
        ·
          refine ⟨1127266482378494991187813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503021976504659988250417 1127266482378494991187813)
          ·
            refine ⟨211362465445967810847715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1127266482378494991187813 211362465445967810847715)
            ·
              refine ⟨317043698168951716271573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211362465445967810847715 317043698168951716271573)
              ·
                refine ⟨7430711675834805850115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 317043698168951716271573 7430711675834805850115)
                ·
                  rfl

theorem cell22_195362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_195362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195362 prefixEnd_195362 := by exact prefixLift 195362
  have htrace : WordTrace (prefixWord ++ tailWord_195362) baseStart_195362 baseEnd_195362 := by
    simpa [prefixWord, tailWord_195362, baseEnd_195362] using wordTrace_append hprefix tailTrace_195362
  have hstable : (prefixWord ++ tailWord_195362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195362).length < 2 ^ (prefixWord ++ tailWord_195362).sum := by decide
  have hdescent : baseEnd_195362 < baseStart_195362 := by decide
  rcases family_descends (prefixWord ++ tailWord_195362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195377 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_195377 : Nat := 118140960795 + 195377 * 2 ^ 59
def prefixEnd_195377 : Nat := 4983230072969 + 3 ^ 40 * 195377 * 2
def baseEnd_195377 : Nat := 66881539889058213525989

theorem tailTrace_195377 : CollatzResearch.WordTrace tailWord_195377 prefixEnd_195377 66881539889058213525989 := by
  unfold tailWord_195377
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125984613189971580168385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4750656408793314386778923 7125984613189971580168385)
  ·
    refine ⟨5344488459892478685126289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7125984613189971580168385 5344488459892478685126289)
    ·
      refine ⟨4008366344919359013844717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5344488459892478685126289 4008366344919359013844717)
      ·
        refine ⟨1503137379344759630191769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4008366344919359013844717 1503137379344759630191769)
        ·
          refine ⟨1127353034508569722643827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503137379344759630191769 1127353034508569722643827)
          ·
            refine ⟨1691029551762854583965741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127353034508569722643827 1691029551762854583965741)
            ·
              refine ⟨634136081911070468987153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1691029551762854583965741 634136081911070468987153)
              ·
                refine ⟨475602061433302851740365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634136081911070468987153 475602061433302851740365)
                ·
                  refine ⟨178350773037488569402637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475602061433302851740365 178350773037488569402637)
                  ·
                    refine ⟨66881539889058213525989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178350773037488569402637 66881539889058213525989)
                    ·
                      rfl

theorem cell22_195377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_195377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195377 prefixEnd_195377 := by exact prefixLift 195377
  have htrace : WordTrace (prefixWord ++ tailWord_195377) baseStart_195377 baseEnd_195377 := by
    simpa [prefixWord, tailWord_195377, baseEnd_195377] using wordTrace_append hprefix tailTrace_195377
  have hstable : (prefixWord ++ tailWord_195377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195377).length < 2 ^ (prefixWord ++ tailWord_195377).sum := by decide
  have hdescent : baseEnd_195377 < baseStart_195377 := by decide
  rcases family_descends (prefixWord ++ tailWord_195377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195435 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 6]
def baseStart_195435 : Nat := 118140960795 + 195435 * 2 ^ 59
def prefixEnd_195435 : Nat := 4983230072969 + 3 ^ 40 * 195435 * 2
def baseEnd_195435 : Nat := 22300464824788465191937

theorem tailTrace_195435 : CollatzResearch.WordTrace tailWord_195435 prefixEnd_195435 22300464824788465191937 := by
  unfold tailWord_195435
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128100046979847485779759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4752066697986564990519839 7128100046979847485779759)
  ·
    refine ⟨10692150070469771228669639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7128100046979847485779759 10692150070469771228669639)
    ·
      refine ⟨16038225105704656843004459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10692150070469771228669639 16038225105704656843004459)
      ·
        refine ⟨24057337658556985264506689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16038225105704656843004459 24057337658556985264506689)
        ·
          refine ⟨18043003243917738948380017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24057337658556985264506689 18043003243917738948380017)
          ·
            refine ⟨13532252432938304211285013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18043003243917738948380017 13532252432938304211285013)
            ·
              refine ⟨634324332793983009903985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13532252432938304211285013 634324332793983009903985)
              ·
                refine ⟨475743249595487257427989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634324332793983009903985 475743249595487257427989)
                ·
                  refine ⟨22300464824788465191937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 475743249595487257427989 22300464824788465191937)
                  ·
                    rfl

theorem cell22_195435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_195435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195435 prefixEnd_195435 := by exact prefixLift 195435
  have htrace : WordTrace (prefixWord ++ tailWord_195435) baseStart_195435 baseEnd_195435 := by
    simpa [prefixWord, tailWord_195435, baseEnd_195435] using wordTrace_append hprefix tailTrace_195435
  have hstable : (prefixWord ++ tailWord_195435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195435).length < 2 ^ (prefixWord ++ tailWord_195435).sum := by decide
  have hdescent : baseEnd_195435 < baseStart_195435 := by decide
  rcases family_descends (prefixWord ++ tailWord_195435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195450 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_195450 : Nat := 118140960795 + 195450 * 2 ^ 59
def prefixEnd_195450 : Nat := 4983230072969 + 3 ^ 40 * 195450 * 2
def baseEnd_195450 : Nat := 66906529280910356450765

theorem tailTrace_195450 : CollatzResearch.WordTrace tailWord_195450 prefixEnd_195450 66906529280910356450765 := by
  unfold tailWord_195450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782161785481376261893951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4752431427950336698383869 1782161785481376261893951)
  ·
    refine ⟨2673242678222064392840927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782161785481376261893951 2673242678222064392840927)
    ·
      refine ⟨4009864017333096589261391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673242678222064392840927 4009864017333096589261391)
      ·
        refine ⟨6014796025999644883892087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009864017333096589261391 6014796025999644883892087)
        ·
          refine ⟨9022194038999467325838131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014796025999644883892087 9022194038999467325838131)
          ·
            refine ⟨13533291058499200988757197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022194038999467325838131 13533291058499200988757197)
            ·
              refine ⟨5074984146937200370783949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13533291058499200988757197 5074984146937200370783949)
              ·
                refine ⟨1903119055101450139043981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5074984146937200370783949 1903119055101450139043981)
                ·
                  refine ⟨713669645663043802141493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1903119055101450139043981 713669645663043802141493)
                  ·
                    refine ⟨66906529280910356450765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 713669645663043802141493 66906529280910356450765)
                    ·
                      rfl

theorem cell22_195450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_195450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195450 prefixEnd_195450 := by exact prefixLift 195450
  have htrace : WordTrace (prefixWord ++ tailWord_195450) baseStart_195450 baseEnd_195450 := by
    simpa [prefixWord, tailWord_195450, baseEnd_195450] using wordTrace_append hprefix tailTrace_195450
  have hstable : (prefixWord ++ tailWord_195450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195450).length < 2 ^ (prefixWord ++ tailWord_195450).sum := by decide
  have hdescent : baseEnd_195450 < baseStart_195450 := by decide
  rcases family_descends (prefixWord ++ tailWord_195450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195467 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 4, 3]
def baseStart_195467 : Nat := 118140960795 + 195467 * 2 ^ 59
def prefixEnd_195467 : Nat := 4983230072969 + 3 ^ 40 * 195467 * 2
def baseEnd_195467 : Nat := 66912348728327978775713

theorem tailTrace_195467 : CollatzResearch.WordTrace tailWord_195467 prefixEnd_195467 66912348728327978775713 := by
  unfold tailWord_195467
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129267182863916950944655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4752844788575944633963103 7129267182863916950944655)
  ·
    refine ⟨10693900774295875426416983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7129267182863916950944655 10693900774295875426416983)
    ·
      refine ⟨16040851161443813139625475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10693900774295875426416983 16040851161443813139625475)
      ·
        refine ⟨24061276742165719709438213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16040851161443813139625475 24061276742165719709438213)
        ·
          refine ⟨4511489389156072445519665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24061276742165719709438213 4511489389156072445519665)
          ·
            refine ⟨3383617041867054334139749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4511489389156072445519665 3383617041867054334139749)
            ·
              refine ⟨634428195350072687651203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3383617041867054334139749 634428195350072687651203)
              ·
                refine ⟨951642293025109031476805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634428195350072687651203 951642293025109031476805)
                ·
                  refine ⟨178432929942207943401901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951642293025109031476805 178432929942207943401901)
                  ·
                    refine ⟨66912348728327978775713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178432929942207943401901 66912348728327978775713)
                    ·
                      rfl

theorem cell22_195467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3].length) (baseStart_195467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195467 prefixEnd_195467 := by exact prefixLift 195467
  have htrace : WordTrace (prefixWord ++ tailWord_195467) baseStart_195467 baseEnd_195467 := by
    simpa [prefixWord, tailWord_195467, baseEnd_195467] using wordTrace_append hprefix tailTrace_195467
  have hstable : (prefixWord ++ tailWord_195467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195467).length < 2 ^ (prefixWord ++ tailWord_195467).sum := by decide
  have hdescent : baseEnd_195467 < baseStart_195467 := by decide
  rcases family_descends (prefixWord ++ tailWord_195467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195501 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_195501 : Nat := 118140960795 + 195501 * 2 ^ 59
def prefixEnd_195501 : Nat := 4983230072969 + 3 ^ 40 * 195501 * 2
def baseEnd_195501 : Nat := 66923987623163223425609

theorem tailTrace_195501 : CollatzResearch.WordTrace tailWord_195501 prefixEnd_195501 66923987623163223425609 := by
  unfold tailWord_195501
  simp only [CollatzResearch.WordTrace]
  refine ⟨7130507264740740757682357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4753671509827160505121571 7130507264740740757682357)
  ·
    refine ⟨668485056069444446032721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7130507264740740757682357 668485056069444446032721)
    ·
      refine ⟨501363792052083334524541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 668485056069444446032721 501363792052083334524541)
      ·
        refine ⟨188011422019531250446703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501363792052083334524541 188011422019531250446703)
        ·
          refine ⟨282017133029296875670055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188011422019531250446703 282017133029296875670055)
          ·
            refine ⟨423025699543945313505083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282017133029296875670055 423025699543945313505083)
            ·
              refine ⟨634538549315917970257625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423025699543945313505083 634538549315917970257625)
              ·
                refine ⟨475903911986938477693219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634538549315917970257625 475903911986938477693219)
                ·
                  refine ⟨713855867980407716539829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475903911986938477693219 713855867980407716539829)
                  ·
                    refine ⟨66923987623163223425609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 713855867980407716539829 66923987623163223425609)
                    ·
                      rfl

theorem cell22_195501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_195501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195501 prefixEnd_195501 := by exact prefixLift 195501
  have htrace : WordTrace (prefixWord ++ tailWord_195501) baseStart_195501 baseEnd_195501 := by
    simpa [prefixWord, tailWord_195501, baseEnd_195501] using wordTrace_append hprefix tailTrace_195501
  have hstable : (prefixWord ++ tailWord_195501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195501).length < 2 ^ (prefixWord ++ tailWord_195501).sum := by decide
  have hdescent : baseEnd_195501 < baseStart_195501 := by decide
  rcases family_descends (prefixWord ++ tailWord_195501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195525 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 11]
def baseStart_195525 : Nat := 118140960795 + 195525 * 2 ^ 59
def prefixEnd_195525 : Nat := 4983230072969 + 3 ^ 40 * 195525 * 2
def baseEnd_195525 : Nat := 22310734437878386941845

theorem tailTrace_195525 : CollatzResearch.WordTrace tailWord_195525 prefixEnd_195525 22310734437878386941845 := by
  unfold tailWord_195525
  simp only [CollatzResearch.WordTrace]
  refine ⟨7131382616653792856556029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4754255077769195237704019 7131382616653792856556029)
  ·
    refine ⟨2674268481245172321208511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7131382616653792856556029 2674268481245172321208511)
    ·
      refine ⟨4011402721867758481812767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674268481245172321208511 4011402721867758481812767)
      ·
        refine ⟨6017104082801637722719151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011402721867758481812767 6017104082801637722719151)
        ·
          refine ⟨9025656124202456584078727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017104082801637722719151 9025656124202456584078727)
          ·
            refine ⟨13538484186303684876118091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025656124202456584078727 13538484186303684876118091)
            ·
              refine ⟨20307726279455527314177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13538484186303684876118091 20307726279455527314177137)
              ·
                refine ⟨15230794709591645485632853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20307726279455527314177137 15230794709591645485632853)
                ·
                  refine ⟨22310734437878386941845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 15230794709591645485632853 22310734437878386941845)
                  ·
                    rfl

theorem cell22_195525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_195525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195525 prefixEnd_195525 := by exact prefixLift 195525
  have htrace : WordTrace (prefixWord ++ tailWord_195525) baseStart_195525 baseEnd_195525 := by
    simpa [prefixWord, tailWord_195525, baseEnd_195525] using wordTrace_append hprefix tailTrace_195525
  have hstable : (prefixWord ++ tailWord_195525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195525).length < 2 ^ (prefixWord ++ tailWord_195525).sum := by decide
  have hdescent : baseEnd_195525 < baseStart_195525 := by decide
  rcases family_descends (prefixWord ++ tailWord_195525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195574 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_195574 : Nat := 118140960795 + 195574 * 2 ^ 59
def prefixEnd_195574 : Nat := 4983230072969 + 3 ^ 40 * 195574 * 2
def baseEnd_195574 : Nat := 66948977015015366350385

theorem tailTrace_195574 : CollatzResearch.WordTrace tailWord_195574 prefixEnd_195574 66948977015015366350385 := by
  unfold tailWord_195574
  simp only [CollatzResearch.WordTrace]
  refine ⟨445823112092267139068111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4755446528984182816726517 445823112092267139068111)
  ·
    refine ⟨668734668138400708602167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445823112092267139068111 668734668138400708602167)
    ·
      refine ⟨1003102002207601062903251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668734668138400708602167 1003102002207601062903251)
      ·
        refine ⟨1504653003311401594354877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003102002207601062903251 1504653003311401594354877)
        ·
          refine ⟨564244876241775597883079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1504653003311401594354877 564244876241775597883079)
          ·
            refine ⟨846367314362663396824619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564244876241775597883079 846367314362663396824619)
            ·
              refine ⟨1269550971543995095236929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846367314362663396824619 1269550971543995095236929)
              ·
                refine ⟨952163228657996321427697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269550971543995095236929 952163228657996321427697)
                ·
                  refine ⟨714122421493497241070773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 952163228657996321427697 714122421493497241070773)
                  ·
                    refine ⟨66948977015015366350385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 714122421493497241070773 66948977015015366350385)
                    ·
                      rfl

theorem cell22_195574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_195574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195574 prefixEnd_195574 := by exact prefixLift 195574
  have htrace : WordTrace (prefixWord ++ tailWord_195574) baseStart_195574 baseEnd_195574 := by
    simpa [prefixWord, tailWord_195574, baseEnd_195574] using wordTrace_append hprefix tailTrace_195574
  have hstable : (prefixWord ++ tailWord_195574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195574).length < 2 ^ (prefixWord ++ tailWord_195574).sum := by decide
  have hdescent : baseEnd_195574 < baseStart_195574 := by decide
  rcases family_descends (prefixWord ++ tailWord_195574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195619 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 4, 3]
def baseStart_195619 : Nat := 118140960795 + 195619 * 2 ^ 59
def prefixEnd_195619 : Nat := 4983230072969 + 3 ^ 40 * 195619 * 2
def baseEnd_195619 : Nat := 66964381434650248975247

theorem tailTrace_195619 : CollatzResearch.WordTrace tailWord_195619 prefixEnd_195619 66964381434650248975247 := by
  unfold tailWord_195619
  simp only [CollatzResearch.WordTrace]
  refine ⟨7134811078313246910477911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4756540718875497940318607 7134811078313246910477911)
  ·
    refine ⟨10702216617469870365716867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7134811078313246910477911 10702216617469870365716867)
    ·
      refine ⟨16053324926204805548575301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702216617469870365716867 16053324926204805548575301)
      ·
        refine ⟨3009998423663401040357869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16053324926204805548575301 3009998423663401040357869)
        ·
          refine ⟨1128749408873775390134201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3009998423663401040357869 1128749408873775390134201)
          ·
            refine ⟨846562056655331542600651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128749408873775390134201 846562056655331542600651)
            ·
              refine ⟨1269843084982997313900977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846562056655331542600651 1269843084982997313900977)
              ·
                refine ⟨952382313737247985425733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269843084982997313900977 952382313737247985425733)
                ·
                  refine ⟨178571683825733997267325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952382313737247985425733 178571683825733997267325)
                  ·
                    refine ⟨66964381434650248975247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178571683825733997267325 66964381434650248975247)
                    ·
                      rfl

theorem cell22_195619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3].length) (baseStart_195619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195619 prefixEnd_195619 := by exact prefixLift 195619
  have htrace : WordTrace (prefixWord ++ tailWord_195619) baseStart_195619 baseEnd_195619 := by
    simpa [prefixWord, tailWord_195619, baseEnd_195619] using wordTrace_append hprefix tailTrace_195619
  have hstable : (prefixWord ++ tailWord_195619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195619).length < 2 ^ (prefixWord ++ tailWord_195619).sum := by decide
  have hdescent : baseEnd_195619 < baseStart_195619 := by decide
  rcases family_descends (prefixWord ++ tailWord_195619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195634 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_195634 : Nat := 118140960795 + 195634 * 2 ^ 59
def prefixEnd_195634 : Nat := 4983230072969 + 3 ^ 40 * 195634 * 2
def baseEnd_195634 : Nat := 66969516241195209850201

theorem tailTrace_195634 : CollatzResearch.WordTrace tailWord_195634 prefixEnd_195634 66969516241195209850201 := by
  unfold tailWord_195634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783839543314726118068489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4756905448839269648182637 1783839543314726118068489)
  ·
    refine ⟨1337879657486044588551367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1783839543314726118068489 1337879657486044588551367)
    ·
      refine ⟨2006819486229066882827051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337879657486044588551367 2006819486229066882827051)
      ·
        refine ⟨3010229229343600324240577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006819486229066882827051 3010229229343600324240577)
        ·
          refine ⟨2257671922007700243180433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010229229343600324240577 2257671922007700243180433)
          ·
            refine ⟨1693253941505775182385325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2257671922007700243180433 1693253941505775182385325)
            ·
              refine ⟨634970228064665693394497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693253941505775182385325 634970228064665693394497)
              ·
                refine ⟨476227671048499270045873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634970228064665693394497 476227671048499270045873)
                ·
                  refine ⟨357170753286374452534405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476227671048499270045873 357170753286374452534405)
                  ·
                    refine ⟨66969516241195209850201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357170753286374452534405 66969516241195209850201)
                    ·
                      rfl

theorem cell22_195634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_195634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195634 prefixEnd_195634 := by exact prefixLift 195634
  have htrace : WordTrace (prefixWord ++ tailWord_195634) baseStart_195634 baseEnd_195634 := by
    simpa [prefixWord, tailWord_195634, baseEnd_195634] using wordTrace_append hprefix tailTrace_195634
  have hstable : (prefixWord ++ tailWord_195634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195634).length < 2 ^ (prefixWord ++ tailWord_195634).sum := by decide
  have hdescent : baseEnd_195634 < baseStart_195634 := by decide
  rcases family_descends (prefixWord ++ tailWord_195634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195664 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_195664 : Nat := 118140960795 + 195664 * 2 ^ 59
def prefixEnd_195664 : Nat := 4983230072969 + 3 ^ 40 * 195664 * 2
def baseEnd_195664 : Nat := 66979785854285131600109

theorem tailTrace_195664 : CollatzResearch.WordTrace tailWord_195664 prefixEnd_195664 66979785854285131600109 := by
  unfold tailWord_195664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568226181575109797933023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4757634908766813063910697 3568226181575109797933023)
  ·
    refine ⟨5352339272362664696899535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3568226181575109797933023 5352339272362664696899535)
    ·
      refine ⟨8028508908543997045349303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5352339272362664696899535 8028508908543997045349303)
      ·
        refine ⟨12042763362815995568023955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8028508908543997045349303 12042763362815995568023955)
        ·
          refine ⟨18064145044223993352035933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12042763362815995568023955 18064145044223993352035933)
          ·
            refine ⟨6774054391583997507013475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18064145044223993352035933 6774054391583997507013475)
            ·
              refine ⟨10161081587375996260520213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774054391583997507013475 10161081587375996260520213)
              ·
                refine ⟨476300699408249824711885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10161081587375996260520213 476300699408249824711885)
                ·
                  refine ⟨178612762278093684266957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476300699408249824711885 178612762278093684266957)
                  ·
                    refine ⟨66979785854285131600109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178612762278093684266957 66979785854285131600109)
                    ·
                      rfl

theorem cell22_195664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_195664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195664 prefixEnd_195664 := by exact prefixLift 195664
  have htrace : WordTrace (prefixWord ++ tailWord_195664) baseStart_195664 baseEnd_195664 := by
    simpa [prefixWord, tailWord_195664, baseEnd_195664] using wordTrace_append hprefix tailTrace_195664
  have hstable : (prefixWord ++ tailWord_195664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195664).length < 2 ^ (prefixWord ++ tailWord_195664).sum := by decide
  have hdescent : baseEnd_195664 < baseStart_195664 := by decide
  rcases family_descends (prefixWord ++ tailWord_195664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195698 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_195698 : Nat := 118140960795 + 195698 * 2 ^ 59
def prefixEnd_195698 : Nat := 4983230072969 + 3 ^ 40 * 195698 * 2
def baseEnd_195698 : Nat := 66991424749120376250005

theorem tailTrace_195698 : CollatzResearch.WordTrace tailWord_195698 prefixEnd_195698 66991424749120376250005 := by
  unfold tailWord_195698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784423111256760850650937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4758461630018028935069165 1784423111256760850650937)
  ·
    refine ⟨1338317333442570637988203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1784423111256760850650937 1338317333442570637988203)
    ·
      refine ⟨2007476000163855956982305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338317333442570637988203 2007476000163855956982305)
      ·
        refine ⟨1505607000122891967736729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2007476000163855956982305 1505607000122891967736729)
        ·
          refine ⟨1129205250092168975802547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505607000122891967736729 1129205250092168975802547)
          ·
            refine ⟨1693807875138253463703821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129205250092168975802547 1693807875138253463703821)
            ·
              refine ⟨635177953176845048888933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693807875138253463703821 635177953176845048888933)
              ·
                refine ⟨119095866220658446666675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635177953176845048888933 119095866220658446666675)
                ·
                  refine ⟨178643799330987670000013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119095866220658446666675 178643799330987670000013)
                  ·
                    refine ⟨66991424749120376250005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178643799330987670000013 66991424749120376250005)
                    ·
                      rfl

theorem cell22_195698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_195698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195698 prefixEnd_195698 := by exact prefixLift 195698
  have htrace : WordTrace (prefixWord ++ tailWord_195698) baseStart_195698 baseEnd_195698 := by
    simpa [prefixWord, tailWord_195698, baseEnd_195698] using wordTrace_append hprefix tailTrace_195698
  have hstable : (prefixWord ++ tailWord_195698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195698).length < 2 ^ (prefixWord ++ tailWord_195698).sum := by decide
  have hdescent : baseEnd_195698 < baseStart_195698 := by decide
  rcases family_descends (prefixWord ++ tailWord_195698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195709 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_195709 : Nat := 118140960795 + 195709 * 2 ^ 59
def prefixEnd_195709 : Nat := 4983230072969 + 3 ^ 40 * 195709 * 2
def baseEnd_195709 : Nat := 66995190273920014224971

theorem tailTrace_195709 : CollatzResearch.WordTrace tailWord_195709 prefixEnd_195709 66995190273920014224971 := by
  unfold tailWord_195709
  simp only [CollatzResearch.WordTrace]
  refine ⟨7138093647987192281254181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4758729098658128187502787 7138093647987192281254181)
  ·
    refine ⟨1338392558997598552735159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7138093647987192281254181 1338392558997598552735159)
    ·
      refine ⟨2007588838496397829102739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338392558997598552735159 2007588838496397829102739)
      ·
        refine ⟨3011383257744596743654109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007588838496397829102739 3011383257744596743654109)
        ·
          refine ⟨1129268721654223778870291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3011383257744596743654109 1129268721654223778870291)
          ·
            refine ⟨1693903082481335668305437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129268721654223778870291 1693903082481335668305437)
            ·
              refine ⟨635213655930500875614539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693903082481335668305437 635213655930500875614539)
              ·
                refine ⟨952820483895751313421809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635213655930500875614539 952820483895751313421809)
                ·
                  refine ⟨714615362921813485066357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 952820483895751313421809 714615362921813485066357)
                  ·
                    refine ⟨66995190273920014224971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 714615362921813485066357 66995190273920014224971)
                    ·
                      rfl

theorem cell22_195709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_195709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195709 prefixEnd_195709 := by exact prefixLift 195709
  have htrace : WordTrace (prefixWord ++ tailWord_195709) baseStart_195709 baseEnd_195709 := by
    simpa [prefixWord, tailWord_195709, baseEnd_195709] using wordTrace_append hprefix tailTrace_195709
  have hstable : (prefixWord ++ tailWord_195709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195709).length < 2 ^ (prefixWord ++ tailWord_195709).sum := by decide
  have hdescent : baseEnd_195709 < baseStart_195709 := by decide
  rcases family_descends (prefixWord ++ tailWord_195709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195741 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_195741 : Nat := 118140960795 + 195741 * 2 ^ 59
def prefixEnd_195741 : Nat := 4983230072969 + 3 ^ 40 * 195741 * 2
def baseEnd_195741 : Nat := 67006144527882597424873

theorem tailTrace_195741 : CollatzResearch.WordTrace tailWord_195741 prefixEnd_195741 67006144527882597424873 := by
  unfold tailWord_195741
  simp only [CollatzResearch.WordTrace]
  refine ⟨7139260783871261746419077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4759507189247507830946051 7139260783871261746419077)
  ·
    refine ⟨1338611396975861577453577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7139260783871261746419077 1338611396975861577453577)
    ·
      refine ⟨1003958547731896183090183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338611396975861577453577 1003958547731896183090183)
      ·
        refine ⟨1505937821597844274635275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003958547731896183090183 1505937821597844274635275)
        ·
          refine ⟨2258906732396766411952913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505937821597844274635275 2258906732396766411952913)
          ·
            refine ⟨1694180049297574808964685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2258906732396766411952913 1694180049297574808964685)
            ·
              refine ⟨635317518486590553361757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1694180049297574808964685 635317518486590553361757)
              ·
                refine ⟨238244069432471457510659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635317518486590553361757 238244069432471457510659)
                ·
                  refine ⟨357366104148707186265989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238244069432471457510659 357366104148707186265989)
                  ·
                    refine ⟨67006144527882597424873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357366104148707186265989 67006144527882597424873)
                    ·
                      rfl

theorem cell22_195741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_195741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195741 prefixEnd_195741 := by exact prefixLift 195741
  have htrace : WordTrace (prefixWord ++ tailWord_195741) baseStart_195741 baseEnd_195741 := by
    simpa [prefixWord, tailWord_195741, baseEnd_195741] using wordTrace_append hprefix tailTrace_195741
  have hstable : (prefixWord ++ tailWord_195741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195741).length < 2 ^ (prefixWord ++ tailWord_195741).sum := by decide
  have hdescent : baseEnd_195741 < baseStart_195741 := by decide
  rcases family_descends (prefixWord ++ tailWord_195741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195769 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_195769 : Nat := 118140960795 + 195769 * 2 ^ 59
def prefixEnd_195769 : Nat := 4983230072969 + 3 ^ 40 * 195769 * 2
def baseEnd_195769 : Nat := 67015729500099857724787

theorem tailTrace_195769 : CollatzResearch.WordTrace tailWord_195769 prefixEnd_195769 67015729500099857724787 := by
  unfold tailWord_195769
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140282027769822528438361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4760188018513215018958907 7140282027769822528438361)
  ·
    refine ⟨5355211520827366896328771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7140282027769822528438361 5355211520827366896328771)
    ·
      refine ⟨8032817281241050344493157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5355211520827366896328771 8032817281241050344493157)
      ·
        refine ⟨1506153240232696939592467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8032817281241050344493157 1506153240232696939592467)
        ·
          refine ⟨2259229860349045409388701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506153240232696939592467 2259229860349045409388701)
          ·
            refine ⟨847211197630892028520763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2259229860349045409388701 847211197630892028520763)
            ·
              refine ⟨1270816796446338042781145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847211197630892028520763 1270816796446338042781145)
              ·
                refine ⟨953112597334753532085859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270816796446338042781145 953112597334753532085859)
                ·
                  refine ⟨1429668896002130298128789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 953112597334753532085859 1429668896002130298128789)
                  ·
                    refine ⟨67015729500099857724787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1429668896002130298128789 67015729500099857724787)
                    ·
                      rfl

theorem cell22_195769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_195769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195769 prefixEnd_195769 := by exact prefixLift 195769
  have htrace : WordTrace (prefixWord ++ tailWord_195769) baseStart_195769 baseEnd_195769 := by
    simpa [prefixWord, tailWord_195769, baseEnd_195769] using wordTrace_append hprefix tailTrace_195769
  have hstable : (prefixWord ++ tailWord_195769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195769).length < 2 ^ (prefixWord ++ tailWord_195769).sum := by decide
  have hdescent : baseEnd_195769 < baseStart_195769 := by decide
  rcases family_descends (prefixWord ++ tailWord_195769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195790 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_195790 : Nat := 118140960795 + 195790 * 2 ^ 59
def prefixEnd_195790 : Nat := 4983230072969 + 3 ^ 40 * 195790 * 2
def baseEnd_195790 : Nat := 22340972743087600983241

theorem tailTrace_195790 : CollatzResearch.WordTrace tailWord_195790 prefixEnd_195790 22340972743087600983241 := by
  unfold tailWord_195790
  simp only [CollatzResearch.WordTrace]
  refine ⟨892630995086717889369103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4760698640462495409968549 892630995086717889369103)
  ·
    refine ⟨1338946492630076834053655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 892630995086717889369103 1338946492630076834053655)
    ·
      refine ⟨2008419738945115251080483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338946492630076834053655 2008419738945115251080483)
      ·
        refine ⟨3012629608417672876620725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008419738945115251080483 3012629608417672876620725)
        ·
          refine ⟨282434025789156832183193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3012629608417672876620725 282434025789156832183193)
          ·
            refine ⟨211825519341867624137395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282434025789156832183193 211825519341867624137395)
            ·
              refine ⟨317738279012801436206093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211825519341867624137395 317738279012801436206093)
              ·
                refine ⟨119151854629800538577285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317738279012801436206093 119151854629800538577285)
                ·
                  refine ⟨22340972743087600983241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119151854629800538577285 22340972743087600983241)
                  ·
                    rfl

theorem cell22_195790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_195790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195790 prefixEnd_195790 := by exact prefixLift 195790
  have htrace : WordTrace (prefixWord ++ tailWord_195790) baseStart_195790 baseEnd_195790 := by
    simpa [prefixWord, tailWord_195790, baseEnd_195790] using wordTrace_append hprefix tailTrace_195790
  have hstable : (prefixWord ++ tailWord_195790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195790).length < 2 ^ (prefixWord ++ tailWord_195790).sum := by decide
  have hdescent : baseEnd_195790 < baseStart_195790 := by decide
  rcases family_descends (prefixWord ++ tailWord_195790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195876 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_195876 : Nat := 118140960795 + 195876 * 2 ^ 59
def prefixEnd_195876 : Nat := 4983230072969 + 3 ^ 40 * 195876 * 2
def baseEnd_195876 : Nat := 67052357786787245299459

theorem tailTrace_195876 : CollatzResearch.WordTrace tailWord_195876 prefixEnd_195876 67052357786787245299459 := by
  unfold tailWord_195876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572092319191089901291741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4762789758921453201722321 3572092319191089901291741)
  ·
    refine ⟨1339534619696658712984403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3572092319191089901291741 1339534619696658712984403)
    ·
      refine ⟨2009301929544988069476605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1339534619696658712984403 2009301929544988069476605)
      ·
        refine ⟨753488223579370526053727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2009301929544988069476605 753488223579370526053727)
        ·
          refine ⟨1130232335369055789080591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753488223579370526053727 1130232335369055789080591)
          ·
            refine ⟨1695348503053583683620887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130232335369055789080591 1695348503053583683620887)
            ·
              refine ⟨2543022754580375525431331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695348503053583683620887 2543022754580375525431331)
              ·
                refine ⟨3814534131870563288146997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543022754580375525431331 3814534131870563288146997)
                ·
                  refine ⟨357612574862865308263781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814534131870563288146997 357612574862865308263781)
                  ·
                    refine ⟨67052357786787245299459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357612574862865308263781 67052357786787245299459)
                    ·
                      rfl

theorem cell22_195876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_195876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195876 prefixEnd_195876 := by exact prefixLift 195876
  have htrace : WordTrace (prefixWord ++ tailWord_195876) baseStart_195876 baseEnd_195876 := by
    simpa [prefixWord, tailWord_195876, baseEnd_195876] using wordTrace_append hprefix tailTrace_195876
  have hstable : (prefixWord ++ tailWord_195876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195876).length < 2 ^ (prefixWord ++ tailWord_195876).sum := by decide
  have hdescent : baseEnd_195876 < baseStart_195876 := by decide
  rcases family_descends (prefixWord ++ tailWord_195876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195891 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 6]
def baseStart_195891 : Nat := 118140960795 + 195891 * 2 ^ 59
def prefixEnd_195891 : Nat := 4983230072969 + 3 ^ 40 * 195891 * 2
def baseEnd_195891 : Nat := 22352497531110735391471

theorem tailTrace_195891 : CollatzResearch.WordTrace tailWord_195891 prefixEnd_195891 22352497531110735391471 := by
  unfold tailWord_195891
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144731733327837364379527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4763154488885224909586351 7144731733327837364379527)
  ·
    refine ⟨10717097599991756046569291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7144731733327837364379527 10717097599991756046569291)
    ·
      refine ⟨16075646399987634069853937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10717097599991756046569291 16075646399987634069853937)
      ·
        refine ⟨12056734799990725552390453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16075646399987634069853937 12056734799990725552390453)
        ·
          refine ⟨1130318887499130520536605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12056734799990725552390453 1130318887499130520536605)
          ·
            refine ⟨423869582812173945201227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1130318887499130520536605 423869582812173945201227)
            ·
              refine ⟨635804374218260917801841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423869582812173945201227 635804374218260917801841)
              ·
                refine ⟨476853280663695688351381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635804374218260917801841 476853280663695688351381)
                ·
                  refine ⟨22352497531110735391471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 476853280663695688351381 22352497531110735391471)
                  ·
                    rfl

theorem cell22_195891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_195891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195891 prefixEnd_195891 := by exact prefixLift 195891
  have htrace : WordTrace (prefixWord ++ tailWord_195891) baseStart_195891 baseEnd_195891 := by
    simpa [prefixWord, tailWord_195891, baseEnd_195891] using wordTrace_append hprefix tailTrace_195891
  have hstable : (prefixWord ++ tailWord_195891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195891).length < 2 ^ (prefixWord ++ tailWord_195891).sum := by decide
  have hdescent : baseEnd_195891 < baseStart_195891 := by decide
  rcases family_descends (prefixWord ++ tailWord_195891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195921 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_195921 : Nat := 118140960795 + 195921 * 2 ^ 59
def prefixEnd_195921 : Nat := 4983230072969 + 3 ^ 40 * 195921 * 2
def baseEnd_195921 : Nat := 67067762206422127924321

theorem tailTrace_195921 : CollatzResearch.WordTrace tailWord_195921 prefixEnd_195921 67067762206422127924321 := by
  unfold tailWord_195921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145825923219152487971617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4763883948812768325314411 7145825923219152487971617)
  ·
    refine ⟨5359369442414364365978713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7145825923219152487971617 5359369442414364365978713)
    ·
      refine ⟨4019527081810773274484035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5359369442414364365978713 4019527081810773274484035)
      ·
        refine ⟨6029290622716159911726053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019527081810773274484035 6029290622716159911726053)
        ·
          refine ⟨1130491991759279983448635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6029290622716159911726053 1130491991759279983448635)
          ·
            refine ⟨1695737987638919975172953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130491991759279983448635 1695737987638919975172953)
            ·
              refine ⟨1271803490729189981379715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695737987638919975172953 1271803490729189981379715)
              ·
                refine ⟨1907705236093784972069573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271803490729189981379715 1907705236093784972069573)
                ·
                  refine ⟨357694731767584682263045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907705236093784972069573 357694731767584682263045)
                  ·
                    refine ⟨67067762206422127924321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357694731767584682263045 67067762206422127924321)
                    ·
                      rfl

theorem cell22_195921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_195921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195921 prefixEnd_195921 := by exact prefixLift 195921
  have htrace : WordTrace (prefixWord ++ tailWord_195921) baseStart_195921 baseEnd_195921 := by
    simpa [prefixWord, tailWord_195921, baseEnd_195921] using wordTrace_append hprefix tailTrace_195921
  have hstable : (prefixWord ++ tailWord_195921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195921).length < 2 ^ (prefixWord ++ tailWord_195921).sum := by decide
  have hdescent : baseEnd_195921 < baseStart_195921 := by decide
  rcases family_descends (prefixWord ++ tailWord_195921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
